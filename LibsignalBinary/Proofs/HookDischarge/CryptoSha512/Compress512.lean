/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.SignalPqxdh.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.StepsLift
import ProofLib.SepLogic.HeapIntro

/-!
# Stacked consumer contract bridges for `sha2::sha512::compress512`

Bridges the `compress512` machine-code proof to consumer contracts (`256 ≤ hookStack`):

1. `compress512StackedMasterSpec hookStack` (RW, preserving `ProcessFieldsPreserved s0 sf ∧
   AllocCallPreserved s0 sf`, hence `Heap.VmPreserved` and `Arm64.Rust.VmPreserved`) and
   permission-polymorphic `compress512StackedMasterROSpec hookStack`.
2. `CliExt.compress512Spec Q` (`Q.F512 = sha512CompressState`, `extHookStack = 16,384` B), plus
   `keepsFs` and `SpecBudget.withVmPreserved` variants.
3. `E2E.Pqxdh.Shared.compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128`
   (`P0.Q.F512 = sha512CompressState`, `pqxdhHookStack = 4,096` B), plus `keepsFs` and
   `SpecBudget.withVmPreserved` variants.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512

open Arm64 ProofLib
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E
  (Sha512State PqxdhPrims PEParams UnreachedPqxdhPrimitives
   chunks128 sha512StateBytesLE sha512StateBytesBE sha512StateOf readSha512State
   beWord ofU8 toU8 modelPrims)
open CryptoVerification.E2E.Pqxdh.Shared
  (CryptoCompressGhost bytesToBv8 fitBv8 fitBytes_of_length_eq fitBv8_eq_bytesToBv8
   revWords64 sha512CompressOutBytes pqxdhHookStack compressInPlaceStubSpecPlaced)
open SignalPqxdh (Bytes chunkBlocks fitBytes sha512Step)
open LibsignalBinary.Heap (AllocCallPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (withRoData withRoDataSep SpecSimulates keepsFs_withRoData)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes sha512K_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512Sym sha2K64Sym compress512Lib)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop (compress512RawROSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.StepsLift
  (ProcessFieldsPreserved_toHeapVmPreserved stackAt_le_two_pow_64 stackAt_split_frame256
   withPlacedCodeLoaded compress512MasterROSpec compress512_master_ro_ok
   compress512_master_ro_subroutineOk)

/-! ## 1. Master Stacked Intermediate Specs & `.rodata` `K64` Transport -/

theorem sha512KBytes_length : sha512KBytes.length = 640 := by
  simp [sha512KBytes, List.length_flatMap, unpack64_length, List.map_const', sha512K_length]

theorem sha512KBytes_length_le : sha512KBytes.length ≤ 2 ^ 64 := by
  rw [sha512KBytes_length]; omega

/-- Read-only (`↦ᵣ`) or read-write (`↦ₛ`) input block slice at `blkA`. -/
@[expose] def compress512Blocks (ro : Bool) (blkA : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  cond ro (blkA ↦ᵣ bs) (blkA ↦ₛ bs)

/-- Frame-preserving normal-return simulation (`R₁ = R`) for non-panicking, non-exiting, non-OOM
specs, commuting with `withRoDataSep` and lowering to `SpecSimulates`. -/
def FrameSimulates {α β : Type} (spec₁ : Spec α) (spec₂ : Spec β) : Prop :=
  ∀ (y : β) (R : SepProp) (s0 : State),
    (s0.mem ⊨ spec₂.pre y s0 ∗ R) →
    ∃ x : α,
      (s0.mem ⊨ spec₁.pre x s0 ∗ R) ∧
      ∀ sf, Returned s0 sf → CallingConventionPreserved s0 sf →
        (sf.mem ⊨ spec₁.post x s0 sf ∗ R) →
        (sf.mem ⊨ spec₂.post y s0 sf ∗ R)

theorem FrameSimulates.toSpecSimulates {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (h : FrameSimulates spec₁ spec₂)
    (hpan : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates spec₁ spec₂ :=
  SpecSimulates.of_map
    (fun y R s0 hpre => let ⟨x, hpre₁, hpost⟩ := h y R s0 hpre; ⟨x, R, hpre₁, hpost⟩)
    hpan hex hoom

theorem FrameSimulates.trans {α β γ : Type} {s₁ : Spec α} {s₂ : Spec β} {s₃ : Spec γ}
    (h₁₂ : FrameSimulates s₁ s₂) (h₂₃ : FrameSimulates s₂ s₃) :
    FrameSimulates s₁ s₃ := by
  intro z R s0 hpre₃
  obtain ⟨y, hpre₂, hm₂⟩ := h₂₃ z R s0 hpre₃
  obtain ⟨x, hpre₁, hm₁⟩ := h₁₂ y R s0 hpre₂
  exact ⟨x, hpre₁, fun sf hret hcc hp => hm₂ sf hret hcc (hm₁ sf hret hcc hp)⟩

theorem FrameSimulates.drop_keepsFs {α : Type} {spec : Spec α} :
    FrameSimulates (keepsFs spec) spec := by
  intro x R s0 hpre
  refine ⟨x, hpre, fun sf _ _ hp => ?_⟩
  dsimp only [keepsFs] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

theorem FrameSimulates.withRoDataSep {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (addr : BitVec 64) (bytes : List (BitVec 8))
    (h : FrameSimulates spec₁ spec₂) :
    FrameSimulates (withRoDataSep addr bytes spec₁) (withRoDataSep addr bytes spec₂) := by
  intro y R s0 hpre
  dsimp only [RustStd.Common.withRoDataSep] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm (addr ↦ᵣ bytes) (spec₂.pre y s0)] at hpre
  obtain ⟨x, hpre₁, hm⟩ := h y ((addr ↦ᵣ bytes) ∗ R) s0 hpre
  refine ⟨x, ?_, fun sf hret hcc hp => ?_⟩
  · rw [sepConj_assoc, sepConj_left_comm (addr ↦ᵣ bytes) (spec₁.pre x s0)]
    exact hpre₁
  · rw [sepConj_assoc, sepConj_left_comm (addr ↦ᵣ bytes) (spec₁.post x s0 sf)] at hp
    have hq := hm sf hret hcc hp
    rw [sepConj_assoc, sepConj_left_comm (addr ↦ᵣ bytes) (spec₂.post y s0 sf)]
    exact hq

/-- Permission-polymorphic (`ro : Bool`) stack-parameterized (`hookStack`-byte) master
`compress512` contract without `.rodata` `K64`, preserving full `ProcessFieldsPreserved s0 sf`
and `AllocCallPreserved s0 sf`. -/
@[expose] def compress512StackedMasterROSpec (hookStack : Nat := extHookStack) :
    Spec (Bool × BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (ro, stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 128 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (stA ↦ₛ sha512StateBytesLE st) ∗ compress512Blocks ro blkA bs ∗ stackAt s0.sp hookStack
  post := fun (ro, stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (stA ↦ₛ sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)) ∗
      compress512Blocks ro blkA bs ∗ stackAt s0.sp hookStack

/-- Stack-parameterized (`hookStack`-byte) RW master `compress512` contract without `.rodata`
`K64`, preserving full `ProcessFieldsPreserved s0 sf` and `AllocCallPreserved s0 sf`. -/
@[expose] def compress512StackedMasterSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 128 * n⌝ ∗
      (stA ↦ₛ sha512StateBytesLE st) ∗ (blkA ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (stA ↦ₛ sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)) ∗
      (blkA ↦ₛ bs) ∗ stackAt s0.sp hookStack

/-- Generic `keepsFs` strengthening for any consumer simulated by `compress512StackedMasterSpec`. -/
theorem FrameSimulates.keepsFs_of_stackedMaster {β : Type} {hookStack : Nat}
    {S : Spec β} (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S) :
    FrameSimulates (compress512StackedMasterSpec hookStack) (keepsFs S) := by
  intro y R s0 hpre
  obtain ⟨x, hpre₁, hm⟩ := hS y R s0 hpre
  refine ⟨x, hpre₁, fun sf hret hcc hpost => ?_⟩
  have hpost_copy := hpost
  dsimp only [compress512StackedMasterSpec] at hpost_copy
  simp only [sepConj_assoc] at hpost_copy
  rw [satisfies_pure_sepConj] at hpost_copy
  have hfs : sf.fs = s0.fs := hpost_copy.1.1.1
  have hS_post := hm sf hret hcc hpost
  dsimp only [keepsFs]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfs, hS_post⟩

/-- Generic `SpecBudget.withVmPreserved` strengthening for any consumer simulated by
`compress512StackedMasterSpec`. -/
theorem FrameSimulates.withVmPreserved_of_stackedMaster {β : Type} {hookStack : Nat}
    {S : Spec β} (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S) :
    FrameSimulates (compress512StackedMasterSpec hookStack) (withVmPreserved S) := by
  intro y R s0 hpre
  obtain ⟨x, hpre₁, hm⟩ := hS y R s0 hpre
  refine ⟨x, hpre₁, fun sf hret hcc hpost => ?_⟩
  have hpost_copy := hpost
  dsimp only [compress512StackedMasterSpec] at hpost_copy
  simp only [sepConj_assoc] at hpost_copy
  rw [satisfies_pure_sepConj] at hpost_copy
  have hvm := ProcessFieldsPreserved_toHeapVmPreserved hpost_copy.1.1
  have hS_post := hm sf hret hcc hpost
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hS_post⟩

private def compress512StackedMasterTrueSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 128 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (stA ↦ₛ sha512StateBytesLE st) ∗ (blkA ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (stA ↦ₛ sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)) ∗
      (blkA ↦ᵣ bs) ∗ stackAt s0.sp hookStack

private theorem compress512MasterRO_simulates_stackedMasterTrue_roSep (k64 : BitVec 64)
    {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide) :
    SpecSimulates (compress512MasterROSpec k64)
      (withRoDataSep k64 sha512KBytes (compress512StackedMasterTrueSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  dsimp only [withRoDataSep, compress512StackedMasterTrueSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hpre⟩ := hpre
  have hmax : hookStack ≤ 2 ^ 64 := by
    have hstk := Satisfies.of_sep_right hpre
    rw [sepConj_left_comm (blkA ↦ᵣ bs) (stackAt s0.sp hookStack)] at hstk
    exact stackAt_le_two_pow_64 hstk
  rw [stackAt_split_frame256 s0 hstack hmax] at hpre
  simp only [sepConj_assoc] at hpre
  refine ⟨(stA, st, blkA, bs, n), stackAt (s0.sp - 256#64) (hookStack - 256) ∗ R, ?_, ?_⟩
  · dsimp only [compress512MasterROSpec, compress512RawROSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hpure, hpre⟩
  · intro sf hret _hcc hpost
    dsimp only [compress512MasterROSpec, compress512RawROSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    have hsf_sp : stackFrame sf 256 = stackFrame s0 256 := by
      simp only [stackFrame, hret.2.1]
    rw [hsf_sp] at hpost
    dsimp only [withRoDataSep, compress512StackedMasterTrueSpec]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝,
        satisfies_pure_sepConj]
    refine ⟨hpf, ?_⟩
    rw [stackAt_split_frame256 s0 hstack hmax]
    simpa only [sepConj_assoc] using hpost

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Heap.Disjoint Heap.union Heap.Matches regionHeap regionHeapRO in
private theorem stackedMasterTrue_roSep_simulates_stackedMasterRO_roSep
    (k64 : BitVec 64) (hookStack : Nat := extHookStack) :
    SpecSimulates
      (withRoDataSep k64 sha512KBytes (compress512StackedMasterTrueSpec hookStack))
      (withRoDataSep k64 sha512KBytes (compress512StackedMasterROSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hpre
  cases ro
  · dsimp only [withRoDataSep, compress512StackedMasterROSpec, compress512Blocks,
      Bool.cond_false] at hpre
    simp only [sepConj_assoc] at hpre
    rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpre
    obtain ⟨hpure, hmem0⟩ := hpre
    have hbs_max : bs.length ≤ 2 ^ 64 := hpure.2.2.2.2
    have hk_max : sha512KBytes.length ≤ 2 ^ 64 := sha512KBytes_length_le
    have hmem : s0.mem ⊨ (blkA ↦ₛ bs) ∗
        (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st) ∗ stackAt s0.sp hookStack)) ∗ R) := by
      simp only [sepConj_assoc] at hmem0 ⊢
      rw [sepConj_left_comm (stA ↦ₛ sha512StateBytesLE st) (blkA ↦ₛ bs),
          sepConj_left_comm (k64 ↦ᵣ sha512KBytes) (blkA ↦ₛ bs)] at hmem0
      exact hmem0
    obtain ⟨h_blk, h_QR, hd0, hb0, hQR0, hm0⟩ := Satisfies.sepConj_elim hmem
    obtain ⟨h_Q0, h_R, hdQR0, rfl, hQ0, hR0⟩ := SepProp.holds_sepConj_elim hQR0
    obtain ⟨h_k0, h_ststk0, hdk0, rfl, hk0, _⟩ := SepProp.holds_sepConj_elim hQ0
    obtain ⟨m_b0, _, rfl⟩ := ((IsBlock.pointsToBytes blkA bs).iff h_blk).mp hb0
    obtain ⟨m_k0, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO k64 sha512KBytes hk_max).iff h_k0).mp hk0
    have hm_blk0 : (regionHeap blkA bs.length m_b0).Matches s0.mem := Heap.Matches.of_union_left hm0
    have hrw0_perm : ∀ a, InRegion blkA bs.length a → s0.mem.perm a = some Perm.rw := by
      intro a ha
      have hv : (regionHeap blkA bs.length m_b0).phys a = some (.rw (m_b0.read8 a)) := by
        simp [regionHeap, ha]
      exact (hm_blk0.1 a (.rw (m_b0.read8 a)) hv).2.1
    have hnk64 : ∀ a, InRegion blkA bs.length a → ¬ InRegion k64 sha512KBytes.length a := by
      intro a ha hka
      have hv : (regionHeap blkA bs.length m_b0).phys a = some (.rw (m_b0.read8 a)) := by
        simp [regionHeap, ha]
      have hkv : (regionHeapRO k64 sha512KBytes.length m_k0).phys a = some (.ro (m_k0.read8 a)) := by
        simp [regionHeapRO, hka]
      rcases hd0.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; cases h1
      · simp [Heap.union, hkv] at h2
      · rw [hv] at h1; cases h1
    let R₁ : SepProp := ⟨fun h => R h ∧ ∀ a, InRegion blkA bs.length a → h.phys a = none⟩
    have hR₁ : R₁ h_R := by
      refine ⟨hR0, fun a ha => ?_⟩
      have hv : (regionHeap blkA bs.length m_b0).phys a = some (.rw (m_b0.read8 a)) := by
        simp [regionHeap, ha]
      rcases hd0.1 a with h1 | h2 | ⟨_, h1, _⟩
      · rw [hv] at h1; cases h1
      · simp only [Heap.union] at h2
        cases h1a : (regionHeapRO k64 sha512KBytes.length m_k0).phys a with
        | some _ => simp [h1a] at h2
        | none =>
          cases h1b : h_ststk0.phys a with
          | some _ => simp [h1a, h1b] at h2
          | none => simpa [h1a, h1b] using h2
      · rw [hv] at h1; cases h1
    have hmem_R₁ : s0.mem ⊨ (blkA ↦ₛ bs) ∗
        (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st) ∗ stackAt s0.sp hookStack)) ∗ R₁) :=
      Satisfies.sepConj_intro hd0 hb0 (SepProp.holds_sepConj_intro hdQR0 hQ0 hR₁) hm0
    have hmem_ro : s0.mem ⊨ (blkA ↦ᵣ bs) ∗
        (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st) ∗ stackAt s0.sp hookStack)) ∗ R₁) :=
      Satisfies.pointsToBytes_to_ro hmem_R₁
    refine ⟨(stA, st, blkA, bs, n), R₁, ?_, ?_⟩
    · dsimp only [withRoDataSep, compress512StackedMasterTrueSpec]
      simp only [sepConj_assoc]
      rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜_⌝, satisfies_pure_sepConj]
      refine ⟨hpure, ?_⟩
      simp only [sepConj_assoc] at hmem_ro ⊢
      rw [sepConj_left_comm (blkA ↦ᵣ bs) (k64 ↦ᵣ sha512KBytes),
          sepConj_left_comm (blkA ↦ᵣ bs) (stA ↦ₛ sha512StateBytesLE st)] at hmem_ro
      exact hmem_ro
    · intro sf _hret _hcc hpost
      dsimp only [withRoDataSep, compress512StackedMasterTrueSpec] at hpost
      simp only [sepConj_assoc] at hpost
      rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨hpf, hacp⟩, hpost_m0⟩ := hpost
      let st' := (chunks128 bs).foldl sha512CompressState st
      have hpost_m' : sf.mem ⊨ (blkA ↦ᵣ bs) ∗
          (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st') ∗ stackAt s0.sp hookStack)) ∗ R₁) := by
        simp only [sepConj_assoc] at hpost_m0 ⊢
        rw [sepConj_left_comm (stA ↦ₛ sha512StateBytesLE st') (blkA ↦ᵣ bs),
            sepConj_left_comm (k64 ↦ᵣ sha512KBytes) (blkA ↦ᵣ bs)] at hpost_m0
        exact hpost_m0
      have hbs_sf : sf.mem.readBytes blkA bs.length = bs :=
        (IsBlockRO.pointsToBytesRO blkA bs hbs_max).read hpost_m'
      obtain ⟨h_ro, h_QfR, hdp, hro_p, hQfR_p, hmp⟩ := Satisfies.sepConj_elim hpost_m'
      have hm_ro : h_ro.Matches sf.mem := Heap.Matches.of_union_left hmp
      have hm_QfR : h_QfR.Matches sf.mem := Heap.Matches.of_union_right hdp hmp
      obtain ⟨m_ro, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO blkA bs hbs_max).iff h_ro).mp hro_p
      have hrw_sf : sf.mem.RW blkA bs.length := by
        intro a ha
        have hcell : (regionHeapRO blkA bs.length m_ro).phys a = some (.ro (m_ro.read8 a)) := by
          simp [regionHeapRO, ha]
        have hlf : sf.mem.isLazyFree a = false := (hm_ro.1 a _ hcell).2.2
        have hperm : sf.mem.perm a = some Perm.rw := (hpf.2.2.2.2.2.2.2 a).trans (hrw0_perm a ha)
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨h_Qf, h_Rf, hdQfR, rfl, hQf_p, ⟨hRf_p, hRf_none⟩⟩ := SepProp.holds_sepConj_elim hQfR_p
      obtain ⟨h_kf, h_ststkf, hdkf, rfl, hkf_p, hststkf_p⟩ := SepProp.holds_sepConj_elim hQf_p
      obtain ⟨h_st, h_stk, hdst, rfl, hst_p, hstk_p⟩ := SepProp.holds_sepConj_elim hststkf_p
      obtain ⟨m_kf, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO k64 sha512KBytes hk_max).iff h_kf).mp hkf_p
      obtain ⟨m_st, _, rfl⟩ := ((IsBlock.pointsToBytes stA (sha512StateBytesLE st')).iff h_st).mp hst_p
      obtain ⟨m_stk, _, rfl⟩ := ((IsBlock.memRegion (s0.sp - BitVec.ofNat 64 hookStack) hookStack).iff h_stk).mp hstk_p
      have h_rest_none : ∀ a, InRegion blkA bs.length a →
          (((regionHeapRO k64 sha512KBytes.length m_kf).union
            ((regionHeap stA (sha512StateBytesLE st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf).phys a = none := by
        intro a ha
        have hro_a : (regionHeapRO blkA bs.length m_ro).phys a = some (.ro (m_ro.read8 a)) := by
          simp [regionHeapRO, ha]
        have hk_none : (regionHeapRO k64 sha512KBytes.length m_kf).phys a = none := by
          simp [regionHeapRO, hnk64 a ha]
        have hst_none : (regionHeap stA (sha512StateBytesLE st').length m_st).phys a = none := by
          by_cases hin : InRegion stA (sha512StateBytesLE st').length a
          · have h1 : (regionHeap stA (sha512StateBytesLE st').length m_st).phys a = some (.rw (m_st.read8 a)) := by
              simp [regionHeap, hin]
            rcases hdp.1 a with h | h | ⟨_, h, h'⟩
            · rw [hro_a] at h; cases h
            · simp [Heap.union, hk_none, h1] at h
            · simp [Heap.union, hk_none, h1] at h'
          · simp [regionHeap, hin]
        have hstk_none : (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk).phys a = none := by
          by_cases hin : InRegion (s0.sp - BitVec.ofNat 64 hookStack) hookStack a
          · have h1 : (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk).phys a =
                some (.rw (m_stk.read8 a)) := by simp [regionHeap, hin]
            rcases hdp.1 a with h | h | ⟨_, h, h'⟩
            · rw [hro_a] at h; cases h
            · simp [Heap.union, hk_none, hst_none, h1] at h
            · simp [Heap.union, hk_none, hst_none, h1] at h'
          · simp [regionHeap, hin]
        simp [Heap.union, hk_none, hst_none, hstk_none, hRf_none a ha]
      let h_rw := regionHeap blkA bs.length sf.mem
      have hd_rw : h_rw.Disjoint
          (((regionHeapRO k64 sha512KBytes.length m_kf).union
            ((regionHeap stA (sha512StateBytesLE st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf) := by
        refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
        by_cases ha : InRegion blkA bs.length a
        · exact Or.inr (Or.inl (h_rest_none a ha))
        · exact Or.inl (by simp [h_rw, regionHeap, ha])
      have hb_rw : (blkA ↦ₛ bs) h_rw :=
        ((IsBlock.pointsToBytes blkA bs).iff h_rw).mpr ⟨sf.mem, ⟨hbs_max, hbs_sf⟩, rfl⟩
      have hm_rw : h_rw.Matches sf.mem := IsBlock.regionHeap_matches blkA bs.length sf.mem hrw_sf
      have hQfR_orig :
          (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st') ∗ stackAt s0.sp hookStack)) ∗ R)
          (((regionHeapRO k64 sha512KBytes.length m_kf).union
            ((regionHeap stA (sha512StateBytesLE st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf) :=
        SepProp.holds_sepConj_intro hdQfR
          (SepProp.holds_sepConj_intro hdkf hkf_p (SepProp.holds_sepConj_intro hdst hst_p hstk_p))
          hRf_p
      have hfin : sf.mem ⊨ (blkA ↦ₛ bs) ∗
          (((k64 ↦ᵣ sha512KBytes) ∗ ((stA ↦ₛ sha512StateBytesLE st') ∗ stackAt s0.sp hookStack)) ∗ R) :=
        Satisfies.sepConj_intro hd_rw hb_rw hQfR_orig (Heap.Matches.union hm_rw hm_QfR)
      dsimp only [withRoDataSep, compress512StackedMasterROSpec, compress512Blocks, Bool.cond_false]
      simp only [sepConj_assoc]
      rw [sepConj_left_comm (k64 ↦ᵣ sha512KBytes) ⌜_⌝, satisfies_pure_sepConj]
      refine ⟨⟨hpf, hacp⟩, ?_⟩
      simp only [sepConj_assoc] at hfin ⊢
      rw [sepConj_left_comm (blkA ↦ₛ bs) (k64 ↦ᵣ sha512KBytes),
          sepConj_left_comm (blkA ↦ₛ bs) (stA ↦ₛ sha512StateBytesLE st')] at hfin
      exact hfin
  · dsimp only [withRoDataSep, compress512StackedMasterROSpec, compress512Blocks, Bool.cond_true,
      compress512StackedMasterTrueSpec] at hpre ⊢
    exact ⟨(stA, st, blkA, bs, n), R, hpre, fun _ _ _ hp => hp⟩

theorem compress512MasterRO_simulates_stackedMasterRO_roSep (k64 : BitVec 64)
    {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide) :
    SpecSimulates (compress512MasterROSpec k64)
      (withRoDataSep k64 sha512KBytes (compress512StackedMasterROSpec hookStack)) :=
  (compress512MasterRO_simulates_stackedMasterTrue_roSep k64 hstack).trans
    (stackedMasterTrue_roSep_simulates_stackedMasterRO_roSep k64 hookStack)

theorem stackedMasterRO_simulates_stackedMaster (hookStack : Nat := extHookStack) :
    FrameSimulates (compress512StackedMasterROSpec hookStack)
      (compress512StackedMasterSpec hookStack) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  dsimp only [compress512StackedMasterSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre
  have hbs_max : bs.length ≤ 2 ^ 64 := by
    have hblk := hmem
    simp only [sepConj_assoc] at hblk
    rw [sepConj_left_comm (stA ↦ₛ sha512StateBytesLE st) (blkA ↦ₛ bs)] at hblk
    exact ((IsBlock.pointsToBytes blkA bs).read hblk).1
  refine ⟨(false, stA, st, blkA, bs, n), ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [compress512StackedMasterROSpec, compress512Blocks, Bool.cond_false]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hbs_max⟩, hmem⟩
  · simpa only [compress512StackedMasterROSpec, compress512Blocks, Bool.cond_false,
      compress512StackedMasterSpec] using hpost

theorem compress512Master_simulates_stackedMaster_roSep (k64 : BitVec 64)
    {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide) :
    SpecSimulates (compress512MasterROSpec k64)
      (withRoDataSep k64 sha512KBytes (compress512StackedMasterSpec hookStack)) :=
  (compress512MasterRO_simulates_stackedMasterRO_roSep k64 hstack).trans
    ((stackedMasterRO_simulates_stackedMaster hookStack).withRoDataSep k64 sha512KBytes).toSpecSimulates

theorem compress512Master_simulates_roSep {β : Type} (k64 : BitVec 64) {hookStack : Nat}
    (hstack : 256 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S) :
    SpecSimulates (compress512MasterROSpec k64) (withRoDataSep k64 sha512KBytes S) :=
  (compress512Master_simulates_stackedMaster_roSep k64 hstack).trans
    (hS.withRoDataSep k64 sha512KBytes).toSpecSimulates

theorem compress512Master_simulates_ro {β : Type} (k64 : BitVec 64) {hookStack : Nat}
    (hstack : 256 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S) :
    SpecSimulates (compress512MasterROSpec k64) (withRoData k64 sha512KBytes S) :=
  (compress512Master_simulates_roSep k64 hstack hS).trans
    (SpecSimulates.withRoData_of_sep sha512KBytes_length_le)

/-- Generic placed `P : Program` bridge for any consumer `S` simulated by
`compress512StackedMasterSpec hookStack`. -/
theorem compress512_placed_ro_ok {β : Type} {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 256 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes S)) :=
  (StepsLift.SpecSimulates.withPlacedCodeLoaded
    (compress512Master_simulates_ro (pl.ρ sha2K64Sym) hstack hS)
    compress512Lib pl).subroutine_ok (compress512_master_ro_ok hpl hext)

/-- Generic `PlacedLib.subroutineOk` bridge for any consumer `S` simulated by
`compress512StackedMasterSpec hookStack`. -/
theorem compress512_ro_subroutineOk {β : Type} {hookStack : Nat} (hstack : 256 ≤ hookStack)
    {S : Spec β} (hS : FrameSimulates (compress512StackedMasterSpec hookStack) S)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes S) externs :=
  StepsLift.SpecSimulates.placedSubroutineOk
    (fun pl => compress512Master_simulates_ro (pl.ρ sha2K64Sym) hstack hS)
    (compress512_master_ro_subroutineOk externs)

/-- Placed `subroutine_ok` for the RW master stacked contract (`256 ≤ hookStack`). -/
theorem compress512_master_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (compress512StackedMasterSpec hookStack))) :=
  compress512_placed_ro_ok hpl hext hstack (fun x _ _ hpre => ⟨x, hpre, fun _ _ _ hp => hp⟩)

/-- Layout-generic `PlacedLib.subroutineOk` for the RW master stacked contract (`256 ≤ hookStack`). -/
theorem compress512_master_subroutineOk {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (compress512StackedMasterSpec hookStack)) externs :=
  compress512_ro_subroutineOk hstack (fun x _ _ hpre => ⟨x, hpre, fun _ _ _ hp => hp⟩) externs

/-- Placed `subroutine_ok` for the permission-polymorphic (`ro : Bool`) master stacked contract. -/
theorem compress512_master_ro_stacked_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 256 ≤ hookStack := by decide) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (compress512StackedMasterROSpec hookStack))) := by
  have hsim : SpecSimulates (compress512MasterROSpec (pl.ρ sha2K64Sym))
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (compress512StackedMasterROSpec hookStack)) :=
    (compress512MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K64Sym) hstack).trans
      (SpecSimulates.withRoData_of_sep sha512KBytes_length_le)
  exact (StepsLift.SpecSimulates.withPlacedCodeLoaded hsim compress512Lib pl).subroutine_ok
    (compress512_master_ro_ok hpl hext)

/-- Layout-generic `PlacedLib.subroutineOk` for the permission-polymorphic (`ro : Bool`) master
stacked contract. -/
theorem compress512_master_ro_stacked_subroutineOk {hookStack : Nat}
    (hstack : 256 ≤ hookStack := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (compress512StackedMasterROSpec hookStack)) externs := by
  refine StepsLift.SpecSimulates.placedSubroutineOk (fun pl => ?_)
    (compress512_master_ro_subroutineOk externs)
  exact (compress512MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K64Sym) hstack).trans
    (SpecSimulates.withRoData_of_sep sha512KBytes_length_le)

/-! ## 2. Byte / Endianness Bridge Lemmas for `compressInPlaceStubSpec*` -/

private theorem shared_bytesToBv8_eq_ofU8 :
    ∀ bs : List UInt8, bytesToBv8 bs = ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (shared_bytesToBv8_eq_ofU8 rest)

private theorem ofU8_toU8 : ∀ bs : List (BitVec 8), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8 rest)

private theorem toU8_ofU8 : ∀ bs : Bytes, toU8 (ofU8 bs) = bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons (by rcases b with ⟨_⟩; rfl) (toU8_ofU8 rest)

private theorem sha512State_toList_eq (h : Sha512State) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem sha512StateBytesLE_len (h : Sha512State) :
    (sha512StateBytesLE h).length = 64 := by
  rw [sha512StateBytesLE, sha512State_toList_eq]; rfl

private theorem sha512StateBytesBE_len (h : Sha512State) :
    (sha512StateBytesBE h).length = 64 := by
  simp only [sha512StateBytesBE, toU8, List.length_map, sha512State_toList_eq]
  rfl

private theorem toLEBytes8_read64 (m : Memory) (a : BitVec 64) :
    toLEBytes 8 (m.read64 a) = m.readBytes a 8 := by
  have h1 : toLEBytes 8 (m.read64 a) = unpack64 (m.read64 a) := rfl
  have hrd : m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  rw [h1, hrd]
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero]
  exact unpack64_pack64 (m.read8 a) (m.read8 (a + 1#64)) (m.read8 (a + 2#64)) (m.read8 (a + 3#64))
    (m.read8 (a + 4#64)) (m.read8 (a + 5#64)) (m.read8 (a + 6#64)) (m.read8 (a + 7#64))

private theorem sha512StateBytesLE_readSha512State (m : Memory) (a : BitVec 64) :
    sha512StateBytesLE (readSha512State m a) = m.readBytes a 64 := by
  have hget (i : Fin 8) :
      toLEBytes 8 ((readSha512State m a).get i) =
        m.readBytes (a + BitVec.ofNat 64 (8 * i.val)) 8 := by
    simp only [readSha512State, List.Vector.get_ofFn, toLEBytes8_read64]
  rw [sha512StateBytesLE, sha512State_toList_eq (readSha512State m a)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hget]
  change
    m.readBytes (a + 0#64) 8 ++
    (m.readBytes (a + 8#64) 8 ++
    (m.readBytes (a + 16#64) 8 ++
    (m.readBytes (a + 24#64) 8 ++
    (m.readBytes (a + 32#64) 8 ++
    (m.readBytes (a + 40#64) 8 ++
    (m.readBytes (a + 48#64) 8 ++
     m.readBytes (a + 56#64) 8)))))) = m.readBytes a 64
  simp only [Memory.readBytes, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    List.cons_append, List.nil_append]

private theorem ofU8_revWords64_toU8_sha512StateBytesLE (h : Sha512State) :
    revWords64 (toU8 (sha512StateBytesLE h)) = sha512StateBytesBE h := by
  rw [← toU8_ofU8 (revWords64 (toU8 (sha512StateBytesLE h)))]
  congr 1
  simp only [revWords64, ofU8, List.map_append, List.map_reverse, List.map_take, List.map_drop]
  change
    (((ofU8 (toU8 (sha512StateBytesLE h))).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 8).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 16).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 24).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 32).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 40).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 48).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 56).take 8).reverse) =
    (h.toList.flatMap (toBEBytes 8))
  rw [ofU8_toU8, sha512StateBytesLE, sha512State_toList_eq h]
  rfl

private theorem ofU8_revWords64_sha512StateBytesBE (h : Sha512State) :
    ofU8 (revWords64 (sha512StateBytesBE h)) = sha512StateBytesLE h := by
  simp only [revWords64, ofU8, List.map_append, List.map_reverse, List.map_take, List.map_drop]
  change
    (((ofU8 (sha512StateBytesBE h)).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 8).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 16).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 24).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 32).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 40).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 48).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 56).take 8).reverse) = sha512StateBytesLE h
  rw [sha512StateBytesBE, ofU8_toU8, sha512StateBytesLE, sha512State_toList_eq h]
  rfl

private theorem beWord64_toBEBytes8 (w : BitVec 64) :
    beWord 64 (toBEBytes 8 w) 0 = w := by
  change
    ((((((((0#64 <<< 8 ||| (w.extractLsb' 56 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 48 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 40 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 32 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 24 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 16 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 8 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 0 8).zeroExtend 64) = w
  bv_bits

private theorem sha512StateOf_sha512StateBytesBE (h : Sha512State) :
    sha512StateOf (sha512StateBytesBE h) = h := by
  apply List.Vector.ext
  intro i
  simp only [sha512StateOf, List.Vector.get_ofFn]
  have hslice :
      beWord 64 (ofU8 (sha512StateBytesBE h)) i.val =
        beWord 64 (toBEBytes 8 (h.get i)) 0 := by
    rw [sha512StateBytesBE, ofU8_toU8, sha512State_toList_eq h]
    fin_cases i <;> rfl
  rw [hslice, beWord64_toBEBytes8]

private theorem list_ofFn_eq_range_map {α : Type} (n : Nat) (f : Nat → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    rw [ih (fun i => f (i + 1)), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

private theorem chunks128_ofU8 (bs : Bytes) :
    chunks128 (ofU8 bs) = (chunkBlocks 128 bs).map ofU8 := by
  have hlen : (ofU8 bs).length = bs.length := by simp [ofU8]
  unfold chunks128 chunkBlocks
  rw [list_ofFn_eq_range_map ((ofU8 bs).length / 128)
      (fun i => ((ofU8 bs).drop (128 * i)).take 128),
    hlen, List.map_map]
  congr 1; funext i
  simp only [Function.comp_def, ofU8, ← List.map_drop, ← List.map_take, Nat.mul_comm 128 i]

private theorem foldl_sha512Step_modelPrims (X : UnreachedPqxdhPrimitives) (P0 : PEParams)
    (blks : List Bytes) (st : Sha512State) :
    blks.foldl (sha512Step (modelPrims X P0)) (sha512StateBytesBE st) =
      sha512StateBytesBE ((blks.map ofU8).foldl P0.Q.F512 st) := by
  induction blks generalizing st with
  | nil => rfl
  | cons blk rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hstep :
        sha512Step (modelPrims X P0) (sha512StateBytesBE st) blk =
          sha512StateBytesBE (P0.Q.F512 st (ofU8 blk)) := by
      unfold sha512Step
      change fitBytes 64
        (sha512StateBytesBE
          (P0.Q.F512 (sha512StateOf (fitBytes 64 (sha512StateBytesBE st))) (ofU8 blk))) =
        sha512StateBytesBE (P0.Q.F512 st (ofU8 blk))
      rw [fitBytes_of_length_eq (sha512StateBytesBE_len st),
        sha512StateOf_sha512StateBytesBE,
        fitBytes_of_length_eq (sha512StateBytesBE_len _)]
    rw [hstep, ih]

/-! ## 3. Simulations from `compress512StackedMasterSpec` to All Stacked Consumer Contracts -/

/-- Simulation for `CliExt.compress512Spec Q` when `Q.F512 = sha512CompressState`. -/
theorem stackedMaster_simulates_cliExt {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec extHookStack)
      (CryptoVerification.SignalSession.CliExt.compress512Spec Q) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  refine ⟨(stA, st, blkA, bs, n), ?_, fun sf _ _ hpost => ?_⟩
  · simpa only [CryptoVerification.SignalSession.CliExt.compress512Spec,
      CryptoVerification.SignalSession.CliExt.withStack, compress512StackedMasterSpec,
      sepConj_assoc] using hpre
  · dsimp only [compress512StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hpf, _⟩, hmem⟩ := hpost
    dsimp only [CryptoVerification.SignalSession.CliExt.compress512Spec,
      CryptoVerification.SignalSession.CliExt.withStack]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj, hF]
    exact ⟨hpf.2.1, hmem⟩

/-- Simulation for `CliExt.compress512Spec Q` with `keepsFs`. -/
theorem stackedMaster_simulates_cliExt_keepsFs {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec extHookStack)
      (keepsFs (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) :=
  (stackedMaster_simulates_cliExt hF).keepsFs_of_stackedMaster

/-- Simulation for `CliExt.compress512Spec Q` with `SpecBudget.withVmPreserved`. -/
theorem stackedMaster_simulates_cliExt_budget {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec extHookStack)
      (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) :=
  (stackedMaster_simulates_cliExt hF).withVmPreserved_of_stackedMaster

private def compressInPlaceAtStack (fn : Bytes → Bytes → Bytes) (stk : Nat) :
    Spec CryptoCompressGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.statePtr ∧
      s.readReg64 .x1 = g.blocksPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.nBlocks ∧
      g.nBlocks < 2 ^ 64 ∧
      g.stateBytes.length = 64 ∧
      g.blockBytes.length = 128 * g.nBlocks⌝ ∗
      (g.statePtr ↦ₛ bytesToBv8 g.stateBytes) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s.sp stk
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.statePtr ↦ₛ fitBv8 64 (fn g.stateBytes g.blockBytes)) ∗
      (g.blocksPtr ↦ₛ bytesToBv8 g.blockBytes) ∗
      stackAt s0.sp stk

private theorem stackedMaster_simulates_compressInPlaceAtStack
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) (stk : Nat) :
    FrameSimulates (compress512StackedMasterSpec stk)
      (compressInPlaceAtStack (sha512CompressOutBytes (modelPrims X P0)) stk) := by
  intro g R s0 hpre
  dsimp only [compressInPlaceAtStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn_lt, hst_len, hblk_len⟩, hmem⟩
  have hx2_nat : (s0.readReg64 .x2).toNat = g.nBlocks := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt]
  have hst_read : s0.mem.readBytes g.statePtr 64 = ofU8 g.stateBytes := by
    have hlen' : (bytesToBv8 g.stateBytes).length = 64 := by simp [bytesToBv8, hst_len]
    have hrd := ((IsBlock.pointsToBytes g.statePtr (bytesToBv8 g.stateBytes)).read hmem).2
    rw [hlen', shared_bytesToBv8_eq_ofU8] at hrd
    exact hrd
  let st0 : Sha512State := readSha512State s0.mem g.statePtr
  have hle_st0 : sha512StateBytesLE st0 = bytesToBv8 g.stateBytes := by
    rw [sha512StateBytesLE_readSha512State, hst_read, ← shared_bytesToBv8_eq_ofU8]
  have hblk_bv_len : (bytesToBv8 g.blockBytes).length = 128 * g.nBlocks := by
    simp [bytesToBv8, hblk_len]
  refine ⟨(g.statePtr, st0, g.blocksPtr, bytesToBv8 g.blockBytes, g.nBlocks), ?_,
    fun sf _ _ hpost => ?_⟩
  · dsimp only [compress512StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj, hle_st0]
    exact ⟨⟨hx0, hx1, hx2_nat, hblk_bv_len⟩, hmem⟩
  · dsimp only [compress512StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hpf, _⟩, hmemf⟩ := hpost
    have hrev_st : revWords64 g.stateBytes = sha512StateBytesBE st0 := by
      have hst_eq : g.stateBytes = toU8 (sha512StateBytesLE st0) := by
        rw [hle_st0, shared_bytesToBv8_eq_ofU8, toU8_ofU8]
      rw [hst_eq, ofU8_revWords64_toU8_sha512StateBytesLE]
    let stFinal := (chunks128 (ofU8 g.blockBytes)).foldl P0.Q.F512 st0
    have hout_eq :
        fitBv8 64 (sha512CompressOutBytes (modelPrims X P0) g.stateBytes g.blockBytes) =
          sha512StateBytesLE stFinal := by
      unfold sha512CompressOutBytes
      rw [hrev_st, foldl_sha512Step_modelPrims, ← chunks128_ofU8,
        fitBytes_of_length_eq (sha512StateBytesBE_len stFinal)]
      have hrev_len : (revWords64 (sha512StateBytesBE stFinal)).length = 64 := by
        have hlen_ofU8 : (ofU8 (revWords64 (sha512StateBytesBE stFinal))).length =
            (revWords64 (sha512StateBytesBE stFinal)).length := by simp [ofU8]
        rw [← hlen_ofU8, ofU8_revWords64_sha512StateBytesBE, sha512StateBytesLE_len]
      rw [fitBv8_eq_bytesToBv8 hrev_len, shared_bytesToBv8_eq_ofU8,
        ofU8_revWords64_sha512StateBytesBE]
    dsimp only [compressInPlaceAtStack]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj, hout_eq]
    refine ⟨hpf.2.1, ?_⟩
    dsimp only [stFinal]
    rw [hF, ← shared_bytesToBv8_eq_ofU8]
    exact hmemf

/-- Simulation for `compressInPlaceStubSpecPlaced ... 64 128` at `pqxdhHookStack = 4096`. -/
theorem stackedMaster_simulates_pqxdhStubPlaced (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec pqxdhHookStack)
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128) :=
  stackedMaster_simulates_compressInPlaceAtStack X hF pqxdhHookStack

theorem stackedMaster_simulates_pqxdhStubPlaced_keepsFs (X : UnreachedPqxdhPrimitives)
    {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec pqxdhHookStack)
      (keepsFs (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)) :=
  (stackedMaster_simulates_pqxdhStubPlaced X hF).keepsFs_of_stackedMaster

theorem stackedMaster_simulates_pqxdhStubPlaced_budget (X : UnreachedPqxdhPrimitives)
    {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    FrameSimulates (compress512StackedMasterSpec pqxdhHookStack)
      (withVmPreserved
        (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)) :=
  (stackedMaster_simulates_pqxdhStubPlaced X hF).withVmPreserved_of_stackedMaster

/-! ## 4. Placed `subroutine_ok` & `PlacedLib.subroutineOk` Corollaries -/

theorem compress512_cliExt_keepsFs_placed_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (keepsFs (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))) := by
  rw [keepsFs_withRoData]
  exact compress512_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_cliExt_keepsFs hF)

theorem compress512_cliExt_placed_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  compress512_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_cliExt hF)

theorem compress512_cliExt_budget_placed_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))) :=
  compress512_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_cliExt_budget hF)

theorem compress512_cliExt_subroutineOk {Q : PqxdhPrims} (hF : Q.F512 = sha512CompressState)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) externs :=
  compress512_ro_subroutineOk (by decide) (stackedMaster_simulates_cliExt hF) externs

theorem compress512_cliExt_budget_subroutineOk {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) externs :=
  compress512_ro_subroutineOk (by decide) (stackedMaster_simulates_cliExt_budget hF) externs

theorem compress512_pqxdhStubPlaced_placed_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  compress512_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_pqxdhStubPlaced X hF)

theorem compress512_pqxdhStubPlaced_budget_placed_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 9652 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    subroutine_ok P (compress512Lib.fnAddr pl compress512Sym)
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (withVmPreserved
            (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))) :=
  compress512_placed_ro_ok hpl hext (by decide)
    (stackedMaster_simulates_pqxdhStubPlaced_budget X hF)

theorem compress512_pqxdhStubPlaced_subroutineOk (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))
      externs :=
  compress512_ro_subroutineOk (by decide) (stackedMaster_simulates_pqxdhStubPlaced X hF) externs

theorem compress512_pqxdhStubPlaced_budget_subroutineOk (X : UnreachedPqxdhPrimitives)
    {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState)
    (externs : String → Option (State → State) := fun _ => none) :
    compress512Lib.subroutineOk compress512Sym
      (fun pl => withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (withVmPreserved
          (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))
      externs :=
  compress512_ro_subroutineOk (by decide)
    (stackedMaster_simulates_pqxdhStubPlaced_budget X hF) externs

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512
