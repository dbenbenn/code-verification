/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift -- proof-setup: allow-public-import
import ProofLib.SepLogic.HeapIntro

/-!
# Stacked Consumer Contract Bridges for `sha2::sha256::compress256`

Simulations and `subroutine_ok` / `PlacedLib.subroutineOk` corollaries linking
`compress256Lib` (`176 ≤ hookStack` / `176 ≤ pkStack`) to each consumer contract:

1. `CliExt.compress256Spec C` (`C.F = sha256CompressState`, with and without `keepsFs`).
2. `HkdfExt.compress256ExternShaSpec sha256CompressState hookStack`.
3. `SpqrV1.Kdf.spqrCompress256ExternSpec sha256CompressState hookStack`.
4. `LibsignalTripleRatchet.withStack (LibsignalTripleRatchet.compress256Spec sha256CompressState) hookStack`.
5. `LibsignalTripleRatchet.withStack (ComputeBudgetAux.compress256BudgetSpec sha256CompressState) hookStack`
   and `withStack (ComputeBudgetAux.session2Compress256BudgetSpec sha256CompressState) hookStack`.
6. `session2Compress256PkStackSpecAt sha256CompressState pkStack sp_cur` (including `SpecX`)
   and `ComputeBudgetAux.session2Compress256PkStackBudgetSpecAt sha256CompressState pkStack sp_cur`.
7. `LibsignalTripleRatchet.withStack (Slots.compress256SingleSpec sha256CompressState) hookStack`
   (with and without `withVmPreserved`).
8. `sessionCompress256ROBudgetSpec sha256CompressState hookStack` (in section 3 below).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack publicKeySerializeStack publicKeySerializeStackX withStack
   session2Compress256Spec session2Compress256PkStackSpecAt session2Compress256PkStackSpecX)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (compress256ExternShaSpec)
open CryptoVerification.SpqrV1.Kdf (spqrCompress256ExternSpec)
open CryptoVerification.SignalSession.Cli.Slots (compress256SingleSpec)
open LibsignalBinary.Heap (AllocCallPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (compress256Blocks sessionCompress256ROSpec sessionCompress256ROBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux
  (compress256BudgetSpec session2Compress256BudgetSpec session2Compress256PkStackBudgetSpecAt)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (withRoData withRoDataSep SpecSimulates keepsFs_withRoData)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Sym sha2K32Sym compress256Lib)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
  (chunks64_of_length_lt chunks64_cons_take_drop compress256RawROSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (ProcessFieldsPreserved_toHeapVmPreserved stackAt_le_two_pow_64 stackAt_split_frame176
   withPlacedCodeLoaded compress256MasterROSpec compress256_master_ro_ok
   compress256_master_ro_subroutineOk)

/-! ## 1. Master Stacked Intermediate Spec & `.rodata` Transport -/

private theorem sha256KBytes_length_le : sha256KBytes.length ≤ 2 ^ 64 := by
  have h : sha256KBytes.length = 256 := by
    simp [sha256KBytes, List.length_flatMap, unpack32_length, Sha256Cells.sha256K_length]
  omega

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
`compress256` contract without `.rodata` `K32`, preserving full `ProcessFieldsPreserved s0 sf`
and `AllocCallPreserved s0 sf`. -/
@[expose] def compress256StackedMasterROSpec (hookStack : Nat := extHookStack) :
    Spec (Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (ro, stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 64 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ compress256Blocks ro blkA bs ∗ stackAt s0.sp hookStack
  post := fun (ro, stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 bs).foldl sha256CompressState st)) ∗
      compress256Blocks ro blkA bs ∗ stackAt s0.sp hookStack

/-- Stack-parameterized (`hookStack`-byte) RW master `compress256` contract without `.rodata`
`K32`, preserving full `ProcessFieldsPreserved s0 sf`. -/
@[expose] def compress256StackedMasterSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 64 * n⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 bs).foldl sha256CompressState st)) ∗
      (blkA ↦ₛ bs) ∗ stackAt s0.sp hookStack

/-- Stack-splitting simulation (`176 ≤ hookStack`) from `compress256MasterROSpec k32` to the
`ro = true` branch of `withRoDataSep k32 sha256KBytes (compress256StackedMasterROSpec hookStack)`. -/
private def compress256StackedMasterTrueSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 64 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 bs).foldl sha256CompressState st)) ∗
      (blkA ↦ᵣ bs) ∗ stackAt s0.sp hookStack

private theorem compress256MasterRO_simulates_stackedMasterTrue_roSep (k32 : BitVec 64)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    SpecSimulates (compress256MasterROSpec k32)
      (withRoDataSep k32 sha256KBytes (compress256StackedMasterTrueSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  dsimp only [withRoDataSep, compress256StackedMasterTrueSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hpre⟩ := hpre
  have hmax : hookStack ≤ 2 ^ 64 := by
    have hstk := Satisfies.of_sep_right hpre
    rw [sepConj_left_comm (blkA ↦ᵣ bs) (stackAt s0.sp hookStack)] at hstk
    exact stackAt_le_two_pow_64 hstk
  rw [stackAt_split_frame176 s0 hstack hmax] at hpre
  simp only [sepConj_assoc] at hpre
  refine ⟨(stA, st, blkA, bs, n), stackAt (s0.sp - 176#64) (hookStack - 176) ∗ R, ?_, ?_⟩
  · dsimp only [compress256MasterROSpec, compress256RawROSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hpure, hpre⟩
  · intro sf hret _hcc hpost
    dsimp only [compress256MasterROSpec, compress256RawROSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    have hsf_sp : stackFrame sf 176 = stackFrame s0 176 := by
      simp only [stackFrame, hret.2.1]
    rw [hsf_sp] at hpost
    dsimp only [withRoDataSep, compress256StackedMasterTrueSpec]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜ProcessFieldsPreserved s0 sf ∧ AllocCallPreserved s0 sf⌝,
        satisfies_pure_sepConj]
    refine ⟨hpf, ?_⟩
    rw [stackAt_split_frame176 s0 hstack hmax]
    simpa only [sepConj_assoc] using hpost

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Heap.Disjoint Heap.union Heap.Matches regionHeap regionHeapRO in
private theorem stackedMasterTrue_roSep_simulates_stackedMasterRO_roSep
    (k32 : BitVec 64) (hookStack : Nat := extHookStack) :
    SpecSimulates
      (withRoDataSep k32 sha256KBytes (compress256StackedMasterTrueSpec hookStack))
      (withRoDataSep k32 sha256KBytes (compress256StackedMasterROSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hpre
  cases ro
  · dsimp only [withRoDataSep, compress256StackedMasterROSpec, compress256Blocks,
      Bool.cond_false] at hpre
    simp only [sepConj_assoc] at hpre
    rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpre
    obtain ⟨hpure, hmem0⟩ := hpre
    have hbs_max : bs.length ≤ 2 ^ 64 := hpure.2.2.2.2
    have hk_max : sha256KBytes.length ≤ 2 ^ 64 := by
      have hlen : sha256KBytes.length = 256 := by
        simp [sha256KBytes, List.length_flatMap, unpack32_length,
          List.map_const', Sha256Cells.sha256K_length]
      omega
    have hmem : s0.mem ⊨ (blkA ↦ₛ bs) ∗
        (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st) ∗ stackAt s0.sp hookStack)) ∗ R) := by
      simp only [sepConj_assoc] at hmem0 ⊢
      rw [sepConj_left_comm (stA ↦ₛ shaStateBytes st) (blkA ↦ₛ bs),
          sepConj_left_comm (k32 ↦ᵣ sha256KBytes) (blkA ↦ₛ bs)] at hmem0
      exact hmem0
    obtain ⟨h_blk, h_QR, hd0, hb0, hQR0, hm0⟩ := Satisfies.sepConj_elim hmem
    obtain ⟨h_Q0, h_R, hdQR0, rfl, hQ0, hR0⟩ := SepProp.holds_sepConj_elim hQR0
    obtain ⟨h_k0, h_ststk0, hdk0, rfl, hk0, _⟩ := SepProp.holds_sepConj_elim hQ0
    obtain ⟨m_b0, _, rfl⟩ := ((IsBlock.pointsToBytes blkA bs).iff h_blk).mp hb0
    obtain ⟨m_k0, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO k32 sha256KBytes hk_max).iff h_k0).mp hk0
    have hm_blk0 : (regionHeap blkA bs.length m_b0).Matches s0.mem := Heap.Matches.of_union_left hm0
    have hrw0_perm : ∀ a, InRegion blkA bs.length a → s0.mem.perm a = some Perm.rw := by
      intro a ha
      have hv : (regionHeap blkA bs.length m_b0).phys a = some (.rw (m_b0.read8 a)) := by
        simp [regionHeap, ha]
      exact (hm_blk0.1 a (.rw (m_b0.read8 a)) hv).2.1
    have hnk32 : ∀ a, InRegion blkA bs.length a → ¬ InRegion k32 sha256KBytes.length a := by
      intro a ha hka
      have hv : (regionHeap blkA bs.length m_b0).phys a = some (.rw (m_b0.read8 a)) := by
        simp [regionHeap, ha]
      have hkv : (regionHeapRO k32 sha256KBytes.length m_k0).phys a = some (.ro (m_k0.read8 a)) := by
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
        cases h1a : (regionHeapRO k32 sha256KBytes.length m_k0).phys a with
        | some _ => simp [h1a] at h2
        | none =>
          cases h1b : h_ststk0.phys a with
          | some _ => simp [h1a, h1b] at h2
          | none => simpa [h1a, h1b] using h2
      · rw [hv] at h1; cases h1
    have hmem_R₁ : s0.mem ⊨ (blkA ↦ₛ bs) ∗
        (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st) ∗ stackAt s0.sp hookStack)) ∗ R₁) :=
      Satisfies.sepConj_intro hd0 hb0 (SepProp.holds_sepConj_intro hdQR0 hQ0 hR₁) hm0
    have hmem_ro : s0.mem ⊨ (blkA ↦ᵣ bs) ∗
        (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st) ∗ stackAt s0.sp hookStack)) ∗ R₁) :=
      Satisfies.pointsToBytes_to_ro hmem_R₁
    refine ⟨(stA, st, blkA, bs, n), R₁, ?_, ?_⟩
    · dsimp only [withRoDataSep, compress256StackedMasterTrueSpec]
      simp only [sepConj_assoc]
      rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜_⌝, satisfies_pure_sepConj]
      refine ⟨hpure, ?_⟩
      simp only [sepConj_assoc] at hmem_ro ⊢
      rw [sepConj_left_comm (blkA ↦ᵣ bs) (k32 ↦ᵣ sha256KBytes),
          sepConj_left_comm (blkA ↦ᵣ bs) (stA ↦ₛ shaStateBytes st)] at hmem_ro
      exact hmem_ro
    · intro sf _hret _hcc hpost
      dsimp only [withRoDataSep, compress256StackedMasterTrueSpec] at hpost
      simp only [sepConj_assoc] at hpost
      rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜_⌝, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨hpf, hacp⟩, hpost_m0⟩ := hpost
      let st' := (chunks64 bs).foldl sha256CompressState st
      have hpost_m' : sf.mem ⊨ (blkA ↦ᵣ bs) ∗
          (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st') ∗ stackAt s0.sp hookStack)) ∗ R₁) := by
        simp only [sepConj_assoc] at hpost_m0 ⊢
        rw [sepConj_left_comm (stA ↦ₛ shaStateBytes st') (blkA ↦ᵣ bs),
            sepConj_left_comm (k32 ↦ᵣ sha256KBytes) (blkA ↦ᵣ bs)] at hpost_m0
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
      obtain ⟨m_kf, _, rfl⟩ := ((IsBlockRO.pointsToBytesRO k32 sha256KBytes hk_max).iff h_kf).mp hkf_p
      obtain ⟨m_st, _, rfl⟩ := ((IsBlock.pointsToBytes stA (shaStateBytes st')).iff h_st).mp hst_p
      obtain ⟨m_stk, _, rfl⟩ := ((IsBlock.memRegion (s0.sp - BitVec.ofNat 64 hookStack) hookStack).iff h_stk).mp hstk_p
      have h_rest_none : ∀ a, InRegion blkA bs.length a →
          (((regionHeapRO k32 sha256KBytes.length m_kf).union
            ((regionHeap stA (shaStateBytes st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf).phys a = none := by
        intro a ha
        have hro_a : (regionHeapRO blkA bs.length m_ro).phys a = some (.ro (m_ro.read8 a)) := by
          simp [regionHeapRO, ha]
        have hk_none : (regionHeapRO k32 sha256KBytes.length m_kf).phys a = none := by
          simp [regionHeapRO, hnk32 a ha]
        have hst_none : (regionHeap stA (shaStateBytes st').length m_st).phys a = none := by
          by_cases hin : InRegion stA (shaStateBytes st').length a
          · have h1 : (regionHeap stA (shaStateBytes st').length m_st).phys a = some (.rw (m_st.read8 a)) := by
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
          (((regionHeapRO k32 sha256KBytes.length m_kf).union
            ((regionHeap stA (shaStateBytes st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf) := by
        refine Heap.Disjoint.of_phys_left rfl rfl fun a => ?_
        by_cases ha : InRegion blkA bs.length a
        · exact Or.inr (Or.inl (h_rest_none a ha))
        · exact Or.inl (by simp [h_rw, regionHeap, ha])
      have hb_rw : (blkA ↦ₛ bs) h_rw :=
        ((IsBlock.pointsToBytes blkA bs).iff h_rw).mpr ⟨sf.mem, ⟨hbs_max, hbs_sf⟩, rfl⟩
      have hm_rw : h_rw.Matches sf.mem := IsBlock.regionHeap_matches blkA bs.length sf.mem hrw_sf
      have hQfR_orig :
          (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st') ∗ stackAt s0.sp hookStack)) ∗ R)
          (((regionHeapRO k32 sha256KBytes.length m_kf).union
            ((regionHeap stA (shaStateBytes st').length m_st).union
              (regionHeap (s0.sp - BitVec.ofNat 64 hookStack) hookStack m_stk))).union h_Rf) :=
        SepProp.holds_sepConj_intro hdQfR
          (SepProp.holds_sepConj_intro hdkf hkf_p (SepProp.holds_sepConj_intro hdst hst_p hstk_p))
          hRf_p
      have hfin : sf.mem ⊨ (blkA ↦ₛ bs) ∗
          (((k32 ↦ᵣ sha256KBytes) ∗ ((stA ↦ₛ shaStateBytes st') ∗ stackAt s0.sp hookStack)) ∗ R) :=
        Satisfies.sepConj_intro hd_rw hb_rw hQfR_orig (Heap.Matches.union hm_rw hm_QfR)
      dsimp only [withRoDataSep, compress256StackedMasterROSpec, compress256Blocks, Bool.cond_false]
      simp only [sepConj_assoc]
      rw [sepConj_left_comm (k32 ↦ᵣ sha256KBytes) ⌜_⌝, satisfies_pure_sepConj]
      refine ⟨⟨hpf, hacp⟩, ?_⟩
      simp only [sepConj_assoc] at hfin ⊢
      rw [sepConj_left_comm (blkA ↦ₛ bs) (k32 ↦ᵣ sha256KBytes),
          sepConj_left_comm (blkA ↦ₛ bs) (stA ↦ₛ shaStateBytes st')] at hfin
      exact hfin
  · dsimp only [withRoDataSep, compress256StackedMasterROSpec, compress256Blocks, Bool.cond_true,
      compress256StackedMasterTrueSpec] at hpre ⊢
    exact ⟨(stA, st, blkA, bs, n), R, hpre, fun _ _ _ hp => hp⟩

theorem compress256MasterRO_simulates_stackedMasterRO_roSep (k32 : BitVec 64)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    SpecSimulates (compress256MasterROSpec k32)
      (withRoDataSep k32 sha256KBytes (compress256StackedMasterROSpec hookStack)) :=
  (compress256MasterRO_simulates_stackedMasterTrue_roSep k32 hstack).trans
    (stackedMasterTrue_roSep_simulates_stackedMasterRO_roSep k32 hookStack)

theorem stackedMasterRO_simulates_stackedMaster (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterROSpec hookStack)
      (compress256StackedMasterSpec hookStack) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  dsimp only [compress256StackedMasterSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre
  have hbs_max : bs.length ≤ 2 ^ 64 := by
    have hblk := hmem
    simp only [sepConj_assoc] at hblk
    rw [sepConj_left_comm (stA ↦ₛ shaStateBytes st) (blkA ↦ₛ bs)] at hblk
    exact ((IsBlock.pointsToBytes blkA bs).read hblk).1
  refine ⟨(false, stA, st, blkA, bs, n), ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [compress256StackedMasterROSpec, compress256Blocks, Bool.cond_false]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hbs_max⟩, hmem⟩
  · dsimp only [compress256StackedMasterROSpec, compress256Blocks, Bool.cond_false] at hpost
    dsimp only [compress256StackedMasterSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.1, hpost.2⟩

/-- Single stack-splitting simulation (`176 ≤ hookStack`) from `compress256MasterROSpec k32` to
`withRoDataSep k32 sha256KBytes (compress256StackedMasterSpec hookStack)`. -/
theorem compress256Master_simulates_stackedMaster_roSep (k32 : BitVec 64)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    SpecSimulates (compress256MasterROSpec k32)
      (withRoDataSep k32 sha256KBytes (compress256StackedMasterSpec hookStack)) :=
  (compress256MasterRO_simulates_stackedMasterRO_roSep k32 hstack).trans
    ((stackedMasterRO_simulates_stackedMaster hookStack).withRoDataSep k32 sha256KBytes).toSpecSimulates

/-- Generic transport from `FrameSimulates (compress256StackedMasterSpec hookStack) S` to
`withRoDataSep k32 sha256KBytes S`. -/
theorem compress256Master_simulates_roSep {β : Type} (k32 : BitVec 64) {hookStack : Nat}
    (hstack : 176 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress256StackedMasterSpec hookStack) S) :
    SpecSimulates (compress256MasterROSpec k32) (withRoDataSep k32 sha256KBytes S) :=
  (compress256Master_simulates_stackedMaster_roSep k32 hstack).trans
    (hS.withRoDataSep k32 sha256KBytes).toSpecSimulates

/-- Generic transport from `FrameSimulates (compress256StackedMasterSpec hookStack) S` to pure
`withRoData k32 sha256KBytes S`. -/
theorem compress256Master_simulates_ro {β : Type} (k32 : BitVec 64) {hookStack : Nat}
    (hstack : 176 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress256StackedMasterSpec hookStack) S) :
    SpecSimulates (compress256MasterROSpec k32) (withRoData k32 sha256KBytes S) :=
  (compress256Master_simulates_roSep k32 hstack hS).trans
    (SpecSimulates.withRoData_of_sep sha256KBytes_length_le)

/-- Generic placed `P : Program` bridge for any consumer `S` simulated by
`compress256StackedMasterSpec hookStack`. -/
theorem compress256_placed_ro_ok {β : Type} {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack) {S : Spec β}
    (hS : FrameSimulates (compress256StackedMasterSpec hookStack) S) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes S)) :=
  (StepsLift.SpecSimulates.withPlacedCodeLoaded
    (compress256Master_simulates_ro (pl.ρ sha2K32Sym) hstack hS)
    compress256Lib pl).subroutine_ok (compress256_master_ro_ok hpl hext)

/-- Generic `PlacedLib.subroutineOk` bridge for any consumer `S` simulated by
`compress256StackedMasterSpec hookStack`. -/
theorem compress256_ro_subroutineOk {β : Type} {hookStack : Nat} (hstack : 176 ≤ hookStack)
    {S : Spec β} (hS : FrameSimulates (compress256StackedMasterSpec hookStack) S)
    (externs : String → Option (State → State) := fun _ => none) :
    compress256Lib.subroutineOk compress256Sym
      (fun pl => withRoData (pl.ρ sha2K32Sym) sha256KBytes S) externs :=
  StepsLift.SpecSimulates.placedSubroutineOk
    (fun pl => compress256Master_simulates_ro (pl.ρ sha2K32Sym) hstack hS)
    (compress256_master_ro_subroutineOk externs)

/-! ## 2. Simulations from `compress256StackedMasterSpec` to Consumer Contracts -/

/-- Consumer 4 (`LibsignalTripleRatchet.withStack (compress256Spec sha256CompressState) hookStack`),
strengthened with `keepsFs`. -/
theorem stackedMaster_simulates_tripleRatchet_keepsFs (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (keepsFs (withStack (CryptoVerification.LibsignalTripleRatchet.compress256Spec sha256CompressState) hookStack)) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  refine ⟨(stA, st, blkA, bs, n), ?_, ?_⟩
  · simpa only [keepsFs, withStack, CryptoVerification.LibsignalTripleRatchet.compress256Spec,
      compress256StackedMasterSpec, sepConj_assoc] using hpre
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    dsimp only [keepsFs, withStack, CryptoVerification.LibsignalTripleRatchet.compress256Spec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpf.1, hpf.2.1, hpost⟩

/-- Consumer 4 (`LibsignalTripleRatchet.withStack (compress256Spec sha256CompressState) hookStack`). -/
theorem stackedMaster_simulates_tripleRatchet (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (withStack (CryptoVerification.LibsignalTripleRatchet.compress256Spec sha256CompressState) hookStack) :=
  (stackedMaster_simulates_tripleRatchet_keepsFs hookStack).trans FrameSimulates.drop_keepsFs

/-- Consumer 1 (`CliExt.compress256Spec C` when `C.F = sha256CompressState`), with `keepsFs`. -/
theorem stackedMaster_simulates_cliExt_keepsFs {C : Crypto} (hF : C.F = sha256CompressState) :
    FrameSimulates (compress256StackedMasterSpec extHookStack)
      (keepsFs (CryptoVerification.SignalSession.CliExt.compress256Spec C)) := by
  have heq : CryptoVerification.SignalSession.CliExt.compress256Spec C =
      withStack (CryptoVerification.LibsignalTripleRatchet.compress256Spec sha256CompressState) extHookStack := by
    unfold CryptoVerification.SignalSession.CliExt.compress256Spec
      CryptoVerification.SignalSession.CliExt.withStack
      withStack CryptoVerification.LibsignalTripleRatchet.compress256Spec
    rw [hF]
  rw [heq]
  exact stackedMaster_simulates_tripleRatchet_keepsFs extHookStack

/-- Consumer 1 (`CliExt.compress256Spec C` when `C.F = sha256CompressState`). -/
theorem stackedMaster_simulates_cliExt {C : Crypto} (hF : C.F = sha256CompressState) :
    FrameSimulates (compress256StackedMasterSpec extHookStack)
      (CryptoVerification.SignalSession.CliExt.compress256Spec C) :=
  (stackedMaster_simulates_cliExt_keepsFs hF).trans FrameSimulates.drop_keepsFs

/-- Consumer 2 (`HkdfExt.compress256ExternShaSpec sha256CompressState hookStack`). -/
theorem stackedMaster_simulates_hkdfExt (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (compress256ExternShaSpec sha256CompressState hookStack) := by
  rintro ⟨stA, blkA, st, bs⟩ R s0 hpre
  dsimp only [compress256ExternShaSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hbs⟩, hpre⟩ := hpre
  rw [sepConj_left_comm (blkA ↦ₛ bs) (stA ↦ₛ shaStateBytes st)] at hpre
  refine ⟨(stA, st, blkA, bs, (s0.readReg64 .x2).toNat), ?_, ?_⟩
  · dsimp only [compress256StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, trivial, hbs.symm⟩, hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    rw [sepConj_left_comm (stA ↦ₛ _) (blkA ↦ₛ bs)] at hpost
    dsimp only [compress256ExternShaSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hpf.2.1, hpost⟩

/-- Consumer 3 (`SpqrV1.Kdf.spqrCompress256ExternSpec sha256CompressState hookStack`). -/
theorem stackedMaster_simulates_spqrExt (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (spqrCompress256ExternSpec sha256CompressState hookStack) := by
  have heq : spqrCompress256ExternSpec sha256CompressState hookStack =
      compress256ExternShaSpec sha256CompressState hookStack := rfl
  rw [heq]
  exact stackedMaster_simulates_hkdfExt hookStack

/-- Consumer 5a (`withStack (ComputeBudgetAux.compress256BudgetSpec sha256CompressState) hookStack`). -/
theorem stackedMaster_simulates_budget (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (withStack (compress256BudgetSpec sha256CompressState) hookStack) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  refine ⟨(stA, st, blkA, bs, n), ?_, ?_⟩
  · simpa only [withStack, compress256BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.compress256Spec,
      compress256StackedMasterSpec, sepConj_assoc] using hpre
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    dsimp only [withStack, compress256BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.compress256Spec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨ProcessFieldsPreserved_toHeapVmPreserved hpf, hpf.2.1, hpost⟩

/-- Consumer 5b (`withStack (ComputeBudgetAux.session2Compress256BudgetSpec sha256CompressState) hookStack`). -/
theorem stackedMaster_simulates_session2Budget (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (withStack (session2Compress256BudgetSpec sha256CompressState) hookStack) := by
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpre
  refine ⟨(stA, st, blkA, bs, n), ?_, ?_⟩
  · simpa only [withStack, session2Compress256BudgetSpec, session2Compress256Spec,
      compress256StackedMasterSpec, sepConj_assoc] using hpre
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    dsimp only [withStack, session2Compress256BudgetSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpf.2.1, ProcessFieldsPreserved_toHeapVmPreserved hpf⟩, hpost⟩

/-- Consumer 6a (`session2Compress256PkStackSpecAt sha256CompressState pkStack sp_cur`). -/
theorem stackedMaster_simulates_pkStackAt (pkStack : Nat) (sp_cur : BitVec 64) :
    FrameSimulates (compress256StackedMasterSpec pkStack)
      (session2Compress256PkStackSpecAt sha256CompressState pkStack sp_cur) := by
  rintro ⟨stA, st, blkA, blk, n⟩ R s0 hpre
  dsimp only [session2Compress256PkStackSpecAt] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hblk, hsp⟩, hpre⟩ := hpre
  rw [← hsp] at hpre
  refine ⟨(stA, st, blkA, blk, n), ?_, ?_⟩
  · dsimp only [compress256StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hblk⟩, hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    rw [hsp] at hpost
    dsimp only [session2Compress256PkStackSpecAt]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hpf.2.1, hpost⟩

/-- Consumer 6b (`ComputeBudgetAux.session2Compress256PkStackBudgetSpecAt sha256CompressState pkStack sp_cur`). -/
theorem stackedMaster_simulates_pkStackBudgetAt (pkStack : Nat) (sp_cur : BitVec 64) :
    FrameSimulates (compress256StackedMasterSpec pkStack)
      (session2Compress256PkStackBudgetSpecAt sha256CompressState pkStack sp_cur) := by
  rintro ⟨stA, st, blkA, blk, n⟩ R s0 hpre
  dsimp only [session2Compress256PkStackBudgetSpecAt] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hblk, hsp⟩, hpre⟩ := hpre
  rw [← hsp] at hpre
  refine ⟨(stA, st, blkA, blk, n), ?_, ?_⟩
  · dsimp only [compress256StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hblk⟩, hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    rw [hsp] at hpost
    dsimp only [session2Compress256PkStackBudgetSpecAt]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpf.2.1, ProcessFieldsPreserved_toHeapVmPreserved hpf⟩, hpost⟩

/-- Consumer 7a (`withStack (Slots.compress256SingleSpec sha256CompressState) hookStack`). -/
theorem stackedMaster_simulates_single (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (withStack (compress256SingleSpec sha256CompressState) hookStack) := by
  rintro ⟨stA, st, blkA, blk⟩ R s0 hpre
  dsimp only [withStack, compress256SingleSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hblk⟩, hpre⟩ := hpre
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine ⟨(stA, st, blkA, blk, 1), ?_, ?_⟩
  · dsimp only [compress256StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_nat, by omega⟩, hpre⟩
  · intro sf _hret _hcc hpost
    have hchunks1 : (chunks64 blk).foldl sha256CompressState st = sha256CompressState st blk := by
      rw [chunks64_cons_take_drop (by omega), List.take_of_length_le (by omega),
          chunks64_of_length_lt (by simp [hblk]), List.foldl_cons, List.foldl_nil]
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj, hchunks1] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    dsimp only [withStack, compress256SingleSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hpf.2.1, hpost⟩

/-- Consumer 7b (`withStack (withVmPreserved (Slots.compress256SingleSpec sha256CompressState)) hookStack`). -/
theorem stackedMaster_simulates_singleBudget (hookStack : Nat := extHookStack) :
    FrameSimulates (compress256StackedMasterSpec hookStack)
      (withStack (withVmPreserved (compress256SingleSpec sha256CompressState)) hookStack) := by
  rintro ⟨stA, st, blkA, blk⟩ R s0 hpre
  dsimp only [withStack, withVmPreserved, compress256SingleSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hblk⟩, hpre⟩ := hpre
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine ⟨(stA, st, blkA, blk, 1), ?_, ?_⟩
  · dsimp only [compress256StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_nat, by omega⟩, hpre⟩
  · intro sf _hret _hcc hpost
    have hchunks1 : (chunks64 blk).foldl sha256CompressState st = sha256CompressState st blk := by
      rw [chunks64_cons_take_drop (by omega), List.take_of_length_le (by omega),
          chunks64_of_length_lt (by simp [hblk]), List.foldl_cons, List.foldl_nil]
    dsimp only [compress256StackedMasterSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj, hchunks1] at hpost
    obtain ⟨hpf, hpost⟩ := hpost
    dsimp only [withStack, withVmPreserved, compress256SingleSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨ProcessFieldsPreserved_toHeapVmPreserved hpf, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hpf.2.1, hpost⟩

/-! ## 3. Placed `subroutine_ok` & `PlacedLib.subroutineOk` Corollaries -/

theorem compress256_cliExt_keepsFs_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {C : Crypto} (hF : C.F = sha256CompressState) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (keepsFs (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (CryptoVerification.SignalSession.CliExt.compress256Spec C)))) := by
  rw [keepsFs_withRoData]
  exact compress256_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_cliExt_keepsFs hF)

theorem compress256_cliExt_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {C : Crypto} (hF : C.F = sha256CompressState) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (CryptoVerification.SignalSession.CliExt.compress256Spec C))) :=
  compress256_placed_ro_ok hpl hext (by decide) (stackedMaster_simulates_cliExt hF)

theorem compress256_cliExt_subroutineOk {C : Crypto} (hF : C.F = sha256CompressState)
    (externs : String → Option (State → State) := fun _ => none) :
    compress256Lib.subroutineOk compress256Sym
      (fun pl => withRoData (pl.ρ sha2K32Sym) sha256KBytes
        (CryptoVerification.SignalSession.CliExt.compress256Spec C)) externs :=
  compress256_ro_subroutineOk (by decide) (stackedMaster_simulates_cliExt hF) externs

theorem compress256_hkdfExt_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (compress256ExternShaSpec sha256CompressState hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_hkdfExt hookStack)

theorem compress256_spqrExt_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (spqrCompress256ExternSpec sha256CompressState hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_spqrExt hookStack)

theorem compress256_tripleRatchet_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (withStack (CryptoVerification.LibsignalTripleRatchet.compress256Spec sha256CompressState) hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_tripleRatchet hookStack)

theorem compress256_budget_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (withStack (compress256BudgetSpec sha256CompressState) hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_budget hookStack)

theorem compress256_session2Budget_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (withStack (session2Compress256BudgetSpec sha256CompressState) hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_session2Budget hookStack)

theorem compress256_pkStackAt_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {pkStack : Nat} (sp_cur : BitVec 64) (hstack : 176 ≤ pkStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (session2Compress256PkStackSpecAt sha256CompressState pkStack sp_cur))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_pkStackAt pkStack sp_cur)

theorem compress256_pkStackX_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    (sp_cur : BitVec 64) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (session2Compress256PkStackSpecX sha256CompressState sp_cur))) :=
  compress256_pkStackAt_placed_ok hpl hext sp_cur (by decide)

theorem compress256_pkStack_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    (sp_cur : BitVec 64) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (session2Compress256PkStackSpecAt sha256CompressState publicKeySerializeStack sp_cur))) :=
  compress256_pkStackAt_placed_ok hpl hext sp_cur (by decide)

theorem compress256_pkStackBudgetAt_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {pkStack : Nat} (sp_cur : BitVec 64) (hstack : 176 ≤ pkStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (session2Compress256PkStackBudgetSpecAt sha256CompressState pkStack sp_cur))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_pkStackBudgetAt pkStack sp_cur)

theorem compress256_single_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (withStack (compress256SingleSpec sha256CompressState) hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_single hookStack)

theorem compress256_singleBudget_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (withStack (withVmPreserved (compress256SingleSpec sha256CompressState)) hookStack))) :=
  compress256_placed_ro_ok hpl hext hstack (stackedMaster_simulates_singleBudget hookStack)

theorem compress256_single_subroutineOk {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    compress256Lib.subroutineOk compress256Sym
      (fun pl => withRoData (pl.ρ sha2K32Sym) sha256KBytes
        (withStack (compress256SingleSpec sha256CompressState) hookStack)) externs :=
  compress256_ro_subroutineOk hstack (stackedMaster_simulates_single hookStack) externs

/-- Consumer 8 (`sessionCompress256ROBudgetSpec sha256CompressState hookStack`). -/
theorem stackedMasterRO_simulates_sessionROBudget (hookStack : Nat := 176) :
    FrameSimulates (compress256StackedMasterROSpec hookStack)
      (sessionCompress256ROBudgetSpec sha256CompressState hookStack) := by
  rintro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hpre
  refine ⟨(ro, stA, st, blkA, bs, n), hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [compress256StackedMasterROSpec] at hpost
  dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec]
  simp only [sepConj_assoc] at hpost ⊢
  rw [satisfies_pure_sepConj] at hpost ⊢
  obtain ⟨⟨hpf, hacp⟩, hmem⟩ := hpost
  refine ⟨⟨ProcessFieldsPreserved_toHeapVmPreserved hpf, hacp⟩, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨hpf.2.1, hmem⟩

theorem compress256_sessionROBudget_placed_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {P : Program}
    (hext : ∀ off : Nat, off < 7636 → P.externAt? (pl.base + BitVec.ofNat 64 off) = none)
    {hookStack : Nat} (hstack : 176 ≤ hookStack := by decide) :
    subroutine_ok P (compress256Lib.fnAddr pl compress256Sym)
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (sessionCompress256ROBudgetSpec sha256CompressState hookStack))) := by
  have hsim : SpecSimulates (compress256MasterROSpec (pl.ρ sha2K32Sym))
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes
        (sessionCompress256ROBudgetSpec sha256CompressState hookStack)) :=
    ((compress256MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K32Sym) hstack).trans
      ((stackedMasterRO_simulates_sessionROBudget hookStack).withRoDataSep
        (pl.ρ sha2K32Sym) sha256KBytes).toSpecSimulates).trans
      (SpecSimulates.withRoData_of_sep sha256KBytes_length_le)
  exact (StepsLift.SpecSimulates.withPlacedCodeLoaded hsim compress256Lib pl).subroutine_ok
    (compress256_master_ro_ok hpl hext)

theorem compress256_sessionROBudget_subroutineOk {hookStack : Nat}
    (hstack : 176 ≤ hookStack := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    compress256Lib.subroutineOk compress256Sym
      (fun pl => withRoData (pl.ρ sha2K32Sym) sha256KBytes
        (sessionCompress256ROBudgetSpec sha256CompressState hookStack)) externs := by
  refine StepsLift.SpecSimulates.placedSubroutineOk (fun pl => ?_)
    (compress256_master_ro_subroutineOk externs)
  exact ((compress256MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K32Sym) hstack).trans
    ((stackedMasterRO_simulates_sessionROBudget hookStack).withRoDataSep
      (pl.ρ sha2K32Sym) sha256KBytes).toSpecSimulates).trans
    (SpecSimulates.withRoData_of_sep sha256KBytes_length_le)

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256
