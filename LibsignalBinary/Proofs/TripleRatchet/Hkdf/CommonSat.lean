/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSegsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# `HookSat`-Parameterized HKDF Hook Bundles and Step Lemmas

Defines `HkdfPlacedHooksSat` (specifying `memset` via `HookSat H lsMemsetSym sessionMemsetRegionSpec`
replacing `some memsetHook`) and its `HookSatExactMemcpy H lsMemcpySym` sibling `HkdfPlacedHooksExactSat`
(with automatic `instance HkdfPlacedHooksSat.toExactSat`), along with `S2Frame` / `AgreesOn` framing
lemmas and `[LibsignalPlacement]` `RunsToFrom` hook-step rules.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoGames.HMAC (ShaState chunks64 hmacWith)
open CryptoGames.HKDF (Salt hkdfExpand hkdfExtract)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved ExpandMultiInfoGhost ExtractGhost FinalizeFixedGhost HkdfPlacedHooks
   NewFromSliceGhost RW RunsTo RunsToFrom TraceEq chunks64_single_foldl compress256Hook_eq
   hmacCoreAt hookMemset_eq_memsetHook hookMemset_region_trace_ok lsCompress256Sym lsMemcpySym
   lsMemsetSym ls_externAt?_of_mem memcpyHook_eq optSaltAt readShaState_of_shaStateBytes
   sessionMemsetRegionSpec shaStateBytes_length truncate8_truncate32)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (S2Frame disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap
   read8_eq_of_readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open VerifiedLibraries.Musl (memcpySrc)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_base_add lsRetAddr624_base_zero
   lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (hookOk_sessionMemcpyRegion_of_master hookOk_sessionMemcpy_of_master masterMemcpySpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact hookSatExactMemcpy_of_eq
   memcpyHook_exact s2_memcpy_step_placed_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (compress256Blocks sessionCompress256ROBudgetSpec sessionCompress256ROSpec
   sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemsetRegionBudgetSpec)

/-! ## `HkdfPlacedHooksSat` and Coercions -/

/-- `HookSat`-parameterized sibling of `HkdfPlacedHooks`: replaces the extensional equality
`H lsMemsetSym = some memsetHook` with `HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
public class HkdfPlacedHooksSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionSpec
  memcpy : H lsMemcpySym = some memcpyHook
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- `memsetHook` satisfies `sessionMemsetRegionSpec` (transferred from `hookMemset_region_trace_ok`
via `hookMemset_eq_memsetHook`). -/
public theorem memsetHook_region_trace_ok : HookOk memsetHook sessionMemsetRegionSpec :=
  hookMemset_eq_memsetHook ▸ hookMemset_region_trace_ok

public theorem hookSat_memsetHook_of_eq {H : LibsignalHooks}
    (h : H lsMemsetSym = some memsetHook) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec :=
  ⟨memsetHook, h, memsetHook_region_trace_ok⟩

public theorem hookSat_hookMemset_of_eq {H : LibsignalHooks}
    (h : H lsMemsetSym = some ProofLib.hookMemset) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec :=
  ⟨ProofLib.hookMemset, h, hookMemset_region_trace_ok⟩

public theorem HkdfPlacedHooks.toSat {F : ShaCompress} {H : LibsignalHooks}
    (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksSat F H where
  memset := hookSat_memsetHook_of_eq hH.memset
  memcpy := hH.memcpy
  compress256 := hH.compress256

public theorem hookSat_sessionMemsetRegion_of_budget {H : LibsignalHooks}
    (h : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) :
    HookSat H lsMemsetSym sessionMemsetRegionSpec := by
  obtain ⟨f, hfH, hfOk⟩ := h
  refine ⟨f, hfH, fun x R s0 hrun hpre hsp => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hfOk x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpost⟩ | ⟨he, hcc, hpost⟩ | ⟨ho, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemsetRegionBudgetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl ⟨hp, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨he, hcc, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hpost⟩))

public theorem HkdfPlacedHooksSat.of_budget {F : ShaCompress} {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksSat F H where
  memset := hookSat_sessionMemsetRegion_of_budget h_memset
  memcpy := h_memcpy
  compress256 := h_compress

private theorem writeBytes_perm_eq_early (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    ∀ a : BitVec 64, (m.writeBytes base bs).perm a = m.perm a := by
  induction bs generalizing m base with
  | nil => intro _; rfl
  | cons _ _ ih =>
    intro a
    dsimp only [Memory.writeBytes]
    rw [ih]
    dsimp only [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

/-- `compress256Hook F` satisfies `sessionCompress256ROBudgetSpec F stk` for any stack budget
`stk` and both `ro = true` (`↦ᵣ`) and `ro = false` (`↦ₛ`) block slices. -/
public theorem compress256Hook_roBudget_ok (F : ShaCompress) (stk : Nat := 176) :
    HookOk (compress256Hook F) (sessionCompress256ROBudgetSpec F stk) := by
  intro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hrun hpre _hsp
  dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len, hbs_le⟩, hmem⟩
  have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_length st
  have hst_bytes : s0.mem.readBytes stA 32 = shaStateBytes st := by
    have h := ((IsBlock.pointsToBytes_len (a := stA) hst_len).read
      (by rwa [sepConj_assoc] at hmem)).2
    simpa [hst_len] using h
  have hst : readShaState s0.mem stA = st :=
    readShaState_of_shaStateBytes s0.mem stA st hst_bytes
  have hmem_blk : s0.mem ⊨ compress256Blocks ro blkA bs ∗
      ((stA ↦ₛ shaStateBytes st) ∗ (stackAt s0.sp stk ∗ R)) := by
    ac_nf at hmem ⊢
  have hbs : s0.mem.readBytes blkA (64 * n) = bs := by
    rw [← hbs_len]
    cases ro
    · exact ((IsBlock.pointsToBytes blkA bs).read hmem_blk).2
    · exact (IsBlockRO.pointsToBytesRO blkA bs hbs_le).read hmem_blk
  let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
  have hout_len : outBytes.length = (shaStateBytes st).length := by
    simp only [outBytes, shaStateBytes_length]
  have hmem_reg : s0.mem ⊨ memRegion stA outBytes.length ∗
      (compress256Blocks ro blkA bs ∗ stackAt s0.sp stk ∗ R) := by
    rw [hout_len]
    have hmem_st : s0.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗
        (compress256Blocks ro blkA bs ∗ stackAt s0.sp stk ∗ R) := by
      ac_nf at hmem ⊢
    exact Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion stA _)) hmem_st
  have hlen32 : outBytes.length ≤ 2 ^ 64 := by
    simp only [outBytes, shaStateBytes_length]; decide
  have hf_eq : compress256Hook F s0 =
      returnToLinkRegister (s0.setMem (s0.mem.writeBytes stA outBytes)) := by
    simp only [compress256Hook, hx0, hx1, hx2, hst, hbs]; rfl
  have hkf : s0.mem.KeepsFrozen (compress256Hook F s0).mem := by
    rw [hf_eq]
    exact keepsFrozen_writeBytes_of_memRegion outBytes hlen32 hmem_reg
  have hsym : (compress256Hook F s0).symtab = s0.symtab := by rw [hf_eq]; rfl
  have hret : Returned s0 (compress256Hook F s0) := by rw [hf_eq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (compress256Hook F s0) := by
    rw [hf_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hvm : VmPreserved s0 (compress256Hook F s0) := by
    rw [hf_eq]
    have hp := writeBytes_perm_eq_early s0.mem stA outBytes
    cases s0
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩
  have hacp : AllocCallPreserved s0 (compress256Hook F s0) := by
    rw [hf_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hvm, hacp⟩, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨by rw [hf_eq]; rfl, ?_⟩
  rw [hf_eq]
  change (s0.mem.writeBytes stA outBytes) ⊨
    ((stA ↦ₛ outBytes) ∗ compress256Blocks ro blkA bs ∗ stackAt s0.sp stk) ∗ R
  have hwb := satisfies_writeBytes outBytes hlen32 hmem_reg
  ac_nf at hwb ⊢

/-- Discharge `HookSat H lsCompress256Sym (sessionCompress256ROBudgetSpec F stk)` from
`H lsCompress256Sym = some (compress256Hook F)`. -/
public theorem hookSat_compress256Hook_roBudget_of_eq {H : LibsignalHooks} {F : ShaCompress}
    {stk : Nat} (h : H lsCompress256Sym = some (compress256Hook F)) :
    HookSat H lsCompress256Sym (sessionCompress256ROBudgetSpec F stk) :=
  ⟨compress256Hook F, h, compress256Hook_roBudget_ok F stk⟩

/-- Executable-byte preservation (`read8`, `perm`, `isLazyFree`, `isAnon` at every `(m.perm a).x = true`
byte), ensuring `KeepsFrozen` commutes across `ProofLib.stripExecOutside` without W^X assumptions on
unowned frame memory. -/
@[expose] public def KeepsExec (m m' : Memory) : Prop :=
  ∀ a : BitVec 64, (m.perm a).x = true →
    m'.read8 a = m.read8 a ∧ m'.perm a = m.perm a ∧
    m'.isLazyFree a = m.isLazyFree a ∧ m'.isAnon a = m.isAnon a

/-- Narrow `spec.pre` with `⌜LsRetAddr624 (s.readReg64 .lr)⌝` (`rfl`-equal to
`HooksDehook.WithLsRet.withLsRet spec`). -/
@[expose] public def withLsRet624 [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsRetAddr624 (s.readReg64 .lr)⌝ ∗ spec.pre x s }

/-- Auto-discharge `LsRetAddr624 lr` at `libsignalSessionLib` `BL` call sites. -/
macro "prove_ls_ret624" : tactic =>
  `(tactic| first
    | (apply lsRetAddr624_blockPlacement_base_add <;> decide)
    | (apply lsRetAddr624_base_add <;> decide)
    | (apply lsRetAddr624_blockPlacement_base_zero <;> decide)
    | (apply lsRetAddr624_base_zero <;> decide)
    | assumption)

/-- Combined `withLsRet624 (sessionCompress256ROBudgetSpec F 176)` + `KeepsExec` contract for a
`compress256` hook `f`. -/
@[expose] public def HookOkCompress256 [LibsignalPlacement] (f : State → State)
    (F : ShaCompress) : Prop :=
  HookOk f (withLsRet624 (sessionCompress256ROBudgetSpec F 176)) ∧
    ∀ s : State, s.mem.RW (s.readReg64 .x0) 32 → KeepsExec s.mem (f s).mem

/-- `HookSat` bundle for `HookOkCompress256`. -/
@[expose] public def HookSatCompress256 [LibsignalPlacement] (H : String → Option (State → State))
    (name : String) (F : ShaCompress) : Prop :=
  ∃ f : State → State, H name = some f ∧ HookOkCompress256 f F

public theorem HookSatCompress256.toHookSat [LibsignalPlacement]
    {H : String → Option (State → State)} {name : String} {F : ShaCompress}
    (h : HookSatCompress256 H name F) :
    HookSat H name (withLsRet624 (sessionCompress256ROBudgetSpec F 176)) :=
  let ⟨f, hfH, hfOk, _⟩ := h
  ⟨f, hfH, hfOk⟩

public theorem hookSatCompress256_of_sym_eq [LibsignalPlacement]
    {H1 H2 : String → Option (State → State)}
    {sym : String} {F : ShaCompress} (heq : H1 sym = H2 sym) (h : HookSatCompress256 H2 sym F) :
    HookSatCompress256 H1 sym F :=
  let ⟨f, hf, hok⟩ := h
  ⟨f, heq.trans hf, hok⟩

private theorem writeBytes_cells_of_outside (m : Memory) :
    ∀ (base a : BitVec 64) (bs : List (BitVec 8)),
      bs.length ≤ (a - base).toNat →
      (m.writeBytes base bs).cells a = m.cells a := by
  intro base a bs
  induction bs generalizing m base with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hout
    have hne : a ≠ base := by
      intro rfl
      simp only [BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod, List.length_cons] at hout
      omega
    have hout' : bs.length ≤ (a - (base + 1#64)).toNat := by
      simp only [List.length_cons] at hout
      bv_omega
    dsimp only [Memory.writeBytes]
    rw [ih (m.write8 base b) (base + 1#64) hout']
    simp [Memory.write8, hne]

public theorem compress256Hook_keepsExec (F : ShaCompress) (s : State)
    (hrw : s.mem.RW (s.readReg64 .x0) 32) :
    KeepsExec s.mem (compress256Hook F s).mem := by
  intro a hx
  have hout : 32 ≤ (a - s.readReg64 .x0).toNat := by
    by_contra hlt
    have hin : InRegion (s.readReg64 .x0) 32 a := Nat.lt_of_not_ge hlt
    have hp := (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)).1
    rw [hp] at hx
    cases hx
  let outBytes := shaStateBytes
    ((chunks64 (s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat))).foldl
      F (readShaState s.mem (s.readReg64 .x0)))
  have hout_len : outBytes.length ≤ (a - s.readReg64 .x0).toNat := by
    rwa [shaStateBytes_length]
  have hcells : (compress256Hook F s).mem.cells a = s.mem.cells a := by
    change (s.mem.writeBytes (s.readReg64 .x0) outBytes).cells a = s.mem.cells a
    exact writeBytes_cells_of_outside s.mem (s.readReg64 .x0) a outBytes hout_len
  exact ⟨by simp [Memory.read8, hcells], by simp [Memory.perm, hcells],
    by simp [Memory.isLazyFree, hcells], by simp [Memory.isAnon, hcells]⟩

/-- Lift `HookOk f spec` to `HookOk f (withLsRet624 spec)`. -/
public theorem hookOk_withLsRet624 [LibsignalPlacement] {α : Type} {f : State → State}
    {spec : Spec α} (hf : HookOk f spec) : HookOk f (withLsRet624 spec) := by
  intro x R s0 hrun hpre hsp
  dsimp only [withLsRet624] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hf x R s0 hrun hpre.2 hsp

/-- `compress256Hook F` satisfies `HookOkCompress256`. -/
public theorem compress256Hook_okCompress256 [LibsignalPlacement] (F : ShaCompress) :
    HookOkCompress256 (compress256Hook F) F :=
  ⟨hookOk_withLsRet624 (compress256Hook_roBudget_ok F 176), compress256Hook_keepsExec F⟩

/-- Discharge `HookSatCompress256 H sym F` from `H sym = some (compress256Hook F)`. -/
public theorem hookSatCompress256_of_eq [LibsignalPlacement] {H : String → Option (State → State)}
    {sym : String} {F : ShaCompress} (h : H sym = some (compress256Hook F)) :
    HookSatCompress256 H sym F :=
  ⟨compress256Hook F, h, compress256Hook_okCompress256 F⟩

/-- `HookSatExactMemcpy` + `HookSatCompress256`-widened sibling of
`HkdfPlacedHooksSat`: relaxes `memcpy : H lsMemcpySym = some memcpyHook` to
`memcpy : HookSatExactMemcpy H lsMemcpySym` and
`compress256 : H lsCompress256Sym = some (compress256Hook F)` to
`compress256 : HookSatCompress256 H lsCompress256Sym F`. -/
public class HkdfPlacedHooksExactSat [LibsignalPlacement] (F : ShaCompress)
    (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym sessionMemsetRegionSpec
  memcpy : HookSatExactMemcpy H lsMemcpySym
  compress256 : HookSatCompress256 H lsCompress256Sym F

/-- Discharge `HookSatExactMemcpy H lsMemcpySym` from `H lsMemcpySym = some memcpyHook`. -/
public theorem hookSat_memcpyHook_exact_of_eq {H : LibsignalHooks}
    (h : H lsMemcpySym = some memcpyHook) :
    HookSatExactMemcpy H lsMemcpySym :=
  hookSatExactMemcpy_of_eq h memcpyHook_exact

/-- Discharge `HookSatExactMemcpy H lsMemcpySym` from `H lsMemcpySym = some ProofLib.hookMemcpy`. -/
public theorem hookSat_hookMemcpy_exact_of_eq {H : LibsignalHooks}
    (h : H lsMemcpySym = some ProofLib.hookMemcpy) :
    HookSatExactMemcpy H lsMemcpySym :=
  hookSatExactMemcpy_of_eq h hookMemcpy_exact

/-- Automatic widening instance from `HkdfPlacedHooksSat F H` to `HkdfPlacedHooksExactSat F H`
via `hookSatExactMemcpy_of_eq` + `memcpyHook_exact` + `hookSatCompress256_of_eq`,
so callers holding `[HkdfPlacedHooksSat F H]` transparently satisfy
`[HkdfPlacedHooksExactSat F H]` as downstream modules migrate. -/
public instance HkdfPlacedHooksSat.toExactSat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksSat F H] : HkdfPlacedHooksExactSat F H where
  memset := hH.memset
  memcpy := hookSatExactMemcpy_of_eq hH.memcpy memcpyHook_exact
  compress256 := hookSatCompress256_of_eq hH.compress256

/-- Direct coercion from `HkdfPlacedHooks F H` to `HkdfPlacedHooksExactSat F H`. -/
public theorem HkdfPlacedHooks.toExactSat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (hH : HkdfPlacedHooks F H) : HkdfPlacedHooksExactSat F H :=
  have _ : HkdfPlacedHooksSat F H := HkdfPlacedHooks.toSat hH
  inferInstance

/-- Construct `HkdfPlacedHooksExactSat F H` from a budget-strengthened `memset` `HookSat`
contract, `HookSatExactMemcpy H lsMemcpySym`, and `HookSatCompress256 H lsCompress256Sym F`. -/
public theorem HkdfPlacedHooksExactSat.of_roBudget [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : HookSatCompress256 H lsCompress256Sym F) :
    HkdfPlacedHooksExactSat F H where
  memset := hookSat_sessionMemsetRegion_of_budget h_memset
  memcpy := h_memcpy
  compress256 := h_compress

/-- Construct `HkdfPlacedHooksExactSat F H` from a budget-strengthened `memset` `HookSat`
contract, `HookSatExactMemcpy H lsMemcpySym`, and `H lsCompress256Sym = some (compress256Hook F)`. -/
public theorem HkdfPlacedHooksExactSat.of_budget [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks}
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    HkdfPlacedHooksExactSat F H :=
  HkdfPlacedHooksExactSat.of_roBudget h_memset h_memcpy
    (hookSatCompress256_of_eq h_compress)

/-! ## `CallingConventionPreserved` and `S2Frame` Helpers -/

public theorem CallingConventionPreserved.x23 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x23 = s.readReg64 .x23 :=
  h.2.2.2.2.2.1

public theorem CallingConventionPreserved.x24 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x24 = s.readReg64 .x24 :=
  h.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x25 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x25 = s.readReg64 .x25 :=
  h.2.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x26 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x26 = s.readReg64 .x26 :=
  h.2.2.2.2.2.2.2.2.1

public theorem CallingConventionPreserved.x28 {s s' : State}
    (h : CallingConventionPreserved s s') : s'.readReg64 .x28 = s.readReg64 .x28 :=
  h.2.2.2.2.2.2.2.2.2.2.1

private theorem isBlock_one_none_outside {P : SepProp} {b : BitVec 64} {n : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P b n Φ) {h : Heap} (hp : P h)
    {a : BitVec 64} (ha : OutsideRegion b n a) :
    h.phys a = none := by
  obtain ⟨m1, -, rfl⟩ := (hb.iff h).mp hp
  have hn : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  change (regionHeap b n m1).phys a = none
  simp [regionHeap, hn]

private theorem isBlock_one_mapped_false {P : SepProp} {b : BitVec 64} {n : Nat}
    {Φ : Memory → Prop} (hb : IsBlock P b n Φ) {h : Heap} (hp : P h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨m1, -, rfl⟩ := (hb.iff h).mp hp
  simp [regionHeap]

/-- One-block analogue of `HkdfExt.isBlock_three_all_s2frame`: a hook transition transforming
`P` to `P'` on `[b, b + n)` while preserving `fullComplementHeap hP m` establishes
`S2Frame m m' [(b, n)]`. -/
public theorem isBlock_one_s2frame {P P' R' : SepProp} {b : BitVec 64} {n : Nat}
    {Φ Φ' : Memory → Prop}
    (hb : IsBlock P b n Φ) (hb' : IsBlock P' b n Φ')
    {hP : Heap} {m m' : Memory}
    (hpP : P hP) (hmP : hP.Matches m)
    (hpost : m' ⊨ P' ∗ R')
    (hmc : (fullComplementHeap hP m).Matches m') :
    S2Frame m m' [(b, n)] := by
  unfold Heap.Matches at hmc hmP
  have hmc_phys := hmc.1
  have hmc_map := hmc.2.2
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion b n a := ha (b, n) (by simp)
    have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc_phys a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc_phys a _ hca).1
  · by_cases hin : InRegion b n a
    · exact hb'.permNoLazy_rw hpost hin
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
      have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      obtain ⟨-, hp', hlf'⟩ := hmc_phys a _ hca
      exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin : InRegion b n a
    · exact hb'.perm_rw hpost hin
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      by_cases hlf_a : m.isLazyFree a = true
      · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        exact hmc_phys a .lazy hca
      · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_f]
        exact (hmc_phys a _ hca).2.1
  · have hm0 : hP.mapped a = false := isBlock_one_mapped_false hb hpP a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : hP.phys a = none := by
      obtain ⟨m1, -, rfl⟩ := (hb.iff hP).mp hpP
      cases ha : (regionHeap b n m1).phys a with
      | none => rfl
      | some c =>
        have hperm := hmP.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b n a <;> simp [regionHeap, h1] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b n a <;> simp [regionHeap, h1] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap hP m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc_phys a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap hP m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc_phys a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩
  · by_cases hin : InRegion b n a
    · exact ⟨by rw [hb'.perm_rw hpost hin]; rfl, hb'.isLazyFree_false hpost hin⟩
    · have ha1 : OutsideRegion b n a := (outsideRegion_iff_not_inRegion b n a).mpr hin
      have hnone : hP.phys a = none := isBlock_one_none_outside hb hpP ha1
      by_cases hrw_a : m.perm a = some Perm.rw
      · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc_phys a _ hca
        exact ⟨by rw [hp']; rfl, hlf'⟩
      · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
        obtain ⟨-, hr', hlf'⟩ := hmc_phys a _ hca
        exact ⟨hr', hlf'⟩

/-- If `m'` modifies only `(dst, bs.length)` relative to `m` via `S2Frame` and
`m'.readBytes dst bs.length = bs`, then `m'` agrees byte-for-byte with `m.writeBytes dst bs`
on every readable non-lazy address of `m`. -/
public theorem agreesOn_readable_of_s2Frame_writeBytes {m m' : Memory}
    {dst : BitVec 64} {bs : List (BitVec 8)}
    (hdst : m'.readBytes dst bs.length = bs)
    (hframe : S2Frame m m' [(dst, bs.length)])
    (hlen : bs.length ≤ 2 ^ 64) :
    AgreesOn (fun a => (m.perm a).r = true ∧ m.isLazyFree a = false)
      m' (m.writeBytes dst bs) := by
  intro a ⟨hr, hlf⟩
  by_cases hin : InRegion dst bs.length a
  · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset dst bs.length a hlen).mp hin
    have hwb : (m.writeBytes dst bs).readBytes dst bs.length = bs :=
      Memory.readBytes_writeBytes_same m dst bs hlen
    exact read8_eq_of_readBytes_eq (hdst.trans hwb.symm) hi
  · have hout : OutsideRegion dst bs.length a :=
      (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin
    have h1 : m'.read8 a = m.read8 a :=
      hframe.1 a hr hlf fun r hr_mem => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
        subst hr_mem; exact hout
    have h2 : (m.writeBytes dst bs).read8 a = m.read8 a :=
      (ProofLib.AgreesOutside.writeBytes_self m dst bs).1 a hout
    exact h1.trans h2.symm

/-- Execute a `HookOk f sessionMemsetRegionSpec` hook on a state `s` with `s.mem.RW dst len`,
yielding `Returned`, `CallingConventionPreserved`, `readBytes dst len = List.replicate len val`,
`S2Frame s.mem (f s).mem [(dst, len)]`, and `AgreesOn` with `s.mem.writeBytes dst (List.replicate len val)`. -/
public theorem hookOk_sessionMemsetRegion_elim {f : State → State}
    (hf : HookOk f sessionMemsetRegionSpec)
    {s : State} {dst : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len) :
    let s' := f s
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    s'.readReg64 .x0 = dst ∧
    s'.trace = s.trace ∧
    s'.mem.readBytes dst len = List.replicate len val ∧
    S2Frame s.mem s'.mem [(dst, len)] ∧
    AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
      s'.mem (s.mem.writeBytes dst (List.replicate len val)) := by
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hb_pre := IsBlock.memRegion dst len
  let hP : Heap := regionHeap dst len s.mem
  have hpP : (memRegion dst len) hP := (hb_pre.iff hP).mpr ⟨s.mem, trivial, rfl⟩
  have hmP : hP.Matches s.mem := IsBlock.regionHeap_matches dst len s.mem hrw
  let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
  have hsep_pre : s.mem ⊨ memRegion dst len ∗ R_comp :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx1_32 : (s.readReg32 .x1).truncate 8 = val := by
    rw [State.readReg32, truncate8_truncate32, hx1]
  have hpre_full : s.mem ⊨ sessionMemsetRegionSpec.pre (dst, val, len) s ∗ R_comp := by
    dsimp only [sessionMemsetRegionSpec, memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_32, hx2, hlen_le⟩, hsep_pre⟩
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  obtain ⟨hkf, hsym, hout⟩ := hf (dst, val, len) R_comp s hrun hpre_full hsp_aligned
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [sessionMemsetRegionSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hx0', htr'⟩, hsep_post⟩ := hpost
    have hrep_len : (List.replicate len val).length = len := List.length_replicate
    have hb_post := IsBlock.pointsToBytes_len (a := dst) hrep_len
    have hread_post : (f s).mem.readBytes dst len = List.replicate len val := by
      have h := (hb_post.read hsep_post).2
      rwa [hrep_len] at h
    have hpost_R : (f s).mem ⊨ R_comp ∗ (dst ↦ₛ List.replicate len val) := by
      ac_nf at hsep_post ⊢
    have hm_post : (fullComplementHeap hP s.mem).Matches (f s).mem := by
      obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
      cases hR_hc'
      exact Heap.Matches.of_union_left hmatch
    have hs2 : S2Frame s.mem (f s).mem [(dst, len)] :=
      isBlock_one_s2frame hb_pre hb_post hpP hmP hsep_post hm_post
    have hread_rep : (f s).mem.readBytes dst (List.replicate len val).length =
        List.replicate len val := by rwa [hrep_len]
    have hs2_rep : S2Frame s.mem (f s).mem [(dst, (List.replicate len val).length)] := by
      rwa [hrep_len]
    have hag : AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        (f s).mem (s.mem.writeBytes dst (List.replicate len val)) :=
      agreesOn_readable_of_s2Frame_writeBytes hread_rep hs2_rep (by rw [hrep_len]; exact hlen_le)
    exact ⟨hkf, hsym, hret, hcc, hx0', htr', hread_post, hs2, hag⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## Placed `RunsToFrom` Step Lemmas -/

/-- Step through `memset` at `lsρ lsMemsetSym` in any placed block program `prog` using
`HookSat H lsMemsetSym sessionMemsetRegionSpec`. -/
public theorem s2_memset_step_placed_of_hookSat [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len val →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len val)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  obtain ⟨f, hfH, hfOk⟩ := h_memset
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hx0', htr', hread', hs2', hag'⟩ :=
    hookOk_sessionMemsetRegion_elim hfOk hrun hx0 hx1 hx2 hsp_al hrw
  have htr_f : TraceEq s (f s) := ⟨htr', hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hpc' : (f s).pc = lr := hret.1.trans hlr
  exact RunsTo.hook hrun hhook hkf hsym
    (h (f s) (TraceEq.trans htr_f htr_s) hpc' hret.2.2 hcc hx0' hkf hread' hs2' hag')

public theorem s2_memset_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memset_step_placed_of_hookSat hH.memset hrun hpc hx0 hx1 hx2 hlr hsp_al hrw h htr_s hi hunmut

public theorem s2_compress256_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.compress256]
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

public theorem s2_memcpy_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memcpyHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.memcpy]
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## 4. Placed `RunsToFrom` Step Lemmas under `HookSatExactMemcpy` / `HkdfPlacedHooksExactSat` -/

/-- Step through `memcpy` at `lsρ lsMemcpySym` in any placed block program `prog` using
`HookSatExactMemcpy H lsMemcpySym` (in the `∀ c : MemcpyClobber` shape with exact memory
`s.mem.writeBytes dst bs`). -/
public theorem s2_memcpy_step_placed_of_hookSatExact [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hsp : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  exact s2_memcpy_step_placed_of_exact H h_memcpy hrun hsp hpc hx0 hx1 hx2 hlr
    hread hrw hreadable hdisj h hi hunmut

/-- `[HkdfPlacedHooksExactSat C.F H]` wrapper for `s2_memcpy_step_placed_of_hookSatExact`. -/
public theorem s2_memcpy_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memcpy_step_placed_of_hookSatExact hH.memcpy hrun hpc hx0 hx1 hx2 hlr hsp_al
    hread hrw hreadable hdisj h hi hunmut

/-- `[HkdfPlacedHooksExactSat C.F H]` wrapper for `s2_memset_step_placed_of_hookSat` (`val = 0#8`). -/
public theorem s2_memset_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.readReg64 .x0 = dst →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q :=
  s2_memset_step_placed_of_hookSat hH.memset hrun hpc hx0 hx1 hx2 hlr hsp_al hrw h htr_s hi hunmut

private theorem not_both_inRegion_of_disj {b1 b2 x : BitVec 64} {n1 n2 : Nat}
    (hn2 : n2 ≤ 2 ^ 64) (hdisj : n2 = 0 ∨ DisjointRegions b1 n1 b2 n2)
    (hx1 : InRegion b1 n1 x) (hx2 : InRegion b2 n2 x) : False := by
  rcases hdisj with rfl | hd
  · exact Nat.not_lt_zero _ hx2
  · have hout := hd.outside hx2 hn2
    exact (outsideRegion_iff_not_inRegion b1 n1 x).mp hout hx1

/-- Execute a `HookOk f (sessionCompress256ROBudgetSpec F 176)` hook on a state `s` with
`s.mem.RW stA 32`, `s.mem.RW (s.sp - 176#64) 176`, and `s.mem.Readable blkA (64 * n)` (supporting
`.ro`, `.rw`, and mixed `.ro`/`.rw` block slices via `ro = true` + `VmPreserved`), yielding
`Returned`, `CallingConventionPreserved`, `VmPreserved`, `AllocCallPreserved`,
`readBytes stA 32 = shaStateBytes ((chunks64 bs).foldl F st)`,
`S2Frame s.mem (f s).mem [(stA, 32), (s.sp - 176#64, 176)]`, and `AgreesOn` with
`s.mem.writeBytes stA (shaStateBytes ((chunks64 bs).foldl F st))` outside `[s.sp - 176#64, 176)`. -/
private theorem hookOk_sessionCompress256ROBudget_elim_at {F : ShaCompress} {f : State → State}
    {s : State}
    (hf : ∀ x R, s.status = .Running →
      (s.mem ⊨ (sessionCompress256ROBudgetSpec F 176).pre x s ∗ R) →
      s.spAligned = true →
      s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab ∧
        SubroutineOutcome (sessionCompress256ROBudgetSpec F 176) x R s (f s))
    {stA blkA : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stA)
    (hx1 : s.readReg64 .x1 = blkA)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stA 32 = shaStateBytes st)
    (hbs : s.mem.readBytes blkA (64 * n) = bs)
    (hrw_st : s.mem.RW stA 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkA (64 * n))
    (hdisj_st_stk : DisjointRegions stA 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stA 32 blkA (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkA (64 * n))
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega) :
    let s' := f s
    let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    VmPreserved s s' ∧
    AllocCallPreserved s s' ∧
    s'.trace = s.trace ∧
    s'.mem.readBytes stA 32 = outBytes ∧
    S2Frame s.mem s'.mem [(stA, 32), (s.sp - 176#64, 176)] ∧
    AgreesOn
      (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
        OutsideRegion (s.sp - 176#64) 176 a)
      s'.mem (s.mem.writeBytes stA outBytes) := by
  have hbs_len : bs.length = 64 * n := by rw [← hbs, Memory.readBytes_length]
  have hbs_le : bs.length ≤ 2 ^ 64 := hbs_len ▸ hn_le
  have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_length st
  let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
  have hout_len : outBytes.length = 32 := shaStateBytes_length _
  have hb_st := IsBlock.pointsToBytes_len (a := stA) hst_len
  have hb_out := IsBlock.pointsToBytes_len (a := stA) hout_len
  have hb_blk := IsBlockRO.pointsToBytesRO blkA bs hbs_le
  have hb_stk := IsBlock.memRegion (s.sp - 176#64) 176
  let h_st : Heap := regionHeap stA 32 s.mem
  let h_blk : Heap := regionHeapRO blkA bs.length s.mem
  let h_stk : Heap := regionHeap (s.sp - 176#64) 176 s.mem
  have hp_st : (stA ↦ₛ shaStateBytes st) h_st :=
    (hb_st.iff h_st).mpr ⟨s.mem, ⟨by rw [hst_len]; decide, by rwa [hst_len]⟩, rfl⟩
  have hp_blk : (blkA ↦ᵣ bs) h_blk :=
    (hb_blk.iff h_blk).mpr ⟨s.mem, hbs_len.symm ▸ hbs, rfl⟩
  have hp_stk : (stackAt s.sp 176) h_stk := (hb_stk.iff h_stk).mpr ⟨s.mem, trivial, rfl⟩
  have hm_st : h_st.Matches s.mem := IsBlock.regionHeap_matches stA 32 s.mem hrw_st
  have hm_blk : h_blk.Matches s.mem :=
    IsBlockRO.regionHeapRO_matches blkA bs.length s.mem (hbs_len.symm ▸ hread_blk)
  have hm_stk : h_stk.Matches s.mem := IsBlock.regionHeap_matches (s.sp - 176#64) 176 s.mem hrw_stk
  have hd_blk_stk : h_blk.Disjoint h_stk := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h_blk, regionHeapRO])
      (hf := by simp [h_blk, regionHeapRO]) (hm := by simp [h_blk, regionHeapRO]) fun x => ?_
    by_cases hxs : InRegion (s.sp - 176#64) 176 x
    · have hnb : ¬ InRegion blkA bs.length x := fun hxb => by
        rw [hbs_len] at hxb
        exact not_both_inRegion_of_disj hn_le (hdisj_stk_blk.imp (by omega) id) hxs hxb
      exact Or.inl (by simp [h_blk, regionHeapRO, hnb])
    · exact Or.inr (Or.inl (by simp [h_stk, regionHeap, hxs]))
  have hd_st_blk : h_st.Disjoint h_blk := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h_st, regionHeap])
      (hf := by simp [h_st, regionHeap]) (hm := by simp [h_st, regionHeap]) fun x => ?_
    by_cases hxs : InRegion stA 32 x
    · have hnb : ¬ InRegion blkA bs.length x := fun hxb => by
        rw [hbs_len] at hxb
        exact not_both_inRegion_of_disj hn_le (hdisj_st_blk.imp (by omega) id) hxs hxb
      exact Or.inr (Or.inl (by simp [h_blk, regionHeapRO, hnb]))
    · exact Or.inl (by simp [h_st, regionHeap, hxs])
  have hd_st_stk : h_st.Disjoint h_stk := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h_st, regionHeap])
      (hf := by simp [h_st, regionHeap]) (hm := by simp [h_st, regionHeap]) fun x => ?_
    by_cases hxs : InRegion (s.sp - 176#64) 176 x
    · have hnb : ¬ InRegion stA 32 x :=
        (outsideRegion_iff_not_inRegion stA 32 x).mp (hdisj_st_stk.outside hxs (by decide))
      exact Or.inl (by simp [h_st, regionHeap, hnb])
    · exact Or.inr (Or.inl (by simp [h_stk, regionHeap, hxs]))
  have hd_st_bs : h_st.Disjoint (h_blk.union h_stk) :=
    (Heap.disjoint_union_right hd_blk_stk).mpr ⟨hd_st_blk, hd_st_stk⟩
  let hP : Heap := h_st.union (h_blk.union h_stk)
  have hpP : ((stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ᵣ bs) ∗ stackAt s.sp 176) hP :=
    SepProp.holds_sepConj_intro hd_st_bs hp_st
      (SepProp.holds_sepConj_intro hd_blk_stk hp_blk hp_stk)
  have hmP : hP.Matches s.mem :=
    Heap.Matches.union hm_st (Heap.Matches.union hm_blk hm_stk)
  let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
  have hsep_pre : s.mem ⊨
      ((stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ᵣ bs) ∗ stackAt s.sp 176) ∗ R_comp :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_full : s.mem ⊨
      (sessionCompress256ROBudgetSpec F 176).pre (true, stA, st, blkA, bs, n) s ∗ R_comp := by
    dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec, compress256Blocks, cond]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hbs_len, hbs_le⟩, by ac_nf at hsep_pre ⊢⟩
  have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
  obtain ⟨hkf, hsym, hout⟩ :=
    hf (true, stA, st, blkA, bs, n) R_comp hrun hpre_full hsp_aligned
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec,
      compress256Blocks, cond] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hvm, hacp⟩, hpost2⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨htr', hsep_post⟩ := hpost2
    have hpost_st : (f s).mem ⊨
        (stA ↦ₛ outBytes) ∗ ((blkA ↦ᵣ bs) ∗ stackAt s.sp 176 ∗ R_comp) := by
      ac_nf at hsep_post ⊢
    have hread_st' : (f s).mem.readBytes stA 32 = outBytes := by
      have h := (hb_out.read hpost_st).2
      rwa [hout_len] at h
    have hpost_stk : (f s).mem ⊨
        stackAt s.sp 176 ∗ ((stA ↦ₛ outBytes) ∗ (blkA ↦ᵣ bs) ∗ R_comp) := by
      ac_nf at hsep_post ⊢
    have hpost_blk : (f s).mem ⊨
        (blkA ↦ᵣ bs) ∗ ((stA ↦ₛ outBytes) ∗ stackAt s.sp 176 ∗ R_comp) := by
      ac_nf at hsep_post ⊢
    have hread_blk' : (f s).mem.readBytes blkA (64 * n) = bs := by
      have h := hb_blk.read hpost_blk
      rwa [hbs_len] at h
    have hlf_blk' : ∀ a, InRegion blkA (64 * n) a → (f s).mem.isLazyFree a = false := by
      intro a hin
      obtain ⟨h1, _, _, hp1, _, hm1⟩ := Satisfies.sepConj_elim hpost_blk
      obtain ⟨m0, _, rfl⟩ := (hb_blk.iff h1).mp hp1
      have hin' : InRegion blkA bs.length a := hbs_len ▸ hin
      have hm1_l := Heap.Matches.of_union_left hm1
      unfold Heap.Matches at hm1_l
      exact (hm1_l.1 a (.ro (m0.read8 a)) (by simp [regionHeapRO, hin'])).2.2
    have hpost_R : (f s).mem ⊨
        R_comp ∗ ((stA ↦ₛ outBytes) ∗ (blkA ↦ᵣ bs) ∗ stackAt s.sp 176) := by
      ac_nf at hsep_post ⊢
    have hm_post : (fullComplementHeap hP s.mem).Matches (f s).mem := by
      obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
      cases hR_hc'
      exact Heap.Matches.of_union_left hmatch
    have hP_mapped : ∀ a, hP.mapped a = false := by
      intro a
      simp [hP, h_st, h_blk, h_stk, Heap.union, regionHeap, regionHeapRO]
    have hP_none : ∀ a, ¬ InRegion stA 32 a → ¬ InRegion (s.sp - 176#64) 176 a →
        ¬ InRegion blkA (64 * n) a → hP.phys a = none := by
      intro a hn1 hn2 hn3
      have hn3' : ¬ InRegion blkA bs.length a := hbs_len ▸ hn3
      simp [hP, h_st, h_blk, h_stk, Heap.union, regionHeap, regionHeapRO, hn1, hn2, hn3']
    have hperm_eq := hvm.perm_eq
    have hs2 : S2Frame s.mem (f s).mem [(stA, 32), (s.sp - 176#64, 176)] := by
      unfold Heap.Matches at hm_post
      have hmc_phys := hm_post.1
      have hmc_map := hm_post.2.2
      refine ⟨fun a hr_a hlf_a ha => ?_,
        ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
         ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a ha => ?_⟩⟩,
        fun a hr_a hlf_a => ?_⟩
      · have hn_st : ¬ InRegion stA 32 a :=
          (outsideRegion_iff_not_inRegion stA 32 a).mp (ha (stA, 32) (by simp))
        have hn_stk : ¬ InRegion (s.sp - 176#64) 176 a :=
          (outsideRegion_iff_not_inRegion (s.sp - 176#64) 176 a).mp
            (ha (s.sp - 176#64, 176) (by simp))
        by_cases hin_blk : InRegion blkA (64 * n) a
        · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset blkA (64 * n) a hn_le).mp hin_blk
          exact read8_eq_of_readBytes_eq (hread_blk'.trans hbs.symm) hi
        · have hnone := hP_none a hn_st hn_stk hin_blk
          by_cases hrw_a : s.mem.perm a = some Perm.rw
          · exact (hmc_phys a (.rw (s.mem.read8 a))
              (by simp [fullComplementHeap, hnone, hrw_a, hlf_a])).1
          · exact (hmc_phys a (.ro (s.mem.read8 a))
              (by simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a])).1
      · by_cases hin_st : InRegion stA 32 a
        · exact hb_out.permNoLazy_rw hpost_st hin_st
        · by_cases hin_stk : InRegion (s.sp - 176#64) 176 a
          · exact hb_stk.permNoLazy_rw hpost_stk hin_stk
          · obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
            by_cases hin_blk : InRegion blkA (64 * n) a
            · exact Memory.permNoLazy_eq_some_rw_iff.mpr
                ⟨(hperm_eq a).trans hrw_a, hlf_blk' a hin_blk⟩
            · have hnone := hP_none a hin_st hin_stk hin_blk
              obtain ⟨-, hp', hlf'⟩ :=
                hmc_phys a (.rw (s.mem.read8 a))
                  (by simp [fullComplementHeap, hnone, hrw_a, hlf_a])
              exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
      · exact (hperm_eq a).trans hrw_a
      · exact hmc_map a (by simp [fullComplementHeap, hP_mapped a, hm_a, han_a])
      · have hn_st : ¬ InRegion stA 32 a :=
          (outsideRegion_iff_not_inRegion stA 32 a).mp (ha (stA, 32) (by simp))
        have hn_stk : ¬ InRegion (s.sp - 176#64) 176 a :=
          (outsideRegion_iff_not_inRegion (s.sp - 176#64) 176 a).mp
            (ha (s.sp - 176#64, 176) (by simp))
        have hn_blk : ¬ InRegion blkA (64 * n) a := by
          intro hin_blk
          have hr := (hread_blk a hin_blk).1
          rw [hpn_a] at hr; cases hr
        have hnone := hP_none a hn_st hn_stk hn_blk
        refine ⟨(hperm_eq a).trans hpn_a, fun hlf_a => ?_⟩
        have hpn_cell : (fullComplementHeap hP s.mem).phys a = some (.protNone (s.mem.read8 a)) := by
          dsimp only [fullComplementHeap]
          rw [hnone, hpn_a, hlf_a]
          rfl
        obtain ⟨hb_eq, -, hlf'⟩ := hmc_phys a (.protNone (s.mem.read8 a)) hpn_cell
        exact ⟨hb_eq, hlf'⟩
      · refine ⟨by rw [hperm_eq a]; exact hr_a, ?_⟩
        by_cases hin_st : InRegion stA 32 a
        · exact (Memory.permNoLazy_eq_some_rw_iff.mp (hb_out.permNoLazy_rw hpost_st hin_st)).2
        · by_cases hin_stk : InRegion (s.sp - 176#64) 176 a
          · exact (Memory.permNoLazy_eq_some_rw_iff.mp (hb_stk.permNoLazy_rw hpost_stk hin_stk)).2
          · by_cases hin_blk : InRegion blkA (64 * n) a
            · exact hlf_blk' a hin_blk
            · have hnone := hP_none a hin_st hin_stk hin_blk
              by_cases hrw_a : s.mem.perm a = some Perm.rw
              · exact (hmc_phys a (.rw (s.mem.read8 a))
                  (by simp [fullComplementHeap, hnone, hrw_a, hlf_a])).2.2
              · exact (hmc_phys a (.ro (s.mem.read8 a))
                  (by simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a])).2.2
    have hag : AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        (f s).mem (s.mem.writeBytes stA outBytes) := by
      intro a ⟨hr_a, hlf_a, hout_stk⟩
      by_cases hin_st : InRegion stA 32 a
      · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset stA 32 a (by decide)).mp hin_st
        have hwb : (s.mem.writeBytes stA outBytes).readBytes stA 32 = outBytes := by
          have h := Memory.readBytes_writeBytes_same s.mem stA outBytes (by rw [hout_len]; decide)
          rwa [hout_len] at h
        exact read8_eq_of_readBytes_eq (hread_st'.trans hwb.symm) hi
      · have hout_st : OutsideRegion stA 32 a :=
          (outsideRegion_iff_not_inRegion stA 32 a).mpr hin_st
        have h1 : (f s).mem.read8 a = s.mem.read8 a :=
          hs2.1 a hr_a hlf_a fun r hr_mem => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
            rcases hr_mem with rfl | rfl
            · exact hout_st
            · exact hout_stk
        have h2 : (s.mem.writeBytes stA outBytes).read8 a = s.mem.read8 a :=
          (ProofLib.AgreesOutside.writeBytes_self s.mem stA outBytes).1 a
            (by rwa [hout_len])
        exact h1.trans h2.symm
    exact ⟨hkf, hsym, hret, hcc, hvm, hacp, htr', hread_st', hs2, hag⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

public theorem hookOk_sessionCompress256ROBudget_elim {F : ShaCompress} {f : State → State}
    (hf : HookOk f (sessionCompress256ROBudgetSpec F 176))
    {s : State} {stA blkA : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stA)
    (hx1 : s.readReg64 .x1 = blkA)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stA 32 = shaStateBytes st)
    (hbs : s.mem.readBytes blkA (64 * n) = bs)
    (hrw_st : s.mem.RW stA 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkA (64 * n))
    (hdisj_st_stk : DisjointRegions stA 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stA 32 blkA (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkA (64 * n))
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega) :
    let s' := f s
    let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    VmPreserved s s' ∧
    AllocCallPreserved s s' ∧
    s'.trace = s.trace ∧
    s'.mem.readBytes stA 32 = outBytes ∧
    S2Frame s.mem s'.mem [(stA, 32), (s.sp - 176#64, 176)] ∧
    AgreesOn
      (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
        OutsideRegion (s.sp - 176#64) 176 a)
      s'.mem (s.mem.writeBytes stA outBytes) :=
  hookOk_sessionCompress256ROBudget_elim_at (fun x R => hf x R s)
    hrun hx0 hx1 hx2 hsp_al hst hbs hrw_st hrw_stk hread_blk
    hdisj_st_stk hdisj_st_blk hdisj_stk_blk hn_le

public theorem hookOk_withLsRet624_sessionCompress256ROBudget_elim [LibsignalPlacement]
    {F : ShaCompress} {f : State → State}
    (hf : HookOk f (withLsRet624 (sessionCompress256ROBudgetSpec F 176)))
    {s : State} {stA blkA : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hlr_ls : LsRetAddr624 (s.readReg64 .lr))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = stA)
    (hx1 : s.readReg64 .x1 = blkA)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stA 32 = shaStateBytes st)
    (hbs : s.mem.readBytes blkA (64 * n) = bs)
    (hrw_st : s.mem.RW stA 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkA (64 * n))
    (hdisj_st_stk : DisjointRegions stA 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stA 32 blkA (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkA (64 * n))
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega) :
    let s' := f s
    let outBytes := shaStateBytes ((chunks64 bs).foldl F st)
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    VmPreserved s s' ∧
    AllocCallPreserved s s' ∧
    s'.trace = s.trace ∧
    s'.mem.readBytes stA 32 = outBytes ∧
    S2Frame s.mem s'.mem [(stA, 32), (s.sp - 176#64, 176)] ∧
    AgreesOn
      (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
        OutsideRegion (s.sp - 176#64) 176 a)
      s'.mem (s.mem.writeBytes stA outBytes) :=
  hookOk_sessionCompress256ROBudget_elim_at
    (fun x R hrun' hpre' hsp' =>
      hf x R s hrun'
        (by dsimp only [withLsRet624]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hlr_ls, hpre'⟩)
        hsp')
    hrun hx0 hx1 hx2 hsp_al hst hbs hrw_st hrw_stk hread_blk
    hdisj_st_stk hdisj_st_blk hdisj_stk_blk hn_le

/-- Step through `n`-block `compress256` at `lsρ lsCompress256Sym` in any placed block program
`prog` using `HookSat H lsCompress256Sym (withLsRet624 (sessionCompress256ROBudgetSpec F 176))`. -/
public theorem s2_compress256_multi_step_placed_of_hookSat [LibsignalPlacement] {prog : Program}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_compress : HookSat H lsCompress256Sym (withLsRet624 (sessionCompress256ROBudgetSpec F 176)))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hbs : s.mem.readBytes blkPtr (64 * n) = bs)
    (hrw_st : s.mem.RW stPtr 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkPtr (64 * n))
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stPtr 32 blkPtr (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkPtr (64 * n))
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      AllocCallPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes stPtr 32 = shaStateBytes ((chunks64 bs).foldl F st) →
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (s.mem.writeBytes stPtr (shaStateBytes ((chunks64 bs).foldl F st))) →
      RunsToFrom prog s₀ s' Q)
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by prove_ls_ret624) :
    RunsToFrom prog s₀ s Q := by
  obtain ⟨f, hfH, hfOk⟩ := h_compress
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hvm, hacp, htr', hread', hs2', hag'⟩ :=
    hookOk_withLsRet624_sessionCompress256ROBudget_elim hfOk (hlr ▸ hlr_ls) hrun hx0 hx1 hx2 hsp_al
      hst hbs hrw_st hrw_stk hread_blk hdisj_st_stk hdisj_st_blk hdisj_stk_blk hn_le
  have htr_f : TraceEq s (f s) := ⟨htr', hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hpc' : (f s).pc = lr := hret.1.trans hlr
  exact RunsTo.hook hrun hhook hkf hsym
    (h (f s) (TraceEq.trans htr_f htr_s) hpc' hret.2.2 hcc hvm hacp hkf hread' hs2' hag')

/-- Step through 1-block `compress256` at `lsρ lsCompress256Sym` in any placed block program
`prog` using `HookSat H lsCompress256Sym (withLsRet624 (sessionCompress256ROBudgetSpec F 176))`. -/
public theorem s2_compress256_step_placed_of_hookSat [LibsignalPlacement] {prog : Program}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_compress : HookSat H lsCompress256Sym (withLsRet624 (sessionCompress256ROBudgetSpec F 176)))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw_st : s.mem.RW stPtr 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkPtr 64)
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hdisj_stk_blk : DisjointRegions (s.sp - 176#64) 176 blkPtr 64)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      AllocCallPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes stPtr 32 = shaStateBytes (F st blk) →
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (s.mem.writeBytes stPtr (shaStateBytes (F st blk))) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by prove_ls_ret624) :
    RunsToFrom prog s₀ s Q := by
  have hx2_nat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine s2_compress256_multi_step_placed_of_hookSat h_compress hrun hpc hx0 hx1 hx2_nat hlr
    hsp_al hst (by simpa using hblk) hrw_st hrw_stk (by simpa using hread_blk)
    hdisj_st_stk (Or.inr (by simpa using hdisj_st_blk)) (Or.inr (by simpa using hdisj_stk_blk))
    (fun s' htr hpc' hstat' hcc hvm hacp hkf hread' hs2' hag' => ?_) (by decide) htr_s hi hunmut
    hlr_ls
  rw [chunks64_single_foldl F st blk hlen] at hread' hag'
  exact h s' htr hpc' hstat' hcc hvm hacp hkf hread' hs2' hag'

/-- Step through 1-block `compress256` under `[HkdfPlacedHooksExactSat C.F H]`. -/
public theorem s2_compress256_step_placed_sat_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw_st : s.mem.RW stPtr 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkPtr 64)
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hdisj_stk_blk : DisjointRegions (s.sp - 176#64) 176 blkPtr 64)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      AllocCallPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes stPtr 32 = shaStateBytes (C.F st blk) →
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk))) →
      RunsToFrom prog s₀ s' Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by prove_ls_ret624) :
    RunsToFrom prog s₀ s Q :=
  s2_compress256_step_placed_of_hookSat hH.compress256.toHookSat hrun hpc hx0 hx1 hx2 hlr hsp_al
    hst hblk hlen hrw_st hrw_stk hread_blk hdisj_st_stk hdisj_st_blk hdisj_stk_blk h htr_s
    hi hunmut hlr_ls

/-! ## 5. `VmPreserved` & Budget Spec Lifts from `HookExactMemcpy` -/

private theorem writeBytes_perm_eq (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    ∀ a : BitVec 64, (m.writeBytes base bs).perm a = m.perm a := by
  induction bs generalizing m base with
  | nil => intro _; rfl
  | cons _ _ ih =>
    intro a
    dsimp only [Memory.writeBytes]
    rw [ih]
    dsimp only [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

/-- `applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c` preserves `VmPreserved`
(`PoolPreserved`, `physMemAvail`, per-byte `mem.perm`, and `FdsHiFrame`). -/
public theorem vmPreserved_applyMemcpyClobber_writeBytes (s : State) (dst : BitVec 64)
    (bs : List (BitVec 8)) (lr : BitVec 64) (c : MemcpyClobber) :
    VmPreserved s (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) := by
  have hp := writeBytes_perm_eq s.mem dst bs
  cases s
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

/-- Pointwise `VmPreserved` (and `oracle` preservation) for any `HookExactMemcpy f` under the
standard `memcpy(dst, src, len)` register, `spAligned`, `RW`/`Readable`, and non-overlap
preconditions. -/
public theorem hookExactMemcpy_vmPreserved {f : State → State} (hf : HookExactMemcpy f)
    {u : State} {dst src : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    VmPreserved u (f u) ∧ (f u).oracle = u.oracle := by
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  rw [heq]
  exact ⟨vmPreserved_applyMemcpyClobber_writeBytes u dst bs (u.readReg64 .lr) c, rfl⟩

/-- Any `HookExactMemcpy f` satisfies `withVmPreserved masterMemcpySpec` (covering both `ro = false`
RW and `ro = true` RO sources) without requiring a global `∀ s, VmPreserved s (f s)` hypothesis. -/
private theorem hookExactMemcpy_withVmPreserved_master_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f (withVmPreserved masterMemcpySpec) := by
  rintro ⟨ro, dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [withVmPreserved, masterMemcpySpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : bs.length ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc : s0.mem.readBytes src bs.length = bs ∧
      s0.mem.Readable src bs.length ∧
      (bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length) := by
    cases ro
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      have hb := IsBlock.pointsToBytes src bs
      refine ⟨(hb.read hsrc_front).2,
        fun a ha => ⟨by rw [hb.perm_rw hsrc_front ha]; rfl, hb.isLazyFree_false hsrc_front ha⟩, ?_⟩
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
        exact Or.inr ((IsBlock.memRegion dst bs.length).disjoint hb hpos hpos hmem)
    · dsimp only [memcpySrc, cond] at hmem
      have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
        rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
      have hb := IsBlockRO.pointsToBytesRO src bs hlen
      refine ⟨hb.read hsrc_front,
        fun a ha => ⟨hb.perm_r hsrc_front ha, hb.isLazyFree_false hsrc_front ha⟩, ?_⟩
      by_cases h0 : bs.length = 0
      · exact Or.inl h0
      · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
        have hnd : ¬ InRegion dst bs.length src := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hlen (by simp [InRegion, hpos]))
            (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length src h))
            hsrc_front
        have hns : ¬ InRegion src bs.length dst := fun h =>
          not_satisfies_ownsRO_ownsRW
            (ownsRO_pointsToBytesRO_at hlen h)
            (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length dst (by simp [InRegion, hpos])))
            hsrc_front
        dsimp only [InRegion] at hnd hns
        exact Or.inr ⟨Nat.le_of_not_lt hnd, Nat.le_of_not_lt hns⟩
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hsrc.1 hrw hsrc.2.1 hsrc.2.2
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact vmPreserved_applyMemcpyClobber_writeBytes s0 dst bs (s0.readReg64 .lr) c
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [withVmPreserved, masterMemcpySpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [heq]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret :
      (applyMemcpyClobber s0 (s0.mem.writeBytes dst bs) (s0.readReg64 .lr) c).readReg64 .x0 =
        dst := hx0
  exact ⟨⟨hx0_ret, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

private theorem hookExactMemcpy_masterMemcpy_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f masterMemcpySpec := by
  intro x R s0 hrun hpre hsp
  rcases hookExactMemcpy_withVmPreserved_master_ok hf x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

/-- Separation-logic `VmPreserved` witness for any `HookExactMemcpy f` on a `memRegion dst bs.length ∗
memcpySrc ro src bs` footprint (both `ro = false` RW and `ro = true` RO). -/
public theorem vmPreserved_of_hookExactMemcpy_sep {f : State → State}
    (hf : HookExactMemcpy f)
    {ro : Bool} {dst src : BitVec 64} {bs : List (BitVec 8)} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = bs.length)
    (hmem : s0.mem ⊨ (memRegion dst bs.length ∗ memcpySrc ro src bs) ∗ R) :
    VmPreserved s0 (f s0) := by
  have hp_master : s0.mem ⊨ (withVmPreserved masterMemcpySpec).pre (ro, dst, src, bs) s0 ∗ R := by
    dsimp only [withVmPreserved, masterMemcpySpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by rwa [sepConj_assoc] at hmem⟩
  obtain ⟨_, _, hout_vm⟩ :=
    hookExactMemcpy_withVmPreserved_master_ok hf (ro, dst, src, bs) R s0 hrun hp_master hsp
  rcases hout_vm with ⟨_, _, hq⟩ | ⟨_, hp_sat⟩ | ⟨_, _, he_sat⟩ | ⟨_, ho_sat⟩
  · dsimp only [withVmPreserved] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.1
  · exact False.elim (not_satisfies_false_sepConj hp_sat)
  · exact False.elim (not_satisfies_false_sepConj he_sat)
  · exact False.elim (not_satisfies_false_sepConj ho_sat)

/-- Generic `VmPreserved`-strengthened (`withVmPreserved`-shape) upgrade for any `memcpy` spec
`target` from `HookOk f target` and a precondition-conditioned `VmPreserved` witness (e.g. via
`vmPreserved_of_hookExactMemcpy_sep`). -/
public theorem hookOk_withVmPreserved_of_witness {β : Type} {f : State → State}
    {target : Spec β}
    (hbase : HookOk f target)
    (hwit : ∀ y R s0, s0.status = .Running → s0.spAligned = true →
      s0.mem ⊨ target.pre y s0 ∗ R → VmPreserved s0 (f s0)) :
    HookOk f { target with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ target.post x s0 sf } := by
  intro y R s0 hrun hp hsp
  have hvm : VmPreserved s0 (f s0) := hwit y R s0 hrun hsp hp
  rcases hbase y R s0 hrun hp hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost⟩
  · exact Or.inr hrest

private theorem hookOk_withVmPreserved_of_exact_lift {β : Type} {f : State → State}
    {target : Spec β}
    (hf : HookExactMemcpy f)
    (hbase : HookOk f target)
    (g : β → Bool × BitVec 64 × BitVec 64 × List (BitVec 8))
    (F : β → State → SepProp)
    (hpre : ∀ y s0, target.pre y s0 ⊢ masterMemcpySpec.pre (g y) s0 ∗ F y s0) :
    HookOk f (withVmPreserved target) := by
  intro y R s0 hrun hp hsp
  have hp_master : s0.mem ⊨ (withVmPreserved masterMemcpySpec).pre (g y) s0 ∗ (F y s0 ∗ R) := by
    dsimp only [withVmPreserved]
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  obtain ⟨_, _, hout_vm⟩ :=
    hookExactMemcpy_withVmPreserved_master_ok hf (g y) (F y s0 ∗ R) s0 hrun hp_master hsp
  have hvm : VmPreserved s0 (f s0) := by
    rcases hout_vm with ⟨_, _, hq⟩ | ⟨_, hp_sat⟩ | ⟨_, _, he_sat⟩ | ⟨_, ho_sat⟩
    · dsimp only [withVmPreserved] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.1
    · exact False.elim (not_satisfies_false_sepConj hp_sat)
    · exact False.elim (not_satisfies_false_sepConj he_sat)
    · exact False.elim (not_satisfies_false_sepConj ho_sat)
  rcases hbase y R s0 hrun hp hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost⟩
  · exact Or.inr hrest

/-- Any `HookExactMemcpy f` satisfies `sessionMemcpyRegionBudgetSpec`
(`= withVmPreserved sessionMemcpyRegionSpec`). -/
public theorem hookExactMemcpy_sessionMemcpyRegionBudget_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f sessionMemcpyRegionBudgetSpec := by
  change HookOk f (withVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec)
  refine hookOk_withVmPreserved_of_exact_lift hf
    (hookOk_sessionMemcpyRegion_of_master (hookExactMemcpy_masterMemcpy_ok hf))
    (fun ⟨d, s, b⟩ => (false, d, s, b)) (fun _ _ => emp)
    (fun ⟨_, _, _⟩ _ => ?_)
  dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
    memcpyRegionSpec, masterMemcpySpec, memcpySrc, cond]
  exact Entails.of_eq (sepConj_emp _).symm

/-- Lift `HookSatExactMemcpy H name` to `HookSat H name sessionMemcpyRegionBudgetSpec`. -/
public theorem hookSat_sessionMemcpyRegionBudget_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) :
    HookSat H name sessionMemcpyRegionBudgetSpec := by
  obtain ⟨f, hfH, hfEx⟩ := h
  exact ⟨f, hfH, hookExactMemcpy_sessionMemcpyRegionBudget_ok hfEx⟩

/-- Any `HookExactMemcpy f` satisfies `sessionMemcpyBudgetSpec stk`
(`= withVmPreserved (sessionMemcpySpec stk)`). -/
public theorem hookExactMemcpy_sessionMemcpyBudget_ok {f : State → State}
    (hf : HookExactMemcpy f) (stk : Nat := 4096) :
    HookOk f (sessionMemcpyBudgetSpec stk) := by
  change HookOk f
    (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec stk))
  refine hookOk_withVmPreserved_of_exact_lift hf
    (hookOk_sessionMemcpy_of_master (hookExactMemcpy_masterMemcpy_ok hf) stk)
    (fun ⟨d, s, b⟩ => (false, d, s, b)) (fun _ s0 => stackAt s0.sp stk)
    (fun ⟨_, _, _⟩ _ => ?_)
  dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
    libcMemcpySpec, masterMemcpySpec, memcpySrc, cond]
  exact Entails.of_eq (by simp only [sepConj_assoc])

/-- Lift `HookSatExactMemcpy H name` to `HookSat H name (sessionMemcpyBudgetSpec stk)`. -/
public theorem hookSat_sessionMemcpyBudget_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) (stk : Nat := 4096) :
    HookSat H name (sessionMemcpyBudgetSpec stk) := by
  obtain ⟨f, hfH, hfEx⟩ := h
  exact ⟨f, hfH, hookExactMemcpy_sessionMemcpyBudget_ok hfEx stk⟩

/-! ## 6. `176`-Byte `compress256`-Stacked `*Sat` HKDF/HMAC Stack Budgets & Specs -/

/-- `new_from_slice` own frame (`544` B) + `compress256` real-code frame (`176` B) = `720` B. -/
public abbrev newFromSliceStackSat : Nat := 720

/-- `finalize_fixed` own frame (`144` B) + `compress256` real-code frame (`176` B) = `320` B. -/
public abbrev finalizeFixedStackSat : Nat := 320

/-- `extract` own frame (`432` B) + `newFromSliceStackSat` (`720` B) = `1152` B. -/
public abbrev extractStackSat : Nat := 1152

/-- `expand_multi_info` own frame (`496` B) + `finalizeFixedStackSat` (`320` B) = `816` B. -/
public abbrev expandMultiInfoStackSat : Nat := 816

/-- `720`-byte-stack sibling of `newFromSliceSpec` accounting for `compress256`'s `176`-byte frame. -/
@[expose] public def newFromSliceSpecSat (F : ShaCompress) : Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
      memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗
      stackAt s.sp newFromSliceStackSat
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
      (x.keyA ↦ₛ x.key) ∗
      stackAt s0.sp newFromSliceStackSat

/-- `320`-byte-stack sibling of `finalizeFixedSpec` accounting for `compress256`'s `176`-byte frame. -/
@[expose] public def finalizeFixedSpecSat (F : ShaCompress) : Spec FinalizeFixedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.hm ∧
      x.key.length ≤ 64 ∧ x.msg.length < 56⌝ ∗
      memRegion x.out 32 ∗ hmacCoreAt F x.hm x.key x.msg ∗
      stackAt s.sp finalizeFixedStackSat
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.out ↦ₛ hmacWith F x.key x.msg) ∗ memRegion x.hm 0x90 ∗
      stackAt s0.sp finalizeFixedStackSat

/-- `1152`-byte-stack sibling of `extractSpec` accounting for `compress256`'s `176`-byte frame. -/
@[expose] public def extractSpecSat (F : ShaCompress) : Spec ExtractGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.saltA ∧
      (x.salt.isSome → s.readReg64 .x2 = 32#64) ∧
      (x.salt = none → x.saltA = 0#64 ∨ s.readReg64 .x2 = 0#64) ∧
      s.readReg64 .x3 = x.ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      x.ikm.length = 32⌝ ∗
      memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s.sp extractStackSat
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦ₛ x.prk F) ∗ hmacCoreAt F (x.ret + 0x20#64) (x.prk F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s0.sp extractStackSat

/-- `816`-byte-stack sibling of `expandMultiInfoSpec` accounting for `compress256`'s `176`-byte frame. -/
@[expose] public def expandMultiInfoSpecSat (F : ShaCompress) : Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧ s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.okmLen ∧
      x.prk.length ≤ 64 ∧ x.info.length < 23 ∧ (x.okmLen = 64 ∨ x.okmLen = 80)⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      stackAt s.sp expandMultiInfoStackSat
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand F x.prk x.info x.okmLen) ∗
      stackAt s0.sp expandMultiInfoStackSat

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
