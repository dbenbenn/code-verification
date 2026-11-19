/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Placed.Multi
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclFetch
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Machine-code proofs for `libcrux_sha2::hacl` subroutines

Proves `subroutine_ok` contracts for blocks `0` (`sha256_init`), `2` (`sha256_update_nblocks`),
`3` (`sha256_update_last`), `4` (`sha256_finish`), and `5` (`hash_256`), together with
`haclMemcpySpec`, `withTraceEq`, and the combined `HaclSubroutines` bundle (`haclSubroutines_ok`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256

open Arm64 ProofLib
open ProofLib.StdStartup (StdStatePreserved stdMemcpySpec)
open CryptoGames.HMAC (ShaState sha256IV sha256With toBEBytes chunks64)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (cells_sub_elim)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
  (sha256CompressState toLEBytes_4_eq_unpack32 pointsToBytes_shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
  (chunks64_of_length_lt chunks64_cons_take_drop)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift (ProcessFieldsPreserved_toHeapVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (sha256InitSym sha256UpdateSym sha256UpdateNblocksSym sha256UpdateLastSym sha256FinishSym
   hash256Sym libcruxHmacSym memcpySym sha256InitBlock sha256UpdateBlock sha256UpdateNblocksBlock
   sha256UpdateLastBlock sha256FinishBlock hash256Block libcruxHmacBlock
   libcruxHmacLib HaclPlacement haclMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
  (chunks64_exact_one haclPadTail haclUpdateLastState haclPadTail_length_lt56
   haclPadTail_length_ge56 unpack32_rev32_eq_toBEBytes_4 haclHash256Pure_eq_sha256With)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclFetch
  (haclPC0 haclPl0 haclPC0_eq_blockProgram haclPl0_base haclPC2 haclPl2 haclPC2_eq_blockProgram
   haclPl2_base haclPl2_rho haclPC3 haclPl3 haclPC3_eq_blockProgram haclPl3_base haclPl3_rho
   haclPC4 haclPl4 haclPC4_eq_blockProgram haclPl4_base haclPC5 haclPl5 haclPC5_eq_blockProgram
   haclPl5_base haclPl5_rho)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
  (HaclInProg execInst_bl_eq withHaclPreserved subroutine_ok_of_pure_block sepWP_block_seg
   sepWP_block_bl sha256InitRawSpec sha256UpdateRawSpec sha256UpdateNblocksSpec
   sha256UpdateLastSpec sha256FinishRawSpec hash256Spec HaclSubroutines)

arm64_proof_prelude

@[wp_norm] private theorem zeroExtend_32_64_eq_setWidth (x : BitVec 32) :
    BitVec.zeroExtend 64 x = BitVec.setWidth 64 x := rfl

private theorem sepWP_of_eq {P : Program} {t : BitVec 64} {s : State} {Pre' Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP P t s Pre' post oom) (heq : Pre = Pre') : SepWP P t s Pre post oom := heq ▸ h

private theorem add_off_rel_target (b t off : BitVec 64) : (b + off) + ((t - b) - off) = t := by bv_omega

/-! ## 1. Minimal `0`-B Stack `memcpy` Contract & `withTraceEq` Bridges -/

/-- Minimal `0`-B caller-stack `memcpy` contract consumed by `sha256_update_last`, preserving
`sf.fs = s0.fs`, `sf.trace = s0.trace`, and `VmPreserved s0 sf` (`allocMemcpyVmSpec` and `stdMemcpySpec`). -/
@[expose] def haclMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Discharge `haclMemcpySpec` from `RustStdAllocBudgetBridge.allocMemcpyVmSpec`. -/
theorem haclMemcpy_of_allocMemcpyVm {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr allocMemcpyVmSpec) : subroutine_ok P addr haclMemcpySpec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun hpre hsp fun sf out => ?_
  rcases out with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [allocMemcpyVmSpec, haclMemcpySpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.1.1, hq.1.2.1.2.1, hq.1.2.2⟩, hq.2⟩
  all_goals exact False.elim (not_satisfies_false_sepConj hp)

/-- Discharge `haclMemcpySpec` from `ProofLib.StdStartup.stdMemcpySpec`. -/
theorem haclMemcpy_of_stdMemcpy {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr stdMemcpySpec) : subroutine_ok P addr haclMemcpySpec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun hpre hsp fun sf out => ?_
  rcases out with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [stdMemcpySpec, haclMemcpySpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; rcases hq with ⟨⟨hx0, hstd⟩, hmem⟩
    exact ⟨⟨hx0, hstd.1, hstd.2.1, ⟨⟨hstd.2.2.2.2.2.1, hstd.2.2.2.2.1, hstd.2.2.1⟩,
      hstd.2.2.2.2.2.2.1, hstd.2.2.2.2.2.2.2, FdsHiFrame.of_fs_eq hstd.1⟩⟩, hmem⟩
  all_goals exact False.elim (not_satisfies_false_sepConj hp)

/-- Discharge `haclMemcpySpec` directly from a `HookSat` entry at `P.externAt? addr`. -/
theorem haclMemcpy_of_hookSat {P : Program} {addr : BitVec 64}
    {H : String → Option (State → State)} {sym : String}
    (hext : P.externAt? addr = H sym) (hsat : HookSat H sym haclMemcpySpec) :
    subroutine_ok P addr haclMemcpySpec := by
  rcases hsat with ⟨f, hH, hok⟩; exact subroutine_ok_of_hookOk (hext.trans hH) hok

/-- Augment a `Spec α` postcondition with `sf.trace = s0.trace ∧ sf.fs = s0.fs` for `libcruxHmacSpec` callers. -/
abbrev withTraceEq {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun g s0 sf => spec.post g s0 sf ∗ ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ }

/-- Drop `sf.trace = s0.trace ∧ sf.fs = s0.fs` from `withTraceEq spec` to recover `subroutine_ok` for `spec`. -/
theorem subroutine_ok_of_withTraceEq {α : Type} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P addr (withTraceEq spec)) : subroutine_ok P addr spec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | rest)
  · dsimp only [withTraceEq] at hq
    rw [show (spec.post x s0 sf ∗ ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝) ∗ R =
      ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (spec.post x s0 sf ∗ R) by sep_ac_rfl,
      satisfies_pure_sepConj] at hq
    exact Or.inl ⟨hret, hcc, hq.2⟩
  · exact Or.inr rest

private def VmTracePreserved (s0 sf : State) : Prop :=
  VmPreserved s0 sf ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs
private theorem VmTracePreserved.trans {s0 s1 s2 : State}
    (h01 : VmTracePreserved s0 s1) (h12 : VmTracePreserved s1 s2) : VmTracePreserved s0 s2 :=
  ⟨h01.1.trans h12.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩
private theorem VmTracePreserved.of_pf {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    VmTracePreserved s0 sf := ⟨ProcessFieldsPreserved_toHeapVmPreserved h, h.2.1, h.1⟩

/-! ## 2. Stack & 32-Byte Slice Decomposition Helpers -/

private def savedRegs8 (s0 : State) : SepProp :=
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private def savedRegs11 (s0 : State) : SepProp :=
  (((s0.sp - 96#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
   ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x27)) ∗
  (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
   ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))

private theorem stackFrame_cells_eq (s0 : State) (n k : Nat)
    (hn : n = 8 * k := by decide) (hk : 8 * k ≤ 2 ^ 64 := by decide) :
    stackFrame s0 n = cells (s0.sp - BitVec.ofNat 64 n) k := by
  subst hn; exact stackAt_eq_cells s0.sp k hk

private theorem stackFrame_split_cells_eq (s0 : State) (n m k off : Nat)
    (hn : n = m + 8 * k := by decide) (hoff : off = 8 * k := by decide)
    (hk : m + 8 * k ≤ 2 ^ 64 := by decide) :
    stackFrame s0 n =
      stackAt (s0.sp - BitVec.ofNat 64 off) m ∗ cells (s0.sp - BitVec.ofNat 64 off) k := by
  subst hn; subst hoff; exact stackAt_split_cells s0.sp m k hk

private theorem cells8_entails (s0 : State) (v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64) :
    (((s0.sp - 64#64) ↦₆₄ v1) ∗ ((s0.sp - 56#64) ↦₆₄ v2) ∗ ((s0.sp - 48#64) ↦₆₄ v3) ∗
     ((s0.sp - 40#64) ↦₆₄ v4) ∗ ((s0.sp - 32#64) ↦₆₄ v5) ∗ ((s0.sp - 24#64) ↦₆₄ v6) ∗
     ((s0.sp - 16#64) ↦₆₄ v7) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ⊢ cells (s0.sp - 64#64) 8 := by
  repeat (refine cells_sub_succ_entails _ _ ?_ (by decide) (by decide))
  dsimp only [Nat.reduceSub]; rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  exact Entails.sepExists_right v8 (by dsimp only [Nat.reduceSub]; rw [cells_zero, sepConj_emp]; exact Entails.refl _)

private theorem stackFrame16_entails (s0 : State) (v1 v2 : BitVec 64) :
    (((s0.sp - 16#64) ↦₆₄ v1) ∗ ((s0.sp - 8#64) ↦₆₄ v2)) ⊢ stackFrame s0 16 := by
  rw [stackFrame_cells_eq s0 16 2]
  refine cells_sub_succ_entails 16 2 ?_ (by decide) (by decide)
  dsimp only [Nat.reduceSub]; rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  exact Entails.sepExists_right v2 (by dsimp only [Nat.reduceSub]; rw [cells_zero, sepConj_emp]; exact Entails.refl _)

private theorem pointsToBytes_32_to_cells32 (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ Sha256Cells.readLE32 bs 0) ∗ ((a + 4#64) ↦₃₂ Sha256Cells.readLE32 bs 4) ∗
       ((a + 8#64) ↦₃₂ Sha256Cells.readLE32 bs 8) ∗ ((a + 12#64) ↦₃₂ Sha256Cells.readLE32 bs 12) ∗
       ((a + 16#64) ↦₃₂ Sha256Cells.readLE32 bs 16) ∗ ((a + 20#64) ↦₃₂ Sha256Cells.readLE32 bs 20) ∗
       ((a + 24#64) ↦₃₂ Sha256Cells.readLE32 bs 24) ∗ ((a + 28#64) ↦₃₂ Sha256Cells.readLE32 bs 28)) := by
  have h0 := Sha256Cells.pointsToBytes_drop_step4 a bs 0 (by omega)
  simp only [List.drop_zero, BitVec.add_zero] at h0
  rw [h0, Sha256Cells.pointsToBytes_drop_step4 a bs 4 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 8 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 12 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 16 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 20 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 24 (by omega),
      Sha256Cells.pointsToBytes_drop_step4 a bs 28 (by omega),
      List.drop_eq_nil_of_le (by omega), pointsToBytes_nil, sepConj_emp]

/-! ## 3. Block `0`: `libcrux_sha2::hacl::sha256_init` (`78` words) -/

private theorem x1_ge8_branches (x1 : BitVec 64) (hx1 : 8 ≤ x1.toNat) :
    (x1 == 0#64) = false ∧ (x1 == 1#64) = false ∧ BitVec.ule x1 2#64 = false ∧
    (x1 == 3#64) = false ∧ BitVec.ule x1 4#64 = false ∧ (x1 == 5#64) = false ∧
    BitVec.ule x1 6#64 = false ∧ (x1 == 7#64) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [beq_eq_false_iff_ne]; intro h; subst h; simp at hx1)
    | (rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; simp; omega)

private theorem sha256Init_raw_at [HaclPlacement] :
    subroutine_ok (haclPC0.rebase haclPl0.base (fun _ => none)) haclPl0.base sha256InitRawSpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨stA, old⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [sha256InitRawSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hold_len⟩, hpre⟩; refine ⟨_, hpre, ?_⟩
  rcases x1_ge8_branches (s0.readReg64 (Reg.gpr 1#5)) hx1 with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  wp_conv_pre => rw [stackFrame_cells_eq s0 16 2]
  repeat (apply cells_sub_elim (by decide) (by decide); intro _)
  rw [pointsToBytes_32_to_cells32 stA old hold_len]
  wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_sym_steps 43
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨?_, by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [wp_norm]⟩⟩
  intro hmem; rw [pointsToBytes_shaStateBytes stA sha256IV]
  dsimp only [sha256IV, List.Vector.toList, List.getD_cons_zero, List.getD_cons_succ]
  refine Satisfies.of_entails hmem ?_
  have hstk := stackFrame16_entails s0 (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
  rw [← sepConj_assoc]; refine sepConj_mono_left ?_; simp only [sepConj_assoc] at hstk ⊢
  repeat refine sepConj_mono_right ?_
  exact hstk

/-- Raw pure-block `subroutine_ok` for Block `0` (`libcrux_sha2::hacl::sha256_init`). -/
theorem sha256Init_raw_subroutineOk (mpl : Obj.MultiPlacement) (hpl : libcruxHmacLib.Placeable mpl) :
    subroutine_ok (libcruxHmacLib.blockProgram mpl 0) (mpl.base 0) sha256InitRawSpec := by
  let _ : HaclPlacement := ⟨mpl, hpl⟩
  change subroutine_ok (libcruxHmacLib.blockProgram haclMpl 0) (haclMpl.base 0) sha256InitRawSpec
  rw [← haclPC0_eq_blockProgram, ← haclPl0_base]; exact sha256Init_raw_at

/-- Ambient-program `subroutine_ok` for Block `0` (`libcrux_sha2::hacl::sha256_init`). -/
theorem sha256Init_subroutineOk {P : Program} {mpl : Obj.MultiPlacement} (hP : HaclInProg P mpl) :
    subroutine_ok P (mpl.base 0) (withHaclPreserved mpl sha256InitRawSpec) :=
  subroutine_ok_of_pure_block (by decide : 0 < 7) hP (fun ⟨_, _⟩ s _ => by cases s; rfl)
    (fun ⟨_, _⟩ s1 s2 _ _ => by cases s1; cases s2; rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (sha256Init_raw_subroutineOk mpl hP.placeable)

/-! ## 4. Block `4`: `libcrux_sha2::hacl::sha256_finish` (`79` words) -/

private theorem pointsToBytes_beState_append (dstA : BitVec 64) (st : ShaState) (tail : List (BitVec 8)) :
    (dstA ↦ₛ (st.toList.flatMap (toBEBytes 4) ++ tail)) =
      ((dstA ↦₃₂ (rev32_64 ((st.toList.getD 0 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 4#64) ↦₃₂ (rev32_64 ((st.toList.getD 1 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 8#64) ↦₃₂ (rev32_64 ((st.toList.getD 2 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 12#64) ↦₃₂ (rev32_64 ((st.toList.getD 3 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 16#64) ↦₃₂ (rev32_64 ((st.toList.getD 4 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 20#64) ↦₃₂ (rev32_64 ((st.toList.getD 5 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 24#64) ↦₃₂ (rev32_64 ((st.toList.getD 6 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 28#64) ↦₃₂ (rev32_64 ((st.toList.getD 7 0#32).setWidth 64)).setWidth 32) ∗
       ((dstA + 32#64) ↦ₛ tail)) := by
  rcases st with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hst⟩ <;>
    try (simp at hst)
  change (dstA ↦ₛ (toBEBytes 4 w0 ++ (toBEBytes 4 w1 ++ (toBEBytes 4 w2 ++ (toBEBytes 4 w3 ++
    (toBEBytes 4 w4 ++ (toBEBytes 4 w5 ++ (toBEBytes 4 w6 ++ (toBEBytes 4 w7 ++ tail))))))))) = _
  simp only [← unpack32_rev32_eq_toBEBytes_4]
  repeat rw [pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.truncate_eq_setWidth]; rfl

private theorem sha256Finish_raw_at [HaclPlacement] :
    subroutine_ok (haclPC4.rebase haclPl4.base (fun _ => none)) haclPl4.base sha256FinishRawSpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨stA, st, dstA, dst⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [sha256FinishRawSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hdst_ge⟩, hpre⟩; refine ⟨_, hpre, ?_⟩
  rcases x1_ge8_branches (s0.readReg64 (Reg.gpr 1#5)) hx1 with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  have hb31 : (s0.readReg64 (Reg.gpr 3#5)).ule 31#64 = false := by
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; change ¬ (s0.readReg64 .x3).toNat ≤ 31; omega
  wp_conv_pre => rw [← sepConj_assoc, stackFrame_cells_eq s0 16 2]
  repeat (apply cells_sub_elim (by decide) (by decide); intro _)
  rw [pointsToBytes_take_drop dstA 32 dst hdst_ge,
      pointsToBytes_32_to_cells32 dstA (dst.take 32) (List.length_take_of_le hdst_ge),
      pointsToBytes_shaStateBytes stA st]
  wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_sym_steps 37
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨?_, by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [wp_norm]⟩⟩
  intro hmem; rw [pointsToBytes_beState_append dstA st (dst.drop 32)]; refine Satisfies.of_entails hmem ?_
  have hstk := stackFrame16_entails s0 (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
  refine sepConj_mono_left ?_; simp only [sepConj_assoc] at hstk ⊢
  repeat refine sepConj_mono_right ?_
  exact hstk

/-- Raw pure-block `subroutine_ok` for Block `4` (`libcrux_sha2::hacl::sha256_finish`). -/
theorem sha256Finish_raw_subroutineOk (mpl : Obj.MultiPlacement) (hpl : libcruxHmacLib.Placeable mpl) :
    subroutine_ok (libcruxHmacLib.blockProgram mpl 4) (mpl.base 4) sha256FinishRawSpec := by
  let _ : HaclPlacement := ⟨mpl, hpl⟩
  change subroutine_ok (libcruxHmacLib.blockProgram haclMpl 4) (haclMpl.base 4) sha256FinishRawSpec
  rw [← haclPC4_eq_blockProgram, ← haclPl4_base]; exact sha256Finish_raw_at

/-- Ambient-program `subroutine_ok` for Block `4` (`libcrux_sha2::hacl::sha256_finish`). -/
theorem sha256Finish_subroutineOk {P : Program} {mpl : Obj.MultiPlacement} (hP : HaclInProg P mpl) :
    subroutine_ok P (mpl.base 4) (withHaclPreserved mpl sha256FinishRawSpec) :=
  subroutine_ok_of_pure_block (by decide : 4 < 7) hP (fun ⟨_, _, _, _⟩ s _ => by cases s; rfl)
    (fun ⟨_, _, _, _⟩ s1 s2 _ _ => by cases s1; cases s2; rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (sha256Finish_raw_subroutineOk mpl hP.placeable)

/-! ## 5. Shared `BL` Call Helpers & Block `2`: `sha256_update_nblocks` (`35` words) -/

private theorem resolve_sha256Update (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256UpdateSym = mpl.base 1 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256InitSym, sha256UpdateSym]

private theorem resolve_sha256UpdateLast (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl sha256UpdateLastSym = mpl.base 3 := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym, sha256UpdateLastSym]

private theorem resolve_memcpy (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.resolve mpl memcpySym = mpl.ρ memcpySym := by
  simp [Obj.MultiPlacedLib.resolve, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, libcruxHmacBlock, sha256InitSym,
    sha256UpdateSym, sha256UpdateNblocksSym, sha256UpdateLastSym, sha256FinishSym, hash256Sym,
    libcruxHmacSym, memcpySym]

private theorem processFieldsPreserved_execInst_bl (imm : BitVec 64) (s : State) :
    ProcessFieldsPreserved s (execInst (.bl imm) s) := by
  rw [execInst_bl_eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

private theorem calleeSavedPreserved_of_bl {imm : BitVec 64} {s sf : State}
    (h : CalleeSavedPreserved (execInst (.bl imm) s) sf) : CalleeSavedPreserved s sf := by
  rw [execInst_bl_eq] at h; rcases h with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  simp only [wp_norm] at h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hfp hv
  exact ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩

private def UpperCalleePreserved (s0 sf : State) : Prop :=
  sf.readReg64 .x25 = s0.readReg64 .x25 ∧ sf.readReg64 .x26 = s0.readReg64 .x26 ∧
  sf.readReg64 .x27 = s0.readReg64 .x27 ∧ sf.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0
private theorem UpperCalleePreserved.trans {s0 s1 s2 : State}
    (h01 : UpperCalleePreserved s0 s1) (h12 : UpperCalleePreserved s1 s2) : UpperCalleePreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.trans h01.2.2.2.2⟩
private theorem UpperCalleePreserved.of_calleeSavedPreserved {s0 sf : State}
    (h : CalleeSavedPreserved s0 sf) : UpperCalleePreserved s0 sf :=
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem sepWP_block_pure_seg {P : Program} {mpl : Obj.MultiPlacement} {i : Nat}
    (hi : i < 7) (hP : HaclInProg P mpl) {mid target : BitVec 64} {s : State}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem) {Frame : SepProp} {PurePost : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hPure_mem : ∀ (sm : State) (m : Memory), PurePost (sm.setMem m) ↔ PurePost sm)
    (hseg : ∀ m : Memory, SepWP (libcruxHmacLib.blockProgram mpl i) mid (s.setMem m) emp
      (fun sm' Pm' => PurePost sm' ∧ (Pm' ⊢ emp)) (fun _ => ⌜False⌝))
    (hcont : ∀ sm : State, sm.pc = mid → sm.status = .Running → ProcessFieldsPreserved s sm →
      libcruxHmacLib.CodeLoaded mpl sm.mem → PurePost sm → SepWP P target sm Frame post oom) :
    SepWP P target s Frame post oom := by
  rw [← emp_sepConj Frame]
  refine sepWP_block_seg hi hP hcl (Pre := emp) (Post := fun _ => emp) (Frame := Frame)
    (fun _ _ => rfl) hPure_mem hseg fun sm hpc' hrun' hpf hcl' hpure => ?_
  rw [emp_sepConj]; exact hcont sm hpc' hrun' hpf hcl' hpure

private theorem step_bl_sha256Update {P : Program} {mpl : Obj.MultiPlacement} {i : Nat}
    (hi : i < 7) (hP : HaclInProg P mpl) {off : Nat}
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    {blkA stA target_pc : BitVec 64} {bs : List (BitVec 8)} {st : ShaState} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded mpl s.mem) (hpc : s.pc = mpl.base i + BitVec.ofNat 64 off)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hf : (libcruxHmacLib.blockProgram mpl i).fetch (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl ((mpl.base 1 - mpl.base i) - BitVec.ofNat 64 off)))
    (hx0 : s.readReg64 .x0 = blkA) (hx1 : (s.readReg64 .x1).toNat = bs.length) (hbs64 : 64 ≤ bs.length)
    (hx2 : s.readReg64 .x2 = stA) (hx3 : 8 ≤ (s.readReg64 .x3).toNat)
    (hnext : ∀ sf : State, sf.pc = s.pc + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → ProcessFieldsPreserved s sf → libcruxHmacLib.CodeLoaded mpl sf.mem →
      SepWP P target_pc sf (((blkA ↦ₛ bs) ∗
        (stA ↦ₛ shaStateBytes (sha256CompressState st (bs.take 64))) ∗ stackFrame s 160) ∗ F) post oom)
    (hoff : off < (libcruxHmacLib.blocks[i]'hi).code.length := by decide) :
    SepWP P target_pc s (((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s 160) ∗ F) post oom := by
  refine sepWP_block_bl hi hP hoff hupd (x := (blkA, bs, stA, st)) (F := F)
    hcl hpc hrun hsp_align (by rw [hpc]; exact hf) (by rw [hpc]; exact add_off_rel_target _ _ _) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R hm; dsimp only [withHaclPreserved, sha256UpdateRawSpec]
    rw [show stackFrame (execInst _ s) 160 = stackFrame s 160 by simp [stackFrame, execInst_bl_eq],
        sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by rw [execInst_bl_eq, State.mem_setPC, State.mem_writeReg64]; exact hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp only [wp_norm]; exact ⟨hx0, hx1, hbs64, hx2, hx3⟩, by simpa only [sepConj_assoc] using hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f _; dsimp only [withHaclPreserved, sha256UpdateRawSpec]
    rw [show stackFrame (execInst _ s) 160 = stackFrame s 160 by simp [stackFrame, execInst_bl_eq],
        sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hpf_bl, hcl_f⟩
    exact hnext sf hpc_f hrun_f hsp_f (calleeSavedPreserved_of_bl hcs_f)
      ((processFieldsPreserved_execInst_bl _ s).trans hpf_bl) hcl_f

private theorem stackFrame224_entails (s0 : State) (v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64) :
    (stackAt (s0.sp - 64#64) 160 ∗ ((s0.sp - 64#64) ↦₆₄ v1) ∗ ((s0.sp - 56#64) ↦₆₄ v2) ∗
     ((s0.sp - 48#64) ↦₆₄ v3) ∗ ((s0.sp - 40#64) ↦₆₄ v4) ∗ ((s0.sp - 32#64) ↦₆₄ v5) ∗
     ((s0.sp - 24#64) ↦₆₄ v6) ∗ ((s0.sp - 16#64) ↦₆₄ v7) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ⊢
    stackFrame s0 224 := by
  rw [stackFrame_split_cells_eq s0 224 160 8 64]
  exact sepConj_mono_right (cells8_entails s0 v1 v2 v3 v4 v5 v6 v7 v8)

private theorem lsr6_32_of_lt32 {len : Nat} (hlen : len < 2 ^ 32) {x0 : BitVec 64}
    (hx0 : x0.setWidth 32 = BitVec.ofNat 32 len) :
    x0.setWidth 32 >>> 6 = BitVec.ofNat 32 (len / 64) := by
  rw [hx0]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]; omega

private theorem x24_init_eq {x2 : BitVec 64} {n : Nat} (hx2 : x2.toNat = n) (hmax : n + 64 < 2 ^ 64) :
    (x2 + 64#64) >>> 6 = BitVec.ofNat 64 ((n + 64) / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hx2]
  rw [Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (by omega : (n + 64) / 64 < 2 ^ 64)]

private theorem x24_pos_bne_zero {n : Nat} (hge : 64 ≤ n) (hmax : n + 64 < 2 ^ 64) :
    (BitVec.ofNat 64 ((n + 64) / 64) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro h; have htn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at htn; omega

private theorem chunks64_take_succ_blocks (bs : List (BitVec 8)) (rem : Nat)
    (h : 64 * (rem + 2) ≤ bs.length) :
    chunks64 (bs.take (64 * (rem + 2))) =
      bs.take 64 :: chunks64 ((bs.drop 64).take (64 * (rem + 1))) := by
  rw [chunks64_cons_take_drop (by rw [List.length_take_of_le h]; omega),
      show (bs.take (64 * (rem + 2))).take 64 = bs.take 64 by rw [List.take_take]; congr 1,
      show (bs.take (64 * (rem + 2))).drop 64 = (bs.drop 64).take (64 * (rem + 1)) by
        rw [List.drop_take]; congr 1]

private theorem loop_step_arith {rem' : Nat} {curBs : List (BitVec 8)} {rlen : BitVec 64}
    (hrem32 : rem' + 1 + 1 < 2 ^ 32) (hbs_ge : 64 ≤ curBs.length) (hbs_max : curBs.length + 64 < 2 ^ 64)
    (hrlen : rlen.toNat = curBs.length) :
    (BitVec.ofNat 64 (rem' + 1 + 1) - 1#64 == 0#64) = false ∧
    BitVec.ofNat 64 (rem' + 1 + 1) - 1#64 = BitVec.ofNat 64 (rem' + 1) ∧
    BitVec.ofNat 64 ((curBs.length + 64) / 64) - 1#64 =
      BitVec.ofNat 64 (((curBs.drop 64).length + 64) / 64) ∧
    (rlen - 64#64).toNat = (curBs.drop 64).length := by
  refine ⟨by rw [beq_eq_false_iff_ne]; intro h; have htn := congrArg BitVec.toNat h
             simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at htn; omega, by bv_omega,
    by rw [List.length_drop]; apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega, ?_⟩
  have hle : (64#64 : BitVec 64) ≤ rlen := by rw [BitVec.le_def]; change 64 ≤ rlen.toNat; omega
  rw [List.length_drop, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, hrlen]

private theorem fetch_block2_bl_update [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 2).fetch (haclMpl.base 2 + 72#64) =
      some (.bl ((haclMpl.base 1 - haclMpl.base 2) - 72#64)) := by
  rw [← haclPC2_eq_blockProgram, ← haclPl2_base]
  have hf : (haclPC2.rebase haclPl2.base (fun _ => none)).fetch (haclPl2.base + 72#64) =
      some (.bl ((haclPl2.ρ sha256UpdateSym - haclPl2.base) - 72#64)) := by
    dsimp only [sha256UpdateSym]; simp [wp_norm]
  rw [hf, ← haclPl2_rho, haclPl2_base, resolve_sha256Update haclMpl]

private theorem nblocks_loop [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hupd : subroutine_ok P (haclMpl.base 1) (withHaclPreserved haclMpl sha256UpdateRawSpec)) :
    ∀ (rem : Nat) (curA stA target_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : ShaState)
      (Frame : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp},
      libcruxHmacLib.CodeLoaded haclMpl s.mem → s.pc = haclMpl.base 2 + 52#64 →
      s.status = .Running → s.spAligned = true → rem + 1 < 2 ^ 32 →
      64 * (rem + 1) ≤ curBs.length → curBs.length + 64 < 2 ^ 64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = BitVec.ofNat 64 ((curBs.length + 64) / 64) →
      s.readReg64 .x22 = curA → (s.readReg64 .x21).toNat = curBs.length →
      s.readReg64 .x20 = stA → 8 ≤ (s.readReg64 .x19).toNat →
      (∀ sm : State, sm.pc = haclMpl.base 2 + 96#64 → sm.status = .Running →
        sm.sp = s.sp → sm.spAligned = true → UpperCalleePreserved s sm →
        ProcessFieldsPreserved s sm → libcruxHmacLib.CodeLoaded haclMpl sm.mem →
        SepWP P target_pc sm (((curA ↦ₛ curBs) ∗
          (stA ↦ₛ shaStateBytes ((chunks64 (curBs.take (64 * (rem + 1)))).foldl
            sha256CompressState curSt)) ∗ stackFrame s 160) ∗ Frame) post oom) →
      SepWP P target_pc s
        (((curA ↦ₛ curBs) ∗ (stA ↦ₛ shaStateBytes curSt) ∗ stackFrame s 160) ∗ Frame) post oom := by
  intro rem; refine Nat.strongRecOn rem fun rem ih => ?_
  intro curA stA target_pc curBs curSt Frame s post oom
    hcl hpc hrun hsp_align hrem32 hbs_ge hbs_max hx23 hx24 hx22 hx21 hx20 hx19 hcont
  have hbs64 : 64 ≤ curBs.length := by omega
  apply sepWP_block_pure_seg (by decide : 2 < 7) hP (mid := haclMpl.base 2 + 72#64) hcl
    (PurePost := fun sm1 => sm1.sp = s.sp ∧ sm1.spAligned = true ∧ UpperCalleePreserved s sm1 ∧
      sm1.readReg64 .x0 = curA ∧ (sm1.readReg64 .x1).toNat = curBs.length ∧
      sm1.readReg64 .x2 = stA ∧ 8 ≤ (sm1.readReg64 .x3).toNat ∧ 8 ≤ (sm1.readReg64 .x19).toNat ∧
      sm1.readReg64 .x20 = stA ∧ (sm1.readReg64 .x21).toNat = curBs.length ∧
      sm1.readReg64 .x22 = curA ∧ sm1.readReg64 .x23 = s.readReg64 .x23 ∧
      sm1.readReg64 .x24 = BitVec.ofNat 64 ((curBs.length + 64) / 64))
    (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
  · intro m; rw [← haclPC2_eq_blockProgram, ← haclPl2_base]; rw [← haclPl2_base] at hpc
    have hrun0 : (s.setMem m).status = .Running := hrun
    have hb24 : (s.readReg64 (Reg.gpr 24#5) == 0#64) = false := by
      change (s.readReg64 .x24 == 0#64) = false; rw [hx24]; exact x24_pos_bne_zero hbs64 hbs_max
    wp_sym_steps 5
    exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨rfl, hsp_align, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩,
        rfl, hx21, rfl, hx19, hx19, hx20, hx21, hx22, rfl, hx24⟩, Entails.refl _⟩
  · intro sm1 hpc1 hrun1 hpf1 hcl1
      ⟨hsp1, hsp_align1, hup1, hx0_1, hx1_1, hx2_1, hx3_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
    have hstk1 : stackFrame s 160 = stackFrame sm1 160 := by simp [stackFrame, hsp1]
    rw [hstk1]
    apply step_bl_sha256Update (by decide : 2 < 7) hP hupd hcl1 hpc1 hrun1 hsp_align1
      fetch_block2_bl_update hx0_1 hx1_1 hbs64 hx2_1 hx3_1
    intro sm2 hpc2 hrun2 hsp2 hcs2 hpf2 hcl2; rw [← hstk1]
    have hpc2' : sm2.pc = haclPl2.base + 76#64 := by rw [hpc2, hpc1, ← haclPl2_base, BitVec.add_assoc]; rfl
    have hsp02 := hsp2.trans hsp1
    have hsp_align2 : sm2.spAligned = true := by unfold State.spAligned at hsp_align1 ⊢; rwa [hsp2]
    have hup02 := hup1.trans (UpperCalleePreserved.of_calleeSavedPreserved hcs2)
    have hpf02 := hpf1.trans hpf2
    have hx23_2 : sm2.readReg64 .x23 = BitVec.ofNat 64 (rem + 1) := (hcs2.2.2.2.2.1.trans hx23_1).trans hx23
    rcases rem with _ | rem'
    · have hx23_z : sm2.readReg64 (Reg.gpr 23#5) = 1#64 := hx23_2
      apply sepWP_block_pure_seg (by decide : 2 < 7) hP (mid := haclMpl.base 2 + 96#64) hcl2
        (PurePost := fun sm3 => sm3.sp = s.sp ∧ sm3.spAligned = true ∧ UpperCalleePreserved sm2 sm3)
        (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
      · intro m; rw [← haclPC2_eq_blockProgram, ← haclPl2_base]; clear hpc2
        have hrun0 : (sm2.setMem m).status = .Running := hrun2
        wp_sym_steps 5
        exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨hsp02, hsp_align2, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩⟩, Entails.refl _⟩
      · intro sm3 hpc3 hrun3 hpf3 hcl3 ⟨hsp3, hsp_align3, hup3⟩
        rw [show sha256CompressState curSt (curBs.take 64) =
            (chunks64 (curBs.take (64 * (0 + 1)))).foldl sha256CompressState curSt by
              rw [chunks64_exact_one (curBs.take 64) (List.length_take_of_le hbs64),
                  List.foldl_cons, List.foldl_nil]]
        exact hcont sm3 hpc3 hrun3 hsp3 hsp_align3 (hup02.trans hup3) (hpf02.trans hpf3) hcl3
    · have hx19_2 : 8 ≤ (sm2.readReg64 .x19).toNat := by rw [hcs2.1]; exact hx19_1
      have hx20_2 : sm2.readReg64 .x20 = stA := hcs2.2.1.trans hx20_1
      have hx21_2 : (sm2.readReg64 (Reg.gpr 21#5)).toNat = curBs.length := by
        change (sm2.readReg64 .x21).toNat = _; rw [hcs2.2.2.1]; exact hx21_1
      have hx22_z : sm2.readReg64 (Reg.gpr 22#5) = curA := hcs2.2.2.2.1.trans hx22_1
      have hx23_z : sm2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (rem' + 1 + 1) := hx23_2
      have hx24_z : sm2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 ((curBs.length + 64) / 64) :=
        hcs2.2.2.2.2.2.1.trans hx24_1
      rcases loop_step_arith hrem32 hbs64 hbs_max hx21_2 with ⟨hb_cbnz, hsub_cnt, hsub_div, hsub_len⟩
      apply sepWP_block_pure_seg (by decide : 2 < 7) hP (mid := haclMpl.base 2 + 52#64) hcl2
        (PurePost := fun sm3 => sm3.sp = s.sp ∧ sm3.spAligned = true ∧ UpperCalleePreserved sm2 sm3 ∧
          sm3.readReg64 .x23 = BitVec.ofNat 64 (rem' + 1) ∧
          sm3.readReg64 .x24 = BitVec.ofNat 64 (((curBs.drop 64).length + 64) / 64) ∧
          sm3.readReg64 .x22 = curA + 64#64 ∧ (sm3.readReg64 .x21).toNat = (curBs.drop 64).length ∧
          sm3.readReg64 .x20 = stA ∧ 8 ≤ (sm3.readReg64 .x19).toNat)
        (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
      · intro m; rw [← haclPC2_eq_blockProgram, ← haclPl2_base]; clear hpc2
        rw [hsub_cnt] at hb_cbnz
        have hrun0 : (sm2.setMem m).status = .Running := hrun2
        wp_sym_steps 5
        exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨by simp only [wp_norm]; exact hsp02,
            by simp only [State.spAligned, wp_norm]; exact hsp_align2,
            ⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩,
            by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
            by simp only [wp_norm]; exact hsub_len,
            by simp only [wp_norm]; exact hx20_2,
            by simp only [wp_norm]; exact hx19_2⟩, Entails.refl _⟩
      · intro sm3 hpc3 hrun3 hpf3 hcl3 ⟨hsp3, hsp_align3, hup3, hx23_3, hx24_3, hx22_3, hx21_3, hx20_3, hx19_3⟩
        have hstk3 : stackFrame s 160 = stackFrame sm3 160 := by simp [stackFrame, hsp3]
        have hsplit := pointsToBytes_take_drop curA 64 curBs hbs64
        refine sepWP_of_eq (ih rem' (Nat.lt_succ_self rem') (curA + 64#64) stA target_pc (curBs.drop 64)
          (sha256CompressState curSt (curBs.take 64)) ((curA ↦ₛ curBs.take 64) ∗ Frame) sm3
          hcl3 hpc3 hrun3 hsp_align3 (by omega) (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega) hx23_3 hx24_3 hx22_3 hx21_3 hx20_3 hx19_3 ?_)
          (by rw [hsplit, hstk3]; sep_ac_rfl)
        intro sm4 hpc4 hrun4 hsp4 hsp_align4 hup4 hpf4 hcl4
        exact sepWP_of_eq (hcont sm4 hpc4 hrun4 (hsp4.trans hsp3) hsp_align4
            ((hup02.trans hup3).trans hup4) ((hpf02.trans hpf3).trans hpf4) hcl4)
          (by rw [chunks64_take_succ_blocks curBs rem' hbs_ge, List.foldl_cons, ← hstk3, hsplit]
              sep_ac_rfl)

private theorem sha256UpdateNblocks_at [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hupd : subroutine_ok P (haclMpl.base 1) (withHaclPreserved haclMpl sha256UpdateRawSpec)) :
    subroutine_ok P (haclMpl.base 2) (sha256UpdateNblocksSpec haclMpl) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨len, blkA, bs, stA, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [sha256UpdateNblocksSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hcl, hlen32, hx0_w, hx1, hx2, hlen_le, hbs_max, hx3, hx4⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  have hpre_comm : ((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s0 224) =
      (stackFrame s0 224 ∗ ((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st))) := by sep_ac_rfl
  rw [hpre_comm]; by_cases hlt64 : len < 64
  · have hdiv0 : len / 64 = 0 := Nat.div_eq_of_lt hlt64
    apply sepWP_block_seg (by decide : 2 < 7) hP hcl (mid := s0.readReg64 Reg.lr)
      (Pre := stackFrame s0 224) (Post := fun _ => stackFrame s0 224)
      (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (Frame := (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st))
      (fun _ _ => rfl) (fun sm m => by cases sm; simp [CalleeSavedPreserved, calleeSavedVRegs])
    · intro m; rw [← haclPC2_eq_blockProgram]; rw [← haclPl2_base] at hpc
      have hrun0 : (s0.setMem m).status = .Running := hrun
      have hsp0 : (s0.setMem m).spAligned = true := hsp_align
      have hw23 : ((s0.readReg64 (Reg.gpr 0#5)).setWidth 32 >>> 6) = 0#32 := by
        have hl := lsr6_32_of_lt32 hlen32 hx0_w; rwa [hdiv0] at hl
      wp_conv_pre => rw [stackFrame_split_cells_eq s0 224 160 8 64]
      repeat (apply cells_sub_elim (by decide) (by decide); intro _)
      wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
      wp_sym_steps 12
      exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          by simp [wp_norm]⟩⟩, stackFrame224_entails s0 _ _ _ _ _ _ _ _⟩
    · intro sf hpc_f hrun_f hpf_f hcl_f ⟨hsp_f, hcs_f⟩
      refine SepWP.done hpc_f hrun_f ⟨fun hmem => ?_, hsp_f, hcs_f⟩
      rw [hdiv0, Nat.mul_zero, List.take_zero, chunks64_of_length_lt (by decide), List.foldl_nil,
          sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpf_f, hcl_f⟩, by rwa [← hpre_comm] at hmem⟩
  · let rem := len / 64 - 1
    have hdiv_succ : len / 64 = rem + 1 := by omega
    apply sepWP_block_seg (by decide : 2 < 7) hP hcl (mid := haclMpl.base 2 + 52#64)
      (Pre := stackFrame s0 224) (Post := fun _ => stackAt (s0.sp - 64#64) 160 ∗ savedRegs8 s0)
      (PurePost := fun sm1 => sm1.sp = s0.sp - 64#64 ∧ sm1.spAligned = true ∧
        UpperCalleePreserved s0 sm1 ∧ sm1.readReg64 .x23 = BitVec.ofNat 64 (rem + 1) ∧
        sm1.readReg64 .x24 = BitVec.ofNat 64 ((bs.length + 64) / 64) ∧ sm1.readReg64 .x22 = blkA ∧
        (sm1.readReg64 .x21).toNat = bs.length ∧ sm1.readReg64 .x20 = stA ∧
        8 ≤ (sm1.readReg64 .x19).toNat)
      (Frame := (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st))
      (fun _ _ => rfl) (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
    · intro m; rw [← haclPC2_eq_blockProgram, ← haclPl2_base]; rw [← haclPl2_base] at hpc
      have hrun0 : (s0.setMem m).status = .Running := hrun
      have hsp0 : (s0.setMem m).spAligned = true := hsp_align
      have hb_cbz : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 len) >>> 6) == 0#32) =
          false := by
        rw [beq_eq_false_iff_ne]; intro h; have htn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
          Nat.shiftRight_eq_div_pow] at htn; omega
      wp_conv_pre => rw [stackFrame_split_cells_eq s0 224 160 8 64]
      repeat (apply cells_sub_elim (by decide) (by decide); intro _)
      wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
      wp_sym_steps 13
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨rfl, State.spAligned_sub s0 64#64 hsp_align, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩,
          ?_, x24_init_eq hx2 hbs_max, rfl, hx2, rfl, hx4⟩, by dsimp only [savedRegs8]; exact Entails.refl _⟩
      simp only [wp_norm]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]; omega
    · intro sm1 hpc1 hrun1 hpf1 hcl1 ⟨hsp1, hsp_align1, hup1, hx23_1, hx24_1, hx22_1, hx21_1, hx20_1, hx19_1⟩
      have hstk1 : stackAt (s0.sp - 64#64) 160 = stackFrame sm1 160 := by simp [stackFrame, hsp1]
      refine sepWP_of_eq (nblocks_loop hP hupd rem blkA stA (s0.readReg64 Reg.lr) bs st (savedRegs8 s0) sm1
        hcl1 hpc1 hrun1 hsp_align1 (by omega) (by have := Nat.mul_div_le len 64; omega) hbs_max
        hx23_1 hx24_1 hx22_1 hx21_1 hx20_1 hx19_1 ?_) (by rw [hstk1]; sep_ac_rfl)
      intro sm2 hpc2 hrun2 hsp2 hsp_align2 hup2 hpf2 hcl2
      let st_done := (chunks64 (bs.take (64 * (rem + 1)))).foldl sha256CompressState st
      refine sepWP_of_eq (sepWP_block_seg (by decide : 2 < 7) hP hcl2 (mid := s0.readReg64 Reg.lr)
        (Pre := stackAt (s0.sp - 64#64) 160 ∗ savedRegs8 s0) (Post := fun _ => stackFrame s0 224)
        (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (Frame := (blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st_done))
        (fun _ _ => rfl) (fun sm m => by cases sm; simp [CalleeSavedPreserved, calleeSavedVRegs]) ?_ ?_)
        (by rw [← hstk1]; dsimp only [st_done]; sep_ac_rfl)
      · intro m; rw [← haclPC2_eq_blockProgram]; rw [← haclPl2_base] at hpc2
        have hrun0 : (sm2.setMem m).status = .Running := hrun2
        have hsp0 : (sm2.setMem m).spAligned = true := hsp_align2
        have hsp_m : sm2.sp = s0.sp - 64#64 := hsp2.trans hsp1
        dsimp only [savedRegs8]; wp_simp_pre only [sepConj_assoc]; wp_sym_steps 5
        have hup := hup1.trans hup2
        exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, hup.1, hup.2.1, hup.2.2.1,
            hup.2.2.2.1, rfl, by simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
              calleeSavedVRegs_writeReg64]; exact hup.2.2.2.2⟩⟩,
           stackFrame224_entails s0 _ _ _ _ _ _ _ _⟩
      · intro sf hpc_f hrun_f hpf_f hcl_f ⟨hsp_f, hcs_f⟩
        refine SepWP.done hpc_f hrun_f ⟨fun hmem => ?_, hsp_f, hcs_f⟩
        rw [hdiv_succ, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨(hpf1.trans hpf2).trans hpf_f, hcl_f⟩, ?_⟩
        rwa [show (stackFrame s0 224 ∗ ((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st_done))) =
          ((blkA ↦ₛ bs) ∗ (stA ↦ₛ shaStateBytes st_done) ∗ stackFrame s0 224) by sep_ac_rfl] at hmem

/-- Ambient-program `subroutine_ok` for Block `2` (`libcrux_sha2::hacl::sha256_update_nblocks`),
covering both `len < 64` (including `len = 0, bs = []`) and the `len / 64` multi-block loop. -/
theorem sha256UpdateNblocks_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec)) :
    subroutine_ok P (mpl.base 2) (sha256UpdateNblocksSpec mpl) :=
  @sha256UpdateNblocks_at ⟨mpl, hP.placeable⟩ P hP hupd

/-! ## 6. Block `3`: `libcrux_sha2::hacl::sha256_update_last` (`74` words) -/

private theorem fetch_block3_bl_update1 [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 3).fetch (haclMpl.base 3 + 164#64) =
      some (.bl ((haclMpl.base 1 - haclMpl.base 3) - 164#64)) := by
  rw [← haclPC3_eq_blockProgram, ← haclPl3_base]
  have hf : (haclPC3.rebase haclPl3.base (fun _ => none)).fetch (haclPl3.base + 164#64) =
      some (.bl ((haclPl3.ρ sha256UpdateSym - haclPl3.base) - 164#64)) := by
    dsimp only [sha256UpdateSym]; simp [wp_norm]
  rw [hf, ← haclPl3_rho, haclPl3_base, resolve_sha256Update haclMpl]

private theorem fetch_block3_bl_update2 [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 3).fetch (haclMpl.base 3 + 196#64) =
      some (.bl ((haclMpl.base 1 - haclMpl.base 3) - 196#64)) := by
  rw [← haclPC3_eq_blockProgram, ← haclPl3_base]
  have hf : (haclPC3.rebase haclPl3.base (fun _ => none)).fetch (haclPl3.base + 196#64) =
      some (.bl ((haclPl3.ρ sha256UpdateSym - haclPl3.base) - 196#64)) := by
    dsimp only [sha256UpdateSym]; simp [wp_norm]
  rw [hf, ← haclPl3_rho, haclPl3_base, resolve_sha256Update haclMpl]

private theorem step_bl_memcpy [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hmemcpy : subroutine_ok P (haclMpl.ρ memcpySym) haclMemcpySpec)
    {dst src target_pc : BitVec 64} {bs : List (BitVec 8)} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem) (hpc : s.pc = haclMpl.base 3 + 96#64)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hlen : bs.length < 2 ^ 64)
    (hnext : ∀ sf : State, sf.pc = s.pc + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → VmTracePreserved s sf → libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) post oom) :
    SepWP P target_pc s ((memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F) post oom := by
  have hf : (libcruxHmacLib.blockProgram haclMpl 3).fetch s.pc =
      some (.bl ((haclMpl.ρ memcpySym - haclMpl.base 3) - 96#64)) := by
    rw [hpc, ← haclPC3_eq_blockProgram, ← haclPl3_base]
    have h0 : (haclPC3.rebase haclPl3.base (fun _ => none)).fetch (haclPl3.base + 96#64) =
        some (.bl ((haclPl3.ρ memcpySym - haclPl3.base) - 96#64)) := by dsimp only [memcpySym]; simp [wp_norm]
    rw [h0, ← haclPl3_rho, haclPl3_base, resolve_memcpy haclMpl]
  refine sepWP_block_bl (by decide : 3 < 7) hP (by decide : 96 < _) hmemcpy (x := (dst, src, bs))
    (F := F) hcl hpc hrun hsp_align hf (by rw [hpc]; exact add_off_rel_target _ _ _) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R hm; dsimp only [haclMemcpySpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by simp only [wp_norm]; exact ⟨hx0, hx1, hx2, hlen⟩, by simpa only [sepConj_assoc] using hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f hcl_f; dsimp only [haclMemcpySpec]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hfs_bl, htr_bl, hvm_bl⟩
    exact hnext sf hpc_f hrun_f hsp_f (calleeSavedPreserved_of_bl hcs_f)
      ((VmTracePreserved.of_pf (processFieldsPreserved_execInst_bl _ s)).trans ⟨hvm_bl, htr_bl, hfs_bl⟩) hcl_f

private theorem stackFrame352_entails_of_bytes (s0 : State) {bs : List (BitVec 8)}
    (hbs : bs.length = 128) (v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64) :
    (stackAt (s0.sp - 192#64) 160 ∗ ((s0.sp - 192#64) ↦ₛ bs) ∗
     ((s0.sp - 64#64) ↦₆₄ v1) ∗ ((s0.sp - 56#64) ↦₆₄ v2) ∗ ((s0.sp - 48#64) ↦₆₄ v3) ∗
     ((s0.sp - 40#64) ↦₆₄ v4) ∗ ((s0.sp - 32#64) ↦₆₄ v5) ∗ ((s0.sp - 24#64) ↦₆₄ v6) ∗
     ((s0.sp - 16#64) ↦₆₄ v7) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ⊢ stackFrame s0 352 := by
  have hreg : stackAt (s0.sp - 64#64) 288 =
      stackAt (s0.sp - 192#64) 160 ∗ memRegion (s0.sp - 192#64) 128 := by
    have hr := stackAt_region (s0.sp - 64#64) 160 128 (by decide)
    rwa [show s0.sp - 64#64 - BitVec.ofNat 64 128 = s0.sp - 192#64 by bv_omega] at hr
  rw [stackFrame_split_cells_eq s0 352 288 8 64, hreg, sepConj_assoc]
  exact sepConj_mono_right (Entails.trans
    (sepConj_mono_left (pointsToBytes_entails_memRegion_of_length hbs))
    (sepConj_mono_right (cells8_entails s0 v1 v2 v3 v4 v5 v6 v7 v8)))

private theorem zeroCells4_eq_rep32 (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 24#64) ↦₆₄ 0#64)) =
    (a ↦ₛ List.replicate 32 0#8) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl, pointsToBytes_replicate_split,
      pointsToBytes_replicate_split_off, pointsToBytes_replicate_split_off,
      pointsToBytes_replicate8_zero, pointsToBytes_replicate8_zero,
      pointsToBytes_replicate8_zero, pointsToBytes_replicate8_zero]

private theorem zeroCells16_eq_rep128 (sp : BitVec 64) :
    (((sp - 192#64) ↦₆₄ 0#64) ∗ ((sp - 184#64) ↦₆₄ 0#64) ∗ ((sp - 176#64) ↦₆₄ 0#64) ∗
     ((sp - 168#64) ↦₆₄ 0#64) ∗ ((sp - 160#64) ↦₆₄ 0#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
     ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗ ((sp - 128#64) ↦₆₄ 0#64) ∗
     ((sp - 120#64) ↦₆₄ 0#64) ∗ ((sp - 112#64) ↦₆₄ 0#64) ∗ ((sp - 104#64) ↦₆₄ 0#64) ∗
     ((sp - 96#64) ↦₆₄ 0#64) ∗ ((sp - 88#64) ↦₆₄ 0#64) ∗ ((sp - 80#64) ↦₆₄ 0#64) ∗
     ((sp - 72#64) ↦₆₄ 0#64)) = ((sp - 192#64) ↦ₛ List.replicate 128 0#8) := by
  rw [show (128 : Nat) = 32 + (32 + (32 + 32)) by rfl, pointsToBytes_replicate_split,
      pointsToBytes_replicate_split_off, pointsToBytes_replicate_split_off,
      ← zeroCells4_eq_rep32, ← zeroCells4_eq_rep32, ← zeroCells4_eq_rep32, ← zeroCells4_eq_rep32]
  have e (a k : BitVec 64) : sp - a + k = sp - (a - k) := by bv_omega
  simp only [Nat.reduceAdd, e, BitVec.reduceSub, sepConj_assoc]

private theorem unpack64_rev64 (w : BitVec 64) : unpack64 (rev64 w) = toBEBytes 8 w := by
  unfold unpack64 toBEBytes
  change [(rev64 w).extractLsb' 0 8, (rev64 w).extractLsb' 8 8, (rev64 w).extractLsb' 16 8,
          (rev64 w).extractLsb' 24 8, (rev64 w).extractLsb' 32 8, (rev64 w).extractLsb' 40 8,
          (rev64 w).extractLsb' 48 8, (rev64 w).extractLsb' 56 8] =
         [w.extractLsb' 56 8, w.extractLsb' 48 8, w.extractLsb' 40 8, w.extractLsb' 32 8,
          w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]
  unfold rev64; repeat (congr 1; · bv_slice)

private theorem unpack64_rev64_lsl3 {x22 : BitVec 64} {totlen : Nat} (hx : x22.toNat = totlen) :
    unpack64 (rev64 (x22 <<< 3)) = toBEBytes 8 (BitVec.ofNat 64 (8 * totlen)) := by
  rw [show x22 <<< 3 = BitVec.ofNat 64 (8 * totlen) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hx, Nat.shiftLeft_eq]; rw [Nat.mul_comm],
    unpack64_rev64]

private theorem rep_tail_lt56 (bufA : BitVec 64) {remLen : Nat} (h56 : remLen < 56) :
    ((bufA + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (128 - remLen) 0#8) =
    (((bufA + BitVec.ofNat 64 remLen) ↦₈ 0#8) ∗
     ((bufA + BitVec.ofNat 64 (remLen + 1)) ↦ₛ List.replicate (55 - remLen) 0#8) ∗
     ((bufA + 56#64) ↦₆₄ 0#64) ∗ ((bufA + 64#64) ↦ₛ List.replicate 64 0#8)) := by
  rw [show 128 - remLen = 1 + ((55 - remLen) + (8 + 64)) by omega, pointsToBytes_replicate_split_off,
      pointsToBytes_replicate_split_off, pointsToBytes_replicate_split_off,
      show List.replicate 1 0#8 = [0#8] from rfl, pointsToBytes_singleton,
      show remLen + 1 + (55 - remLen) = 56 by omega, show (56 : Nat) + 8 = 64 by rfl,
      pointsToBytes_replicate8_zero]

private theorem pad_merge_lt56 (bufA : BitVec 64) {totlen : Nat} {x22 : BitVec 64}
    (hx22 : x22.toNat = totlen) {rem : List (BitVec 8)} (h56 : rem.length < 56) :
    ((bufA ↦ₛ rem) ∗ ((bufA + BitVec.ofNat 64 rem.length) ↦₈ 0x80#8) ∗
     ((bufA + BitVec.ofNat 64 (rem.length + 1)) ↦ₛ List.replicate (55 - rem.length) 0#8) ∗
     ((bufA + 56#64) ↦₆₄ rev64 (x22 <<< 3))) = (bufA ↦ₛ haclPadTail totlen rem) := by
  unfold haclPadTail; simp only [h56, ↓reduceIte]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_singleton,
      pointsTo64_eq_pointsToBytes, unpack64_rev64_lsl3 hx22,
      show bufA + BitVec.ofNat 64 (rem ++ [0x80#8]).length = bufA + BitVec.ofNat 64 (rem.length + 1) by simp,
      show bufA + BitVec.ofNat 64 (rem ++ [0x80#8] ++ List.replicate (55 - rem.length) 0#8).length =
        bufA + 56#64 by rw [List.length_append, List.length_append, List.length_singleton,
          List.length_replicate, show rem.length + 1 + (55 - rem.length) = 56 by omega]]
  simp only [sepConj_assoc]

private theorem rep_tail_ge56 (bufA : BitVec 64) {remLen : Nat} (hlo : 56 ≤ remLen) (hhi : remLen ≤ 64) :
    ((bufA + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (128 - remLen) 0#8) =
    (((bufA + BitVec.ofNat 64 remLen) ↦₈ 0#8) ∗
     ((bufA + BitVec.ofNat 64 (remLen + 1)) ↦ₛ List.replicate (119 - remLen) 0#8) ∗
     ((bufA + 120#64) ↦₆₄ 0#64)) := by
  rw [show 128 - remLen = 1 + ((119 - remLen) + 8) by omega, pointsToBytes_replicate_split_off,
      pointsToBytes_replicate_split_off, show List.replicate 1 0#8 = [0#8] from rfl,
      pointsToBytes_singleton, show remLen + 1 + (119 - remLen) = 120 by omega,
      pointsToBytes_replicate8_zero]

private theorem pad_merge_ge56 (bufA : BitVec 64) {totlen : Nat} {x22 : BitVec 64}
    (hx22 : x22.toNat = totlen) {rem : List (BitVec 8)} (hlo : 56 ≤ rem.length) (hhi : rem.length ≤ 64) :
    ((bufA ↦ₛ rem) ∗ ((bufA + BitVec.ofNat 64 rem.length) ↦₈ 0x80#8) ∗
     ((bufA + BitVec.ofNat 64 (rem.length + 1)) ↦ₛ List.replicate (119 - rem.length) 0#8) ∗
     ((bufA + 120#64) ↦₆₄ rev64 (x22 <<< 3))) = (bufA ↦ₛ haclPadTail totlen rem) := by
  have hnot : ¬ rem.length < 56 := by omega
  unfold haclPadTail; simp only [hnot, ↓reduceIte]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_singleton,
      pointsTo64_eq_pointsToBytes, unpack64_rev64_lsl3 hx22,
      show bufA + BitVec.ofNat 64 (rem ++ [0x80#8]).length = bufA + BitVec.ofNat 64 (rem.length + 1) by simp,
      show bufA + BitVec.ofNat 64 (rem ++ [0x80#8] ++ List.replicate (119 - rem.length) 0#8).length =
        bufA + 120#64 by rw [List.length_append, List.length_append, List.length_singleton,
          List.length_replicate, show rem.length + 1 + (119 - rem.length) = 120 by omega]]
  simp only [sepConj_assoc]

private theorem cmn_w23_lt56 {remLen : Nat} (h56 : remLen < 56) :
    BitVec.ule (BitVec.ofNat 32 remLen - 56#32) (BitVec.ofNat 32 remLen - 56#32 + 65#32) = false ∧
    BitVec.ult (BitVec.ofNat 32 remLen - 56#32 + 65#32) (BitVec.ofNat 32 remLen - 56#32) = true := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, decide_eq_false_iff_not, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

private theorem cmn_w23_ge56 {remLen : Nat} (hlo : 56 ≤ remLen) (hhi : remLen ≤ 64) :
    BitVec.ule (BitVec.ofNat 32 remLen - 56#32) (BitVec.ofNat 32 remLen - 56#32 + 65#32) = true ∧
    BitVec.ult (BitVec.ofNat 32 remLen - 56#32 + 65#32) (BitVec.ofNat 32 remLen - 56#32) = false := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, decide_eq_false_iff_not, decide_eq_true_eq,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

private theorem epilogue_block3 [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    {s0 sm : State} {remA stA : BitVec 64} {slice bs128 : List (BitVec 8)} {st_done : ShaState} {R : SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl sm.mem) (hpc : sm.pc = haclMpl.base 3 + 200#64)
    (hrun : sm.status = .Running) (hsp_align : sm.spAligned = true) (hsp : sm.sp = s0.sp - 192#64)
    (hup : UpperCalleePreserved s0 sm) (hvm : VmTracePreserved s0 sm) (hbs128 : bs128.length = 128) :
    SepWP P (s0.readReg64 Reg.lr) sm
      ((stackAt (s0.sp - 192#64) 160 ∗ ((s0.sp - 192#64) ↦ₛ bs128) ∗ savedRegs8 s0) ∗
       ((remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st_done)))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (((⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
          (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st_done) ∗ stackFrame s0 352) ∗
          ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝) ∗ R)) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  apply sepWP_block_seg (by decide : 3 < 7) hP hcl (mid := s0.readReg64 Reg.lr)
    (Pre := stackAt (s0.sp - 192#64) 160 ∗ ((s0.sp - 192#64) ↦ₛ bs128) ∗ savedRegs8 s0)
    (Post := fun _ => stackFrame s0 352) (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (Frame := (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st_done))
    (fun _ _ => rfl) (fun sm' m => by cases sm'; simp [CalleeSavedPreserved, calleeSavedVRegs])
  · intro m; rw [← haclPC3_eq_blockProgram]; rw [← haclPl3_base] at hpc
    have hrun0 : (sm.setMem m).status = .Running := hrun
    have hsp0 : (sm.setMem m).spAligned = true := hsp_align
    dsimp only [savedRegs8]; wp_simp_pre only [sepConj_assoc]; wp_sym_steps 6
    exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
        rfl, by simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]
                exact hup.2.2.2.2⟩⟩, stackFrame352_entails_of_bytes s0 hbs128 _ _ _ _ _ _ _ _⟩
  · intro sf hpc_f hrun_f hpf_f hcl_f ⟨hsp_f, hcs_f⟩
    refine SepWP.done hpc_f hrun_f ⟨fun hmem => ?_, hsp_f, hcs_f⟩
    have hvmt := hvm.trans (VmTracePreserved.of_pf hpf_f)
    rw [show (((⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
          (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st_done) ∗ stackFrame s0 352) ∗
          ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝) ∗ R) =
        ⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
        ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
        ((stackFrame s0 352 ∗ ((remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st_done))) ∗ R) by sep_ac_rfl,
        satisfies_pure_sepConj]
    exact ⟨⟨hvmt.1, hcl_f⟩, by rw [satisfies_pure_sepConj]; exact ⟨hvmt.2, hmem⟩⟩

set_option maxHeartbeats 400000 in
private theorem sha256UpdateLast_at [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hupd : subroutine_ok P (haclMpl.base 1) (withHaclPreserved haclMpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (haclMpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (haclMpl.base 3) (withTraceEq (sha256UpdateLastSpec haclMpl)) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨totlen, remLen, remA, slice, stA, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [withTraceEq, sha256UpdateLastSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hcl, hx0, hrem64, hx1_w, hx2, hx3, hrem_le, hx4, hx5⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  let bufA := s0.sp - 192#64
  let rem := slice.take remLen
  have hrem_len : rem.length = remLen := List.length_take_of_le hrem_le
  refine sepWP_of_eq (sepWP_block_seg (by decide : 3 < 7) hP hcl (mid := haclMpl.base 3 + 96#64)
    (Pre := stackFrame s0 352)
    (Post := fun _ => stackAt bufA 160 ∗ (bufA ↦ₛ List.replicate 128 0#8) ∗ savedRegs8 s0)
    (PurePost := fun sm1 => sm1.sp = bufA ∧ sm1.spAligned = true ∧ UpperCalleePreserved s0 sm1 ∧
      sm1.readReg64 .x0 = bufA ∧ sm1.readReg64 .x1 = remA ∧
      sm1.readReg64 .x2 = BitVec.ofNat 64 remLen ∧ 8 ≤ (sm1.readReg64 .x19).toNat ∧
      sm1.readReg64 .x20 = stA ∧ sm1.readReg64 .x21 = BitVec.ofNat 64 remLen ∧
      (sm1.readReg64 .x22).toNat = totlen ∧ sm1.readReg64 .x23 = BitVec.ofNat 64 remLen ∧
      sm1.readReg64 .x24 = bufA)
    (Frame := (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st))
    (fun _ _ => rfl) (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned]) ?_ ?_)
    (by sep_ac_rfl)
  · intro m; rw [← haclPC3_eq_blockProgram, ← haclPl3_base]; rw [← haclPl3_base] at hpc
    have hrun0 : (s0.setMem m).status = .Running := hrun
    have hsp0 : (s0.setMem m).spAligned = true := hsp_align
    have hb_hs129 : BitVec.ule 129#32 (BitVec.ofNat 32 remLen) = false := by
      rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; simp only [BitVec.toNat_ofNat]; omega
    have hrem_bv : BitVec.setWidth 64 (BitVec.ofNat 32 remLen) = BitVec.ofNat 64 remLen := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hb_lo_len : BitVec.ult (s0.readReg64 (Reg.gpr 3#5)) (BitVec.ofNat 64 remLen) = false := by
      rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]; simp only [BitVec.toNat_ofNat]
      change ¬ (s0.readReg64 .x3).toNat < _; omega
    wp_conv_pre => rw [stackFrame_split_cells_eq s0 352 160 24 192]
    repeat (apply cells_sub_elim (by decide) (by decide); intro _)
    wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    wp_sym_steps 24
    exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨rfl, State.spAligned_sub s0 192#64 hsp_align,
        ⟨rfl, rfl, rfl, rfl, by simp [calleeSavedVRegs, wp_norm]⟩,
        rfl, rfl, rfl, hx5, rfl, rfl, hx0, hrem_bv, rfl⟩,
       by dsimp only [bufA, savedRegs8]; rw [← zeroCells16_eq_rep128 s0.sp]
          simp only [sepConj_assoc]; exact Entails.refl _⟩
  · intro sm1 hpc1 hrun1 hpf1 hcl1
      ⟨hsp1, hsp_align1, hup1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
    have hbuf_split : (bufA ↦ₛ List.replicate 128 0#8) =
        ((bufA ↦ₛ List.replicate remLen 0#8) ∗
         ((bufA + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (128 - remLen) 0#8)) := by
      conv => lhs; rw [show (128 : Nat) = remLen + (128 - remLen) by omega]
      exact pointsToBytes_replicate_split bufA remLen (128 - remLen) 0#8
    have hslice_split := pointsToBytes_take_drop remA remLen slice hrem_le
    let mcFrame : SepProp :=
      stackAt bufA 160 ∗ ((bufA + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (128 - remLen) 0#8) ∗
      savedRegs8 s0 ∗ ((remA + BitVec.ofNat 64 remLen) ↦ₛ slice.drop remLen) ∗ (stA ↦ₛ shaStateBytes st)
    have hent : (bufA ↦ₛ List.replicate remLen 0#8) ⊢ memRegion bufA rem.length :=
      pointsToBytes_entails_memRegion_of_length (by rw [List.length_replicate, hrem_len])
    refine sepWP_of_eq (SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_left hent))
      (step_bl_memcpy hP hmemcpy (dst := bufA) (src := remA) (bs := rem) (F := mcFrame)
        hcl1 hpc1 hrun1 hsp_align1 hx0_1 hx1_1 (by rw [hrem_len]; exact hx2_1) (by rw [hrem_len]; omega) ?_))
      (by dsimp only [rem, mcFrame]; rw [hbuf_split, hslice_split]; sep_ac_rfl)
    intro sm2 hpc2 hrun2 hsp2 hcs2 hvm2 hcl2
    have hpc2' : sm2.pc = haclPl3.base + 100#64 := by rw [hpc2, hpc1, ← haclPl3_base, BitVec.add_assoc]; rfl
    have hsp2' : sm2.sp = bufA := hsp2.trans hsp1
    have hsp_align2 : sm2.spAligned = true := by unfold State.spAligned at hsp_align1 ⊢; rwa [hsp2]
    have hup02 := hup1.trans (UpperCalleePreserved.of_calleeSavedPreserved hcs2)
    have hvm02 := (VmTracePreserved.of_pf hpf1).trans hvm2
    have hx19_2 : 8 ≤ (sm2.readReg64 .x19).toNat := by rw [hcs2.1]; exact hx19_1
    have hx20_2 : sm2.readReg64 .x20 = stA := hcs2.2.1.trans hx20_1
    have hx22_2 : (sm2.readReg64 .x22).toNat = totlen := by rw [hcs2.2.2.2.1]; exact hx22_1
    have hbeq128 : ((BitVec.ofNat 64 remLen).setWidth 32 == 128#32) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have htn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htn; omega
    let pad := haclPadTail totlen rem
    let buf128 := if remLen < 56 then pad ++ List.replicate 64 0#8 else pad
    have hbuf128_len : buf128.length = 128 := by
      dsimp only [buf128, pad]; split_ifs with h56
      · rw [List.length_append, haclPadTail_length_lt56 totlen (by omega), List.length_replicate]
      · exact haclPadTail_length_ge56 totlen (by omega) (by omega)
    refine sepWP_of_eq (sepWP_block_seg (by decide : 3 < 7) hP hcl2 (mid := haclMpl.base 3 + 164#64)
      (Pre := (bufA ↦ₛ rem) ∗ ((bufA + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (128 - remLen) 0#8))
      (Post := fun _ => (bufA ↦ₛ buf128))
      (PurePost := fun sm3 => sm3.sp = bufA ∧ sm3.spAligned = true ∧ UpperCalleePreserved sm2 sm3 ∧
        sm3.readReg64 .x0 = bufA ∧ (sm3.readReg64 .x1).toNat = 64 ∧ sm3.readReg64 .x2 = stA ∧
        8 ≤ (sm3.readReg64 .x3).toNat ∧ 8 ≤ (sm3.readReg64 .x19).toNat ∧ sm3.readReg64 .x20 = stA ∧
        (sm3.readReg64 .x23).setWidth 32 = BitVec.ofNat 32 remLen - 56#32)
      (Frame := stackAt bufA 160 ∗ savedRegs8 s0 ∗ (remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st))
      (fun _ _ => rfl) (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned]) ?_ ?_)
      (by dsimp only [rem, mcFrame]; rw [hslice_split]; sep_ac_rfl)
    · intro m; rw [← haclPC3_eq_blockProgram, ← haclPl3_base]; clear hpc2
      have hrun0 : (sm2.setMem m).status = .Running := hrun2
      have hx23_z : sm2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 remLen := hcs2.2.2.2.2.1.trans hx23_1
      have hx24_z : sm2.readReg64 (Reg.gpr 24#5) = bufA := hcs2.2.2.2.2.2.1.trans hx24_1
      have hx21_z : sm2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 remLen := hcs2.2.2.1.trans hx21_1
      have hx20_z : sm2.readReg64 (Reg.gpr 20#5) = stA := hx20_2
      have hrem32 : (BitVec.ofNat 64 remLen).setWidth 32 = BitVec.ofNat 32 remLen := by
        apply BitVec.eq_of_toNat_eq; simp
      have hw23_sub : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 remLen - 56#32)) =
          BitVec.ofNat 32 remLen - 56#32 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      by_cases h56 : remLen < 56
      · wp_conv_pre => rw [rep_tail_lt56 bufA h56]
        wp_sym_steps 9; rw [(cmn_w23_lt56 h56).1]; simp only [Bool.false_eq_true, ↓reduceIte]; wp_sym_steps 7
        refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨hsp2', hsp_align2, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩,
            rfl, rfl, rfl, hx19_2, hx19_2, hx20_2, hw23_sub⟩, ?_⟩
        dsimp only [buf128, pad]; simp only [h56, ↓reduceIte]
        rw [pointsToBytes_append, haclPadTail_length_lt56 totlen (by omega), ← hrem_len,
            ← pad_merge_lt56 bufA hx22_2 (by omega)]
        simp only [sepConj_assoc]; exact Entails.refl _
      · have hge56 : 56 ≤ remLen := by omega
        wp_conv_pre => rw [rep_tail_ge56 bufA hge56 hrem64]
        wp_sym_steps 9; rw [(cmn_w23_ge56 hge56 hrem64).1]; simp only [↓reduceIte]; wp_sym_steps 7
        refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨hsp2', hsp_align2, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩,
            rfl, rfl, rfl, hx19_2, hx19_2, hx20_2, hw23_sub⟩, ?_⟩
        dsimp only [buf128, pad]; simp only [h56, ↓reduceIte]
        rw [← hrem_len, pad_merge_ge56 bufA hx22_2 (by omega) (by omega)]; exact Entails.refl _
    · intro sm3 hpc3 hrun3 hpf3 hcl3
        ⟨hsp3, hsp_align3, hup3, hx0_3, hx1_3, hx2_3, hx3_3, hx19_3, hx20_3, hx23_3⟩
      have hstk3 : stackAt bufA 160 = stackFrame sm3 160 := by simp [stackFrame, hsp3]
      have h64_128 : 64 ≤ buf128.length := by rw [hbuf128_len]; decide
      have hbuf_split2 := pointsToBytes_take_drop bufA 64 buf128 h64_128
      have htake_len : (buf128.take 64).length = 64 := List.length_take_of_le h64_128
      have hdrop_len : (buf128.drop 64).length = 64 := by rw [List.length_drop, hbuf128_len]
      refine sepWP_of_eq (step_bl_sha256Update (by decide : 3 < 7) hP hupd
        (blkA := bufA) (bs := buf128.take 64) (stA := stA) (st := st)
        (F := ((bufA + 64#64) ↦ₛ buf128.drop 64) ∗ savedRegs8 s0 ∗ (remA ↦ₛ slice))
        hcl3 hpc3 hrun3 hsp_align3 fetch_block3_bl_update1
        hx0_3 (by rw [htake_len]; exact hx1_3) (le_of_eq htake_len.symm) hx2_3 hx3_3 ?_)
        (by rw [hbuf_split2, hstk3]; sep_ac_rfl)
      intro sm4 hpc4 hrun4 hsp4 hcs4 hpf4 hcl4
      have hpc4' : sm4.pc = haclPl3.base + 168#64 := by rw [hpc4, hpc3, ← haclPl3_base, BitVec.add_assoc]; rfl
      have hsp_align4 : sm4.spAligned = true := by unfold State.spAligned at hsp_align3 ⊢; rwa [hsp4]
      have hup04 := (hup02.trans hup3).trans (UpperCalleePreserved.of_calleeSavedPreserved hcs4)
      have hvm04 := (hvm02.trans (VmTracePreserved.of_pf hpf3)).trans (VmTracePreserved.of_pf hpf4)
      let st1 := sha256CompressState st ((buf128.take 64).take 64)
      by_cases h56 : remLen < 56
      · apply sepWP_block_pure_seg (by decide : 3 < 7) hP (mid := haclMpl.base 3 + 200#64) hcl4
          (PurePost := fun sm5 => sm5.sp = bufA ∧ sm5.spAligned = true ∧ UpperCalleePreserved sm4 sm5)
          (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
        · intro m; rw [← haclPC3_eq_blockProgram, ← haclPl3_base]; clear hpc4
          have hrun0 : (sm4.setMem m).status = .Running := hrun4
          have hx23_z : (sm4.readReg64 (Reg.gpr 23#5)).setWidth 32 = BitVec.ofNat 32 remLen - 56#32 := by
            change (sm4.readReg64 .x23).setWidth 32 = _; rw [hcs4.2.2.2.2.1]; exact hx23_3
          have hb_hs := (cmn_w23_lt56 h56).2
          wp_sym_steps 2
          exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun4])
            ⟨⟨hsp4.trans hsp3, hsp_align4, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩⟩, Entails.refl _⟩
        · intro sm5 hpc5 hrun5 hpf5 hcl5 ⟨hsp5, hsp_align5, hup5⟩
          have hpad_len : pad.length = 64 := haclPadTail_length_lt56 totlen (by omega)
          have hst_eq : st1 = haclUpdateLastState sha256CompressState totlen rem st := by
            dsimp only [st1, buf128]; simp only [h56, ↓reduceIte]
            rw [List.take_take, Nat.min_self, List.take_append_of_le_length (le_of_eq hpad_len.symm),
                List.take_of_length_le (le_of_eq hpad_len)]
            have hrem56 : rem.length < 56 := by omega
            dsimp only [pad, haclUpdateLastState]; simp only [hrem56, ↓reduceIte]
          exact sepWP_of_eq (epilogue_block3 hP (s0 := s0) (remA := remA) (stA := stA) (slice := slice)
            (bs128 := buf128) (st_done := haclUpdateLastState sha256CompressState totlen rem st)
            hcl5 hpc5 hrun5 hsp_align5 hsp5 (hup04.trans hup5)
            (hvm04.trans (VmTracePreserved.of_pf hpf5)) hbuf128_len)
            (by dsimp only [st1] at hst_eq; rw [← hstk3, hst_eq, hbuf_split2]; sep_ac_rfl)
      · have hge56 : 56 ≤ remLen := by omega
        apply sepWP_block_pure_seg (by decide : 3 < 7) hP (mid := haclMpl.base 3 + 196#64) hcl4
          (PurePost := fun sm5 => sm5.sp = bufA ∧ sm5.spAligned = true ∧ UpperCalleePreserved sm4 sm5 ∧
            sm5.readReg64 .x0 = bufA + 64#64 ∧ (sm5.readReg64 .x1).toNat = 64 ∧
            sm5.readReg64 .x2 = stA ∧ 8 ≤ (sm5.readReg64 .x3).toNat)
          (fun sm m => by cases sm; simp [UpperCalleePreserved, State.spAligned])
        · intro m; rw [← haclPC3_eq_blockProgram, ← haclPl3_base]; clear hpc4
          have hrun0 : (sm4.setMem m).status = .Running := hrun4
          have hx23_z : (sm4.readReg64 (Reg.gpr 23#5)).setWidth 32 = BitVec.ofNat 32 remLen - 56#32 := by
            change (sm4.readReg64 .x23).setWidth 32 = _; rw [hcs4.2.2.2.2.1]; exact hx23_3
          have hx20_z : sm4.readReg64 (Reg.gpr 20#5) = stA := hcs4.2.1.trans hx20_3
          have hb_hs := (cmn_w23_ge56 hge56 hrem64).2
          wp_sym_steps 7
          exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun4])
            ⟨⟨hsp4.trans hsp3, hsp_align4, ⟨rfl, rfl, rfl, rfl, by simp [wp_norm]⟩,
              rfl, rfl, rfl, by rw [hcs4.1]; exact hx19_3⟩, Entails.refl _⟩
        · intro sm5 hpc5 hrun5 hpf5 hcl5 ⟨hsp5, hsp_align5, hup5, hx0_5, hx1_5, hx2_5, hx3_5⟩
          have hstk5 : stackFrame sm3 160 = stackFrame sm5 160 := by simp [stackFrame, hsp3, hsp5]
          refine sepWP_of_eq (step_bl_sha256Update (by decide : 3 < 7) hP hupd
            (blkA := bufA + 64#64) (bs := buf128.drop 64) (stA := stA) (st := st1)
            (F := (bufA ↦ₛ buf128.take 64) ∗ savedRegs8 s0 ∗ (remA ↦ₛ slice))
            hcl5 hpc5 hrun5 hsp_align5 fetch_block3_bl_update2
            hx0_5 (by rw [hdrop_len]; exact hx1_5) (le_of_eq hdrop_len.symm) hx2_5 hx3_5 ?_)
            (by rw [hstk5]; sep_ac_rfl)
          intro sm6 hpc6 hrun6 hsp6 hcs6 hpf6 hcl6
          have hst_eq : sha256CompressState st1 ((buf128.drop 64).take 64) =
              haclUpdateLastState sha256CompressState totlen rem st := by
            rw [List.take_of_length_le (l := buf128.drop 64) (le_of_eq hdrop_len)]
            dsimp only [st1]; rw [List.take_take, Nat.min_self]
            dsimp only [buf128]; simp only [h56, ↓reduceIte]
            have hrem56 : ¬ rem.length < 56 := by omega
            dsimp only [pad, haclUpdateLastState]; simp only [hrem56, ↓reduceIte]
          exact sepWP_of_eq (epilogue_block3 hP (s0 := s0) (remA := remA) (stA := stA) (slice := slice)
            (bs128 := buf128) (st_done := haclUpdateLastState sha256CompressState totlen rem st)
            hcl6 (by rw [hpc6, hpc5, BitVec.add_assoc]; rfl) hrun6
            (by unfold State.spAligned at hsp_align5 ⊢; rwa [hsp6]) (hsp6.trans hsp5)
            ((hup04.trans hup5).trans (UpperCalleePreserved.of_calleeSavedPreserved hcs6))
            ((hvm04.trans (VmTracePreserved.of_pf hpf5)).trans (VmTracePreserved.of_pf hpf6)) hbuf128_len)
            (by rw [← hstk5, ← hstk3, hst_eq, hbuf_split2]; sep_ac_rfl)

/-- Ambient-program `subroutine_ok` for Block `3` (`libcrux_sha2::hacl::sha256_update_last`)
augmented with `sf.trace = s0.trace` (`withTraceEq`); see `sha256UpdateLast_subroutineOk` for the
`352`-byte stack-budget breakdown. -/
theorem sha256UpdateLast_withTraceEq_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (mpl.base 3) (withTraceEq (sha256UpdateLastSpec mpl)) :=
  @sha256UpdateLast_at ⟨mpl, hP.placeable⟩ P hP hupd hmemcpy

/-- Ambient-program `subroutine_ok` for Block `3` (`libcrux_sha2::hacl::sha256_update_last`).

Stack budget (`352` B in `sha256UpdateLastSpec`): block `3` allocates `192` B locally
(`sub sp, sp, #192`: a `128`-B padding buffer at `[sp, sp+128)` and a `64`-B callee-saved spill
region at `[sp+128, sp+192)`). Its callees below `sp` require `max(0, 160) = 160` B
(`haclMemcpySpec` uses `0` B of caller stack under both `allocMemcpyVmSpec` and `MuslMemOps`
`stdMemcpySpec`; `sha256UpdateRawSpec` uses `160` B), giving `192 + 160 = 352` B. -/
theorem sha256UpdateLast_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (mpl.base 3) (sha256UpdateLastSpec mpl) :=
  subroutine_ok_of_withTraceEq (sha256UpdateLast_withTraceEq_subroutineOk hP hupd hmemcpy)

/-! ## 7. Block `5`: `libcrux_sha2::hacl::hash_256` (`101` words) & `HaclSubroutines` Bundle -/

private theorem fetch_block5_bl_update [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 5).fetch (haclMpl.base 5 + 168#64) =
      some (.bl ((haclMpl.base 1 - haclMpl.base 5) - 168#64)) := by
  rw [← haclPC5_eq_blockProgram, ← haclPl5_base]
  have hf : (haclPC5.rebase haclPl5.base (fun _ => none)).fetch (haclPl5.base + 168#64) =
      some (.bl ((haclPl5.ρ sha256UpdateSym - haclPl5.base) - 168#64)) := by
    dsimp only [sha256UpdateSym]; simp [wp_norm]
  rw [hf, ← haclPl5_rho, haclPl5_base, resolve_sha256Update haclMpl]

private def TopCalleePreserved (s0 sf : State) : Prop :=
  sf.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sf = calleeSavedVRegs s0
private theorem TopCalleePreserved.trans {s0 s1 s2 : State}
    (h01 : TopCalleePreserved s0 s1) (h12 : TopCalleePreserved s1 s2) : TopCalleePreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.trans h01.2⟩
private theorem TopCalleePreserved.of_calleeSavedPreserved {s0 sf : State}
    (h : CalleeSavedPreserved s0 sf) : TopCalleePreserved s0 sf :=
  ⟨h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem step_bl_sha256UpdateLast [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hlast : subroutine_ok P (haclMpl.base 3) (withTraceEq (sha256UpdateLastSpec haclMpl)))
    {totlen remLen : Nat} {remA stA target_pc : BitVec 64} {slice : List (BitVec 8)} {st : ShaState}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : libcruxHmacLib.CodeLoaded haclMpl s.mem) (hpc : s.pc = haclMpl.base 5 + 224#64)
    (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hx0 : (s.readReg64 .x0).toNat = totlen) (hrem64 : remLen ≤ 64)
    (hx1_w : (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 remLen) (hx2 : s.readReg64 .x2 = remA)
    (hx3 : (s.readReg64 .x3).toNat = slice.length) (hrem_le : remLen ≤ slice.length)
    (hx4 : s.readReg64 .x4 = stA) (hx5 : 8 ≤ (s.readReg64 .x5).toNat)
    (hnext : ∀ sf : State, sf.pc = s.pc + 4#64 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → VmTracePreserved s sf → libcruxHmacLib.CodeLoaded haclMpl sf.mem →
      SepWP P target_pc sf (((remA ↦ₛ slice) ∗
        (stA ↦ₛ shaStateBytes (haclUpdateLastState sha256CompressState totlen (slice.take remLen) st)) ∗
        stackFrame s 352) ∗ F) post oom) :
    SepWP P target_pc s (((remA ↦ₛ slice) ∗ (stA ↦ₛ shaStateBytes st) ∗ stackFrame s 352) ∗ F) post oom := by
  have hf : (libcruxHmacLib.blockProgram haclMpl 5).fetch s.pc =
      some (.bl ((haclMpl.base 3 - haclMpl.base 5) - 224#64)) := by
    rw [hpc, ← haclPC5_eq_blockProgram, ← haclPl5_base]
    have h0 : (haclPC5.rebase haclPl5.base (fun _ => none)).fetch (haclPl5.base + 224#64) =
        some (.bl ((haclPl5.ρ sha256UpdateLastSym - haclPl5.base) - 224#64)) := by
      dsimp only [sha256UpdateLastSym]; simp [wp_norm]
    rw [h0, ← haclPl5_rho, haclPl5_base, resolve_sha256UpdateLast haclMpl]
  refine sepWP_block_bl (by decide : 5 < 7) hP (by decide : 224 < _) hlast
    (x := (totlen, remLen, remA, slice, stA, st)) (F := F) hcl hpc hrun hsp_align hf
    (by rw [hpc]; exact add_off_rel_target _ _ _) ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  · intro R hm; dsimp only [withTraceEq, sha256UpdateLastSpec]
    rw [show stackFrame (execInst _ s) 352 = stackFrame s 352 by simp [stackFrame, execInst_bl_eq],
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [execInst_bl_eq, State.mem_setPC, State.mem_writeReg64]; exact hcl, ?_⟩,
      by simpa only [sepConj_assoc] using hm⟩
    simp only [wp_norm]; exact ⟨hx0, hrem64, hx1_w, hx2, hx3, hrem_le, hx4, hx5⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f _; dsimp only [withTraceEq, sha256UpdateLastSpec]
    let s_bl := execInst (.bl ((haclMpl.base 3 - haclMpl.base 5) - 224#64)) s
    refine sepWP_of_eq (SepWP.pure_elim
      (fun h1 : VmPreserved s_bl sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem =>
        SepWP.pure_elim (fun h2 : sf.trace = s_bl.trace ∧ sf.fs = s_bl.fs =>
          hnext sf hpc_f hrun_f hsp_f (calleeSavedPreserved_of_bl hcs_f)
            ((VmTracePreserved.of_pf (processFieldsPreserved_execInst_bl _ s)).trans ⟨h1.1, h2.1, h2.2⟩) h1.2)))
      (by dsimp only [s_bl]
          rw [show stackFrame (execInst _ s) 352 = stackFrame s 352 by simp [stackFrame, execInst_bl_eq]]
          sep_ac_rfl)

private theorem stackFrame480_split (s0 : State) :
    stackFrame s0 480 =
      ((cells (s0.sp - 128#64) 7 ∗ cells (s0.sp - 64#64) 8) ∗
       (stackAt (s0.sp - 128#64) 352 ∗ cells (s0.sp - 72#64) 1)) := by
  rw [stackFrame_split_cells_eq s0 480 352 16 128,
      cells_split_sub s0.sp 128 72 7 9 (by decide), cells_split_sub s0.sp 72 64 1 8 (by decide)]
  sep_ac_rfl

private theorem stackFrame480_entails_of_state (s0 : State) (st : ShaState) :
    (stackAt (s0.sp - 128#64) 352 ∗ cells (s0.sp - 72#64) 1 ∗
     ((s0.sp - 128#64) ↦ₛ shaStateBytes st) ∗ savedRegs11 s0) ⊢ stackFrame s0 480 := by
  have hlen : (shaStateBytes st).length = 32 := by
    rcases st with ⟨_ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hL⟩ <;>
      try (simp at hL)
    simp [shaStateBytes, toLEBytes]
  have hst4 : ((s0.sp - 128#64) ↦ₛ shaStateBytes st) ⊢ cells (s0.sp - 128#64) 4 := by
    rw [← memRegion_cells (s0.sp - 128#64) 4 (by decide)]
    exact pointsToBytes_entails_memRegion_of_length hlen
  have hc3 : (((s0.sp - 96#64) ↦₆₄ s0.readReg64 Reg.fp) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x27)) ⊢ cells (s0.sp - 96#64) 3 := by
    refine cells_sub_succ_entails 96 3 (cells_sub_succ_entails 88 2 ?_)
    dsimp only [Nat.reduceSub]; rw [cells_sub_succ s0.sp 80 1 (by decide) (by decide)]
    exact Entails.sepExists_right _ (by dsimp only [Nat.reduceSub]; rw [cells_zero, sepConj_emp]; exact Entails.refl _)
  rw [show stackFrame s0 480 = (stackAt (s0.sp - 128#64) 352 ∗ cells (s0.sp - 72#64) 1 ∗
        (cells (s0.sp - 128#64) 4 ∗ (cells (s0.sp - 96#64) 3 ∗ cells (s0.sp - 64#64) 8))) by
      rw [stackFrame480_split s0, cells_split_sub s0.sp 128 96 4 3 (by decide)]; sep_ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hst4 (sepConj_mono hc3 (cells8_entails s0 _ _ _ _ _ _ _ _))))

private theorem ivCells4_eq_shaStateBytes (sp : BitVec 64) :
    (((sp - 128#64) ↦₆₄ 0xbb67ae856a09e667#64) ∗ ((sp - 120#64) ↦₆₄ 0xa54ff53a3c6ef372#64) ∗
     ((sp - 112#64) ↦₆₄ 0x9b05688c510e527f#64) ∗ ((sp - 104#64) ↦₆₄ 0x5be0cd191f83d9ab#64)) =
    ((sp - 128#64) ↦ₛ shaStateBytes sha256IV) := by
  have e (a k : BitVec 64) : sp - a + k = sp - (a - k) := by bv_omega
  rw [pointsToBytes_shaStateBytes (sp - 128#64) sha256IV]
  dsimp only [sha256IV, List.Vector.toList, List.getD_cons_zero, List.getD_cons_succ]
  simp only [pointsTo64_split32', BitVec.truncate_eq_setWidth, e, BitVec.reduceSub, sepConj_assoc]; rfl

private theorem and64_mask64_of_lt32 {n : Nat} (hn : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 n) &&& 0xffffffc0#64 = BitVec.ofNat 64 (64 * (n / 64)) := by
  rw [show ∀ w : BitVec 32, BitVec.setWidth 64 w &&& 0xffffffc0#64 = BitVec.setWidth 64 ((w >>> 6) <<< 6)
    from fun w => by bv_slice]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]; omega

private theorem and64_mask3f (n : Nat) :
    BitVec.setWidth 64 (BitVec.ofNat 32 n) &&& 270582939711#64 = BitVec.ofNat 64 (n - 64 * (n / 64)) := by
  rw [show ∀ w : BitVec 32, BitVec.setWidth 64 w &&& 270582939711#64 = BitVec.setWidth 64 ((w <<< 26) >>> 26)
    from fun w => by bv_slice]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]; omega

private def HashLoopSaved (s sf : State) : Prop :=
  TopCalleePreserved s sf ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
  sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
  sf.readReg64 .x23 = s.readReg64 .x23
private theorem HashLoopSaved.trans {s0 s1 s2 : State}
    (h01 : HashLoopSaved s0 s1) (h12 : HashLoopSaved s1 s2) : HashLoopSaved s0 s2 :=
  ⟨h01.1.trans h12.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1, h12.2.2.2.2.2.trans h01.2.2.2.2.2⟩
private theorem HashLoopSaved.of_calleeSavedPreserved {s0 sf : State}
    (h : CalleeSavedPreserved s0 sf) : HashLoopSaved s0 sf :=
  ⟨TopCalleePreserved.of_calleeSavedPreserved h, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

private theorem hash256_loop [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hupd : subroutine_ok P (haclMpl.base 1) (withHaclPreserved haclMpl sha256UpdateRawSpec)) :
    ∀ (rem : Nat) (curA stA target_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : ShaState)
      (Frame : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp},
      libcruxHmacLib.CodeLoaded haclMpl s.mem → s.pc = haclMpl.base 5 + 148#64 →
      s.status = .Running → s.sp = stA → s.spAligned = true → rem + 1 < 2 ^ 32 →
      64 * (rem + 1) ≤ curBs.length → curBs.length + 64 < 2 ^ 64 →
      s.readReg64 .x26 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x27 = BitVec.ofNat 64 ((curBs.length + 64) / 64) →
      s.readReg64 .x24 = curA → (s.readReg64 .x25).toNat = curBs.length →
      (∀ sm : State, sm.pc = haclMpl.base 5 + 192#64 → sm.status = .Running →
        sm.sp = stA → sm.spAligned = true → HashLoopSaved s sm →
        ProcessFieldsPreserved s sm → libcruxHmacLib.CodeLoaded haclMpl sm.mem →
        SepWP P target_pc sm (((curA ↦ₛ curBs) ∗
          (stA ↦ₛ shaStateBytes ((chunks64 (curBs.take (64 * (rem + 1)))).foldl
            sha256CompressState curSt)) ∗ stackFrame s 160) ∗ Frame) post oom) →
      SepWP P target_pc s
        (((curA ↦ₛ curBs) ∗ (stA ↦ₛ shaStateBytes curSt) ∗ stackFrame s 160) ∗ Frame) post oom := by
  intro rem; refine Nat.strongRecOn rem fun rem ih => ?_
  intro curA stA target_pc curBs curSt Frame s post oom
    hcl hpc hrun hsp hsp_align hrem32 hbs_ge hbs_max hx26 hx27 hx24 hx25 hcont
  have hbs64 : 64 ≤ curBs.length := by omega
  apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 168#64) hcl
    (PurePost := fun sm1 => sm1.sp = stA ∧ sm1.spAligned = true ∧ HashLoopSaved s sm1 ∧
      sm1.readReg64 .x0 = curA ∧ (sm1.readReg64 .x1).toNat = curBs.length ∧
      sm1.readReg64 .x2 = stA ∧ 8 ≤ (sm1.readReg64 .x3).toNat ∧
      sm1.readReg64 .x24 = curA ∧ (sm1.readReg64 .x25).toNat = curBs.length ∧
      sm1.readReg64 .x26 = s.readReg64 .x26 ∧
      sm1.readReg64 .x27 = BitVec.ofNat 64 ((curBs.length + 64) / 64))
    (fun sm m => by cases sm; simp [HashLoopSaved, TopCalleePreserved, State.spAligned])
  · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; rw [← haclPl5_base] at hpc
    have hrun0 : (s.setMem m).status = .Running := hrun
    have hx24_z : s.readReg64 (Reg.gpr 24#5) = curA := hx24
    have hx27_z : s.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 ((curBs.length + 64) / 64) := hx27
    have hb27 := x24_pos_bne_zero hbs64 hbs_max
    wp_sym_steps 5
    exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨hsp, hsp_align, ⟨⟨rfl, by simp [wp_norm]⟩, rfl, rfl, rfl, rfl, rfl⟩,
        rfl, hx25, rfl, by simp [wp_norm], hx24, hx25, rfl, hx27⟩, Entails.refl _⟩
  · intro sm1 hpc1 hrun1 hpf1 hcl1
      ⟨hsp1, hsp_align1, hls1, hx0_1, hx1_1, hx2_1, hx3_1, hx24_1, hx25_1, hx26_1, hx27_1⟩
    have hstk1 : stackFrame s 160 = stackFrame sm1 160 := by simp [stackFrame, hsp, hsp1]
    rw [hstk1]
    apply step_bl_sha256Update (by decide : 5 < 7) hP hupd hcl1 hpc1 hrun1 hsp_align1
      fetch_block5_bl_update hx0_1 hx1_1 hbs64 hx2_1 hx3_1
    intro sm2 hpc2 hrun2 hsp2 hcs2 hpf2 hcl2; rw [← hstk1]
    have hpc2' : sm2.pc = haclPl5.base + 172#64 := by rw [hpc2, hpc1, ← haclPl5_base, BitVec.add_assoc]; rfl
    have hsp2' := hsp2.trans hsp1
    have hsp_align2 : sm2.spAligned = true := by unfold State.spAligned at hsp_align1 ⊢; rwa [hsp2]
    have hls02 := hls1.trans (HashLoopSaved.of_calleeSavedPreserved hcs2)
    have hpf02 := hpf1.trans hpf2
    have hx26_2 : sm2.readReg64 .x26 = BitVec.ofNat 64 (rem + 1) :=
      (hcs2.2.2.2.2.2.2.2.1.trans hx26_1).trans hx26
    rcases rem with _ | rem'
    · have hx26_z : sm2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
      apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 192#64) hcl2
        (PurePost := fun sm3 => sm3.sp = stA ∧ sm3.spAligned = true ∧ HashLoopSaved sm2 sm3)
        (fun sm m => by cases sm; simp [HashLoopSaved, TopCalleePreserved, State.spAligned])
      · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; clear hpc2
        have hrun0 : (sm2.setMem m).status = .Running := hrun2
        wp_sym_steps 5
        exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨hsp2', hsp_align2, ⟨⟨rfl, by simp [wp_norm]⟩, rfl, rfl, rfl, rfl, rfl⟩⟩, Entails.refl _⟩
      · intro sm3 hpc3 hrun3 hpf3 hcl3 ⟨hsp3, hsp_align3, hls3⟩
        rw [show sha256CompressState curSt (curBs.take 64) =
            (chunks64 (curBs.take (64 * (0 + 1)))).foldl sha256CompressState curSt by
              rw [chunks64_exact_one (curBs.take 64) (List.length_take_of_le hbs64),
                  List.foldl_cons, List.foldl_nil]]
        exact hcont sm3 hpc3 hrun3 hsp3 hsp_align3 (hls02.trans hls3) (hpf02.trans hpf3) hcl3
    · have hx24_z : sm2.readReg64 (Reg.gpr 24#5) = curA := hcs2.2.2.2.2.2.1.trans hx24_1
      have hx25_2 : (sm2.readReg64 (Reg.gpr 25#5)).toNat = curBs.length := by
        change (sm2.readReg64 .x25).toNat = _; rw [hcs2.2.2.2.2.2.2.1]; exact hx25_1
      have hx27_z : sm2.readReg64 (Reg.gpr 27#5) = BitVec.ofNat 64 ((curBs.length + 64) / 64) :=
        hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
      have hx26_z : sm2.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 (rem' + 1 + 1) := hx26_2
      rcases loop_step_arith hrem32 hbs64 hbs_max hx25_2 with ⟨hb_cbnz, hsub_cnt, hsub_div, hsub_len⟩
      apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 148#64) hcl2
        (PurePost := fun sm3 => sm3.sp = stA ∧ sm3.spAligned = true ∧ HashLoopSaved sm2 sm3 ∧
          sm3.readReg64 .x26 = BitVec.ofNat 64 (rem' + 1) ∧
          sm3.readReg64 .x27 = BitVec.ofNat 64 (((curBs.drop 64).length + 64) / 64) ∧
          sm3.readReg64 .x24 = curA + 64#64 ∧ (sm3.readReg64 .x25).toNat = (curBs.drop 64).length)
        (fun sm m => by cases sm; simp [HashLoopSaved, TopCalleePreserved, State.spAligned])
      · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; clear hpc2
        rw [hsub_cnt] at hb_cbnz
        have hrun0 : (sm2.setMem m).status = .Running := hrun2
        wp_sym_steps 5
        exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun2])
          ⟨⟨by simp only [wp_norm]; exact hsp2',
            by simp only [State.spAligned, wp_norm]; exact hsp_align2,
            ⟨⟨by simp [wp_norm], by simp [wp_norm]⟩,
              by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩,
            by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
            by simp only [wp_norm]; exact hsub_len⟩, Entails.refl _⟩
      · intro sm3 hpc3 hrun3 hpf3 hcl3 ⟨hsp3, hsp_align3, hls3, hx26_3, hx27_3, hx24_3, hx25_3⟩
        have hstk3 : stackFrame s 160 = stackFrame sm3 160 := by simp [stackFrame, hsp, hsp3]
        have hsplit := pointsToBytes_take_drop curA 64 curBs hbs64
        refine sepWP_of_eq (ih rem' (Nat.lt_succ_self rem') (curA + 64#64) stA target_pc (curBs.drop 64)
          (sha256CompressState curSt (curBs.take 64)) ((curA ↦ₛ curBs.take 64) ∗ Frame) sm3
          hcl3 hpc3 hrun3 hsp3 hsp_align3 (by omega) (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega) hx26_3 hx27_3 hx24_3 hx25_3 ?_)
          (by rw [hsplit, hstk3]; sep_ac_rfl)
        intro sm4 hpc4 hrun4 hsp4 hsp_align4 hls4 hpf4 hcl4
        exact sepWP_of_eq (hcont sm4 hpc4 hrun4 hsp4 hsp_align4
            ((hls02.trans hls3).trans hls4) ((hpf02.trans hpf3).trans hpf4) hcl4)
          (by rw [chunks64_take_succ_blocks curBs rem' hbs_ge, List.foldl_cons, ← hstk3, hsplit]
              sep_ac_rfl)

set_option maxHeartbeats 400000 in
private theorem hash256_at [HaclPlacement] {P : Program} (hP : HaclInProg P haclMpl)
    (hupd : subroutine_ok P (haclMpl.base 1) (withHaclPreserved haclMpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (haclMpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (haclMpl.base 5) (withTraceEq (hash256Spec haclMpl)) := by
  have hlast := sha256UpdateLast_at hP hupd hmemcpy
  apply subroutine_ok_of_sepWP_init; rintro ⟨dstA, dst, msgA, msg⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [withTraceEq, hash256Spec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hcl, hx0, hx1, hdst32, hx2, hx3, hmsg32, hx4_w⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  let stA := s0.sp - 128#64
  refine sepWP_of_eq (sepWP_block_seg (by decide : 5 < 7) hP hcl (mid := haclMpl.base 5 + 128#64)
    (Pre := cells (s0.sp - 64#64) 8 ∗ cells (s0.sp - 128#64) 7)
    (Post := fun _ => (stA ↦ₛ shaStateBytes sha256IV) ∗ savedRegs11 s0)
    (PurePost := fun sm1 => sm1.sp = stA ∧ sm1.spAligned = true ∧ TopCalleePreserved s0 sm1 ∧
      sm1.readReg64 .x19 = dstA ∧ (sm1.readReg64 .x20).toNat = dst.length ∧
      sm1.readReg64 .x21 = BitVec.ofNat 64 msg.length ∧ sm1.readReg64 .x22 = msgA ∧
      (sm1.readReg64 .x23).toNat = msg.length ∧ sm1.readReg64 .x26 = BitVec.ofNat 64 (msg.length / 64))
    (Frame := (dstA ↦ₛ dst) ∗ (msgA ↦ₛ msg) ∗ stackAt stA 352 ∗ cells (s0.sp - 72#64) 1)
    (fun _ _ => rfl) (fun sm m => by cases sm; simp [TopCalleePreserved, State.spAligned]) ?_ ?_)
    (by rw [stackFrame480_split s0]; dsimp only [stA]; sep_ac_rfl)
  · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; rw [← haclPl5_base] at hpc
    have hrun0 : (s0.setMem m).status = .Running := hrun
    have hsp0 : (s0.setMem m).spAligned = true := hsp_align
    have hx0_z : s0.readReg64 (Reg.gpr 0#5) = dstA := hx0
    have hx2_z : s0.readReg64 (Reg.gpr 2#5) = msgA := hx2
    have hx4_z : (s0.readReg64 (Reg.gpr 4#5)).setWidth 32 = BitVec.ofNat 32 msg.length := hx4_w
    repeat (apply cells_sub_elim (by decide) (by decide); intro _)
    wp_conv_pre =>
      rw [cells_zero, sepConj_emp]
      simp only [sepConj_assoc]; rw [sepConj_comm (cells (s0.sp - 64#64) 8)]
    repeat (apply cells_sub_elim (by decide) (by decide); intro _)
    wp_simp_pre only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    wp_sym_steps 32
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨⟨rfl,
      State.spAligned_sub s0 128#64 hsp_align, ⟨rfl, by simp [wp_norm]⟩, rfl, hx1, ?_, rfl, hx3, ?_⟩, ?_⟩
    · simp only [wp_norm]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega
    · simp only [wp_norm]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]; omega
    · dsimp only [stA, savedRegs11]; rw [← ivCells4_eq_shaStateBytes s0.sp]
      simp only [sepConj_assoc]; exact Entails.refl _
  · intro sm1 hpc1 hrun1 hpf1 hcl1 ⟨hsp1, hsp_align1, htc1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1⟩
    let nbytes := 64 * (msg.length / 64)
    let st_mid := (chunks64 (msg.take nbytes)).foldl sha256CompressState sha256IV
    suffices hjoin : ∀ sm : State, sm.pc = haclMpl.base 5 + 192#64 → sm.status = .Running →
        sm.sp = stA → sm.spAligned = true → HashLoopSaved sm1 sm → ProcessFieldsPreserved sm1 sm →
        libcruxHmacLib.CodeLoaded haclMpl sm.mem →
        SepWP P (s0.readReg64 Reg.lr) sm
          ((dstA ↦ₛ dst) ∗ (msgA ↦ₛ msg) ∗ stackAt stA 352 ∗ cells (s0.sp - 72#64) 1 ∗
           (stA ↦ₛ shaStateBytes st_mid) ∗ savedRegs11 s0)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (((⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
              (dstA ↦ₛ (sha256With sha256CompressState msg ++ dst.drop 32)) ∗
              (msgA ↦ₛ msg) ∗ stackFrame s0 480) ∗ ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝) ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) (fun _ => ⌜False⌝) by
      by_cases hlt64 : msg.length < 64
      · apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 192#64) hcl1
          (PurePost := fun sm2 => sm2.sp = stA ∧ sm2.spAligned = true ∧ HashLoopSaved sm1 sm2)
          (fun sm m => by cases sm; simp [HashLoopSaved, TopCalleePreserved, State.spAligned])
        · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; rw [← haclPl5_base] at hpc1
          have hrun0 : (sm1.setMem m).status = .Running := hrun1
          have hx26_z : sm1.readReg64 (Reg.gpr 26#5) = 0#64 := by
            rw [hx26_1, show msg.length / 64 = 0 by omega]
          clear hx26_1; wp_sym_steps 1
          exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun1])
            ⟨⟨hsp1, hsp_align1, ⟨⟨rfl, by simp [wp_norm]⟩, rfl, rfl, rfl, rfl, rfl⟩⟩, Entails.refl _⟩
        · intro sm2 hpc2 hrun2 hpf2 hcl2 ⟨hsp2, hsp_align2, hls2⟩
          exact sepWP_of_eq (hjoin sm2 hpc2 hrun2 hsp2 hsp_align2 hls2 hpf2 hcl2)
            (by dsimp only [st_mid, nbytes]
                rw [show msg.length / 64 = 0 by omega, Nat.mul_zero, List.take_zero,
                    chunks64_of_length_lt (by decide), List.foldl_nil]; sep_ac_rfl)
      · let rem := msg.length / 64 - 1
        have hrem_succ : rem + 1 = msg.length / 64 := by omega
        apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 148#64) hcl1
          (PurePost := fun sm2 => sm2.sp = stA ∧ sm2.spAligned = true ∧ HashLoopSaved sm1 sm2 ∧
            sm2.readReg64 .x26 = BitVec.ofNat 64 (rem + 1) ∧
            sm2.readReg64 .x27 = BitVec.ofNat 64 ((msg.length + 64) / 64) ∧
            sm2.readReg64 .x24 = msgA ∧ (sm2.readReg64 .x25).toNat = msg.length)
          (fun sm m => by cases sm; simp [HashLoopSaved, TopCalleePreserved, State.spAligned])
        · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; rw [← haclPl5_base] at hpc1
          have hrun0 : (sm1.setMem m).status = .Running := hrun1
          have hx26_z : sm1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 (rem + 1) := by
            rw [hrem_succ]; exact hx26_1
          have hx22_z : sm1.readReg64 (Reg.gpr 22#5) = msgA := hx22_1
          have hb26 : ((BitVec.ofNat 64 (rem + 1)).setWidth 32 == 0#32) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have htn := congrArg BitVec.toNat h
            simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htn; omega
          wp_sym_steps 5
          exact SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun1])
            ⟨⟨hsp1, hsp_align1, ⟨⟨rfl, by simp [wp_norm]⟩, rfl, rfl, rfl, rfl, rfl⟩,
              hx26_z, x24_init_eq hx23_1 (by omega), rfl, hx23_1⟩, Entails.refl _⟩
        · intro sm2 hpc2 hrun2 hpf2 hcl2 ⟨hsp2, hsp_align2, hls2, hx26_2, hx27_2, hx24_2, hx25_2⟩
          have hstk_shrink := stackAt_shrink stA 352 160 (by decide)
          have hstk2 : stackAt stA 160 = stackFrame sm2 160 := by simp [stackFrame, hsp2]
          refine sepWP_of_eq (hash256_loop hP hupd rem msgA stA (s0.readReg64 Reg.lr) msg sha256IV
            ((dstA ↦ₛ dst) ∗ memRegion (stA - BitVec.ofNat 64 352) (352 - 160) ∗
              cells (s0.sp - 72#64) 1 ∗ savedRegs11 s0) sm2
            hcl2 hpc2 hrun2 hsp2 hsp_align2 (by omega) (by omega) (by omega)
            hx26_2 hx27_2 hx24_2 hx25_2 ?_)
            (by rw [hstk_shrink, hstk2]; sep_ac_rfl)
          intro sm3 hpc3 hrun3 hsp3 hsp_align3 hls3 hpf3 hcl3
          exact sepWP_of_eq (hjoin sm3 hpc3 hrun3 hsp3 hsp_align3 (hls2.trans hls3) (hpf2.trans hpf3) hcl3)
            (by dsimp only [st_mid, nbytes]; rw [hrem_succ, ← hstk2, hstk_shrink]; sep_ac_rfl)
    intro sm hpc_m hrun_m hsp_m hsp_align_m hls_m hpf_m hcl_m
    let remLen := msg.length - nbytes
    have hnbytes_le : nbytes ≤ msg.length := Nat.mul_div_le msg.length 64
    have hrem64 : remLen ≤ 64 := by
      have := Nat.lt_div_mul_add (a := msg.length) (b := 64) (by decide); omega
    apply sepWP_block_pure_seg (by decide : 5 < 7) hP (mid := haclMpl.base 5 + 224#64) hcl_m
      (PurePost := fun sm4 => sm4.sp = stA ∧ sm4.spAligned = true ∧ TopCalleePreserved sm sm4 ∧
        (sm4.readReg64 .x0).toNat = msg.length ∧ (sm4.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 remLen ∧
        sm4.readReg64 .x2 = msgA + BitVec.ofNat 64 nbytes ∧
        (sm4.readReg64 .x3).toNat = (msg.drop nbytes).length ∧
        sm4.readReg64 .x4 = stA ∧ 8 ≤ (sm4.readReg64 .x5).toNat ∧
        sm4.readReg64 .x19 = dstA ∧ (sm4.readReg64 .x20).toNat = dst.length)
      (fun sm' m => by cases sm'; simp [TopCalleePreserved, State.spAligned])
    · intro m; rw [← haclPC5_eq_blockProgram, ← haclPl5_base]; rw [← haclPl5_base] at hpc_m
      have hrun0 : (sm.setMem m).status = .Running := hrun_m
      have hx21_z : sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 msg.length := hls_m.2.2.2.1.trans hx21_1
      have hx22_z : sm.readReg64 (Reg.gpr 22#5) = msgA := hls_m.2.2.2.2.1.trans hx22_1
      have hx23_m : (sm.readReg64 .x23).toNat = msg.length := by rw [hls_m.2.2.2.2.2]; exact hx23_1
      have hw21 : (BitVec.ofNat 64 msg.length).setWidth 32 = BitVec.ofNat 32 msg.length := by
        apply BitVec.eq_of_toNat_eq; simp
      have hmask8 : BitVec.setWidth 64 (BitVec.ofNat 32 msg.length) &&& 0xffffffc0#64 =
          BitVec.ofNat 64 nbytes := and64_mask64_of_lt32 hmsg32
      have hnbytes_sw : BitVec.setWidth 64 ((BitVec.ofNat 64 nbytes).setWidth 32) =
          BitVec.ofNat 64 nbytes := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      have hnbytes_tr : BitVec.setWidth 64 (BitVec.truncate 32 (BitVec.ofNat 64 nbytes)) =
          BitVec.ofNat 64 nbytes := hnbytes_sw
      have hb_lo : BitVec.ult (sm.readReg64 (Reg.gpr 23#5)) (BitVec.ofNat 64 nbytes) = false := by
        rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]; simp only [BitVec.toNat_ofNat]
        change ¬ (sm.readReg64 .x23).toNat < _; omega
      wp_sym_steps 8
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun_m])
        ⟨⟨hsp_m, hsp_align_m, ⟨rfl, by simp [wp_norm]⟩, ?_, ?_, rfl, ?_, rfl, by simp [wp_norm],
          hls_m.2.1.trans hx19_1, by simp only [wp_norm]; rw [hls_m.2.2.1]; exact hx20_1⟩, Entails.refl _⟩
      · simp only [wp_norm, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      · simp only [wp_norm, hw21, and64_mask3f msg.length]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      · simp only [wp_norm]
        have hle23 : BitVec.ofNat 64 nbytes ≤ sm.readReg64 (Reg.gpr 23#5) := by
          rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
          change nbytes % 2 ^ 64 ≤ (sm.readReg64 .x23).toNat; omega
        rw [List.length_drop, BitVec.toNat_sub_of_le hle23, BitVec.toNat_ofNat, hx23_m]; omega
    · intro sm4 hpc4 hrun4 hpf4 hcl4
        ⟨hsp4, hsp_align4, htc4, hx0_4, hx1_4, hx2_4, hx3_4, hx4_4, hx5_4, hx19_4, hx20_4⟩
      have hmsg_split := pointsToBytes_take_drop msgA nbytes msg hnbytes_le
      have hstk4 : stackAt stA 352 = stackFrame sm4 352 := by simp [stackFrame, hsp4]
      refine sepWP_of_eq (step_bl_sha256UpdateLast hP hlast
        (totlen := msg.length) (remLen := remLen) (remA := msgA + BitVec.ofNat 64 nbytes)
        (slice := msg.drop nbytes) (stA := stA) (st := st_mid)
        (F := (dstA ↦ₛ dst) ∗ (msgA ↦ₛ msg.take nbytes) ∗ cells (s0.sp - 72#64) 1 ∗ savedRegs11 s0)
        hcl4 hpc4 hrun4 hsp_align4 hx0_4 hrem64 hx1_4 hx2_4 hx3_4 (by rw [List.length_drop]) hx4_4 hx5_4 ?_)
        (by rw [hmsg_split, hstk4]; sep_ac_rfl)
      intro sm5 hpc5 hrun5 hsp5 hcs5 hvm5 hcl5
      have hpc5' : sm5.pc = haclPl5.base + 228#64 := by rw [hpc5, hpc4, ← haclPl5_base, BitVec.add_assoc]; rfl
      have hsp5' : sm5.sp = stA := hsp5.trans hsp4
      have hsp_align5 : sm5.spAligned = true := by unfold State.spAligned at hsp_align4 ⊢; rwa [hsp5]
      have htc05 := ((htc1.trans hls_m.1).trans htc4).trans (TopCalleePreserved.of_calleeSavedPreserved hcs5)
      have hvm05 := (VmTracePreserved.of_pf ((hpf1.trans hpf_m).trans hpf4)).trans hvm5
      have hdrop_take : (msg.drop nbytes).take remLen = msg.drop nbytes :=
        List.take_of_length_le (by rw [List.length_drop])
      let st_last := haclUpdateLastState sha256CompressState msg.length (msg.drop nbytes) st_mid
      refine sepWP_of_eq (sepWP_block_seg (by decide : 5 < 7) hP hcl5 (mid := s0.readReg64 Reg.lr)
        (Pre := (dstA ↦ₛ dst) ∗ stackAt stA 352 ∗ cells (s0.sp - 72#64) 1 ∗
          (stA ↦ₛ shaStateBytes st_last) ∗ savedRegs11 s0)
        (Post := fun _ => (dstA ↦ₛ (sha256With sha256CompressState msg ++ dst.drop 32)) ∗ stackFrame s0 480)
        (PurePost := fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (Frame := (msgA ↦ₛ msg))
        (fun _ _ => rfl) (fun sm' m => by cases sm'; simp [CalleeSavedPreserved, calleeSavedVRegs]) ?_ ?_)
        (by rw [hdrop_take, ← hstk4, hmsg_split]; dsimp only [st_last]; sep_ac_rfl)
      · intro m; rw [← haclPC5_eq_blockProgram]; clear hpc5 hsp5 hsp4
        have hrun0 : (sm5.setMem m).status = .Running := hrun5
        have hsp0 : (sm5.setMem m).spAligned = true := hsp_align5
        have hx19_z : sm5.readReg64 (Reg.gpr 19#5) = dstA := hcs5.1.trans hx19_4
        have hx20_5 : (sm5.readReg64 .x20).toNat = dst.length := by rw [hcs5.2.1]; exact hx20_4
        have hb31 : (sm5.readReg64 (Reg.gpr 20#5)).ule 31#64 = false := by
          rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; change ¬ (sm5.readReg64 .x20).toNat ≤ 31; omega
        dsimp only [stA] at hsp5'; dsimp only [stA, savedRegs11]
        rw [pointsToBytes_take_drop dstA 32 dst hdst32,
            pointsToBytes_32_to_cells32 dstA (dst.take 32) (List.length_take_of_le hdst32),
            pointsToBytes_shaStateBytes (s0.sp - 128#64) st_last]
        wp_simp_pre only [BitVec.ofNat_eq_ofNat, sepConj_assoc]
        wp_sym_steps 26
        refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun5])
          ⟨⟨by simp [wp_norm], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, htc05.1, rfl,
            by simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
                 calleeSavedVRegs_writeReg64]; exact htc05.2⟩⟩, ?_⟩
        rw [← (haclHash256Pure_eq_sha256With sha256CompressState msg : _ = sha256With sha256CompressState msg)]
        dsimp only [nbytes, st_mid, st_last]
        rw [pointsToBytes_beState_append dstA _ (dst.drop 32)]
        have hstk := stackFrame480_entails_of_state s0
          (haclUpdateLastState sha256CompressState msg.length (msg.drop (64 * (msg.length / 64)))
            ((chunks64 (msg.take (64 * (msg.length / 64)))).foldl sha256CompressState sha256IV))
        dsimp only [savedRegs11] at hstk
        rw [pointsToBytes_shaStateBytes (s0.sp - 128#64)] at hstk
        simp only [sepConj_assoc] at hstk ⊢
        repeat refine sepConj_mono_right ?_
        exact hstk
      · intro sf hpc_f hrun_f hpf_f hcl_f ⟨hsp_f, hcs_f⟩
        refine SepWP.done hpc_f hrun_f ⟨fun hmem => ?_, hsp_f, hcs_f⟩
        have hvmt := hvm05.trans (VmTracePreserved.of_pf hpf_f)
        rw [show (((⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
              (dstA ↦ₛ (sha256With sha256CompressState msg ++ dst.drop 32)) ∗
              (msgA ↦ₛ msg) ∗ stackFrame s0 480) ∗ ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝) ∗ R) =
            ⌜VmPreserved s0 sf ∧ libcruxHmacLib.CodeLoaded haclMpl sf.mem⌝ ∗
            ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
            ((((dstA ↦ₛ (sha256With sha256CompressState msg ++ dst.drop 32)) ∗
               stackFrame s0 480) ∗ (msgA ↦ₛ msg)) ∗ R) by sep_ac_rfl, satisfies_pure_sepConj]
        exact ⟨⟨hvmt.1, hcl_f⟩, by rw [satisfies_pure_sepConj]; exact ⟨hvmt.2, hmem⟩⟩

/-- Ambient-program `subroutine_ok` for Block `5` (`libcrux_sha2::hacl::hash_256`) augmented with
`sf.trace = s0.trace` (`withTraceEq`). -/
theorem hash256_withTraceEq_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (mpl.base 5) (withTraceEq (hash256Spec mpl)) :=
  @hash256_at ⟨mpl, hP.placeable⟩ P hP hupd hmemcpy

/-- Ambient-program `subroutine_ok` for Block `5` (`libcrux_sha2::hacl::hash_256`). -/
theorem hash256_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    subroutine_ok P (mpl.base 5) (hash256Spec mpl) :=
  subroutine_ok_of_withTraceEq (hash256_withTraceEq_subroutineOk hP hupd hmemcpy)

/-- Assemble the full `HaclSubroutines` bundle (Blocks `0`, `2`, `3`, `4`, `5`) parameterized over
Block `1` (`sha256_update`) and `haclMemcpySpec` (`0` B caller stack). -/
theorem haclSubroutines_ok {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    HaclSubroutines P mpl :=
  ⟨sha256Init_subroutineOk hP, sha256UpdateNblocks_subroutineOk hP hupd,
   sha256UpdateLast_subroutineOk hP hupd hmemcpy, sha256Finish_subroutineOk hP,
   hash256_subroutineOk hP hupd hmemcpy⟩

/-- `HaclSubroutines` specialized to `RustStdAllocBudgetBridge.allocMemcpyVmSpec`. -/
theorem haclSubroutines_ok_of_allocMemcpyVm {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) allocMemcpyVmSpec) : HaclSubroutines P mpl :=
  haclSubroutines_ok hP hupd (haclMemcpy_of_allocMemcpyVm hmemcpy)

/-- `HaclSubroutines` specialized to `HookSat H memcpySym allocMemcpyVmSpec`. -/
theorem haclSubroutines_ok_of_hookSat {P : Program} {mpl : Obj.MultiPlacement}
    {H : String → Option (State → State)} (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hext : P.externAt? (mpl.ρ memcpySym) = H memcpySym)
    (hsat : HookSat H memcpySym allocMemcpyVmSpec) : HaclSubroutines P mpl :=
  haclSubroutines_ok_of_allocMemcpyVm hP hupd (by
    rcases hsat with ⟨f, hH, hok⟩; exact subroutine_ok_of_hookOk (hext.trans hH) hok)

/-- `HaclSubroutines` specialized to linked-ELF `MuslMemOps` `stdMemcpySpec`. -/
theorem haclSubroutines_ok_of_stdMemcpy {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hupd : subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec))
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) stdMemcpySpec) : HaclSubroutines P mpl :=
  haclSubroutines_ok hP hupd (haclMemcpy_of_stdMemcpy hmemcpy)

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256
