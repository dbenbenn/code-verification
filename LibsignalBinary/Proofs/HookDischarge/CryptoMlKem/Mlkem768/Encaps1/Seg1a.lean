/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedOddSites
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (cell_entails_memRegion8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Vec128At VecRangeMem append_extractLsb64 bytesToVecNat pointsToBytes_eq_vecRangeMem
  vec128At_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_chk spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args SavedFrame03 blk03_code_eq blk03_tree_size blkLib03 blkPC03
  blkPl03 blkPlaceable03 blkTree03)

/-!
# `encapsulate1_serialized` (`B03`) — Segment 1a (`+0x0000 .. +0x00fc`)

Shared `Seg1 → Seg2` stack/register bundles, fetch theorems for `[0x0000, 0x026c)`, prologue +
four `4096`-byte stack probes (`+0x0000 → +0x0064`), and `G(m || H(pk))` via `B00` (`+0x0064 → +0x00fc`).
-/

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x0000 → 0x026c]
gen_placed_odd_sites blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x0200 → 0x0268]

@[simp, arm64_norm]
theorem blkPC03_rebase_fetchOff_24c [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC03.rebase b X).fetch (b + BitVec.ofNat 64 588) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl03.ρ "libcrux_ml_kem:.rodata.cst16.0")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib03) (prog := blkPC03) (pl := blkPl03)
    (b := b) (X := X) (off := 588)
    (r := { off := 588, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" })
    rfl blkPlaceable03 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 588)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 147) blk03_code_eq blk03_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
theorem blkPC03_rebase_fetchOff_258 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC03.rebase b X).fetch (b + BitVec.ofNat 64 600) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 10))
          (lo12Of (blkPl03.ρ "libcrux_ml_kem:.rodata.cst16.1")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib03) (prog := blkPC03) (pl := blkPl03)
    (b := b) (X := X) (off := 600)
    (r := { off := 600, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" })
    rfl blkPlaceable03 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 600)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 150) blk03_code_eq blk03_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
theorem blkPC03_rebase_fetchOff_260 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC03.rebase b X).fetch (b + BitVec.ofNat 64 608) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl03.ρ "libcrux_ml_kem:.rodata.cst16.2")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib03) (prog := blkPC03) (pl := blkPl03)
    (b := b) (X := X) (off := 608)
    (r := { off := 608, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" })
    rfl blkPlaceable03 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 608)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 152) blk03_code_eq blk03_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
theorem blkPl03_ρ [MlKemPlacement] (sym : String) :
    blkPl03.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC03

/-! ## 1. Stack Bundles and Register Invariant Entering `Seg2` (`+0x0504`) -/

/-- Caller arguments spilled at `[sp, sp + 40)` in `B03` and read back in `Seg6`. -/
@[expose] def SavedArgs03 (sp : BitVec 64) (a : MlkemBlk03Args) : SepProp :=
  (sp ↦₆₄ a.ssA) ∗
  ((sp + 8#64) ↦₆₄ a.ret) ∗
  ((sp + 16#64) ↦₆₄ a.randA) ∗
  ((sp + 24#64) ↦₆₄ a.esA) ∗
  ((sp + 32#64) ↦₆₄ 2080#64)

/-- Low stack constants read during `Seg2`: `sp + 3496`, `cst16.2`, `cst16.1`, and `(sp + 2192) + 11`. -/
@[expose] def Seg2ConstsLo (sp : BitVec 64) : SepProp :=
  ((sp + 40#64) ↦₆₄ (sp + 3496#64)) ∗
  Vec128At (sp + 48#64) 0x000000000000000000000000001f0200#128 ∗
  Vec128At (sp + 64#64) 0x000000000000000000000000001f0100#128 ∗
  ((sp + 88#64) ↦₆₄ ((sp + 2192#64) + 11#64))

/-- Duplicated `rho = hdr64.take 32` 64-bit lanes and `cst16.0` mask at `[sp + 336, sp + 416)`. -/
@[expose] def Seg2SeedConsts (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  let s0w := ByteSlice.readLE rho 0 8
  let s1w := ByteSlice.readLE rho 8 8
  let s2w := ByteSlice.readLE rho 16 8
  let s3w := ByteSlice.readLE rho 24 8
  Vec128At (sp + 336#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
  Vec128At (sp + 352#64) (s3w ++ s3w) ∗
  Vec128At (sp + 368#64) (s2w ++ s2w) ∗
  Vec128At (sp + 384#64) (s1w ++ s1w) ∗
  Vec128At (sp + 400#64) (s0w ++ s0w)

/-- Stack slots, `G(m || H(pk))`, callee-saved spill frame, and caller regions untouched across `Seg2`. -/
@[expose] def Seg2Preserved (s0 : State) (a : MlkemBlk03Args) (R : SepProp) : SepProp :=
  let sp := s0.sp - 17024#64
  SavedArgs03 sp a ∗
  memRegion (sp + 80#64) 8 ∗
  memRegion (sp + 3704#64) 568 ∗
  memRegion (sp + 5904#64) 864 ∗
  ((sp + 6768#64) ↦ₛ sha3_512List (a.rand ++ a.hdr64.drop 32)) ∗
  memRegion (sp + 11440#64) 1008 ∗
  memRegion (sp + 12472#64) 1512 ∗
  memRegion (sp + 14488#64) 2376 ∗
  SavedFrame03 (sp + 16864#64) s0 ∗
  stackAt sp 1136 ∗
  (a.hdrA ↦ₛ a.hdr64) ∗
  (a.randA ↦ₛ a.rand) ∗
  memRegion a.ret 961 ∗
  memRegion a.esA 2080 ∗
  memRegion a.ssA 32 ∗
  R

/-- Callee-saved GPR and `sp` invariant maintained across all 3 rows of `Seg2`. -/
@[expose] def Seg2RegInv [MlKemPlacement] (sp : BitVec 64) (s : State) : Prop :=
  s.sp = sp ∧
  s.spAligned = true ∧
  s.readReg64 .x19 =
    mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ∧
  s.readReg64 .x20 = sp + 4272#64 ∧
  s.readReg64 .x21 = sp + 12448#64 ∧
  s.readReg64 .x23 = sp + 2456#64 ∧
  s.readReg64 (.gpr 24#5) = 544#64 ∧
  s.readReg64 (.gpr 25#5) = sp + 14248#64 ∧
  s.readReg64 (.gpr 26#5) = (sp + 13984#64) + 11#64 ∧
  s.readReg64 (.gpr 27#5) = 256#64 ∧
  s.readReg64 .x28 = sp + 13984#64

theorem sha3_512List_length (msg : List (BitVec 8)) :
    (sha3_512List msg).length = 64 := by
  simp [sha3_512List, keccakSponge]

/-! ## 2. Prologue & Four `4096`-Byte Stack Probes (`+0x0000 → +0x0064`) -/

theorem cells32_entails_memRegion (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      memRegion a 32 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact entails_sub (cell_entails_memRegion8 a v0) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (a + 8#64) v1) (by sep_frame)
      (entails_sub (cell_entails_memRegion8 (a + 16#64) v2) (by sep_frame)
        (entails_sub (cell_entails_memRegion8 (a + 24#64) v3) (by sep_frame) (by sep_frame))))

private theorem stackAt_18160_prologue_split (sp0 : BitVec 64) :
    stackAt sp0 18160 =
      memRegion (sp0 - 16544#64) 8 ∗
      memRegion (sp0 - 12448#64) 8 ∗
      memRegion (sp0 - 8352#64) 8 ∗
      memRegion (sp0 - 4256#64) 8 ∗
      memRegion (sp0 - 160#64) 32 ∗
      memRegion (sp0 - 128#64) 32 ∗
      memRegion (sp0 - 96#64) 32 ∗
      memRegion (sp0 - 64#64) 32 ∗
      memRegion (sp0 - 32#64) 32 ∗
      memRegion (sp0 - 17024#64) 480 ∗
      memRegion (sp0 - 16536#64) 4088 ∗
      memRegion (sp0 - 12440#64) 4088 ∗
      memRegion (sp0 - 8344#64) 4088 ∗
      memRegion (sp0 - 4248#64) 4088 ∗
      stackAt (sp0 - 17024#64) 1136 := by
  unfold stackAt
  have hbase : sp0 - BitVec.ofNat 64 18160 = (sp0 - 17024#64) - BitVec.ofNat 64 1136 := by bv_omega
  rw [hbase,
    memRegion_split' (b' := sp0 - 17024#64) (n := (1136 : Nat)) (k := (17024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 17024#64) (b' := sp0 - 16544#64) (n := 480) (k := (16544 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 16536#64) (n := 8) (k := (16536 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 12448#64) (n := (4088 : Nat)) (k := (12448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 12440#64) (n := 8) (k := (12440 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 8352#64) (n := (4088 : Nat)) (k := (8352 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 8344#64) (n := 8) (k := (8344 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4256#64) (n := (4088 : Nat)) (k := (4256 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4248#64) (n := 8) (k := (4248 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 160#64) (n := (4088 : Nat)) (k := 160) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 128#64) (n := 32) (k := 128) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 96#64) (n := 32) (k := 96) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 64#64) (n := 32) (k := 64) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem probes_restore_16864 (sp0 p0 p1 p2 p3 : BitVec 64) :
    ((sp0 - 16544#64) ↦₆₄ p0) ∗ ((sp0 - 12448#64) ↦₆₄ p1) ∗
      ((sp0 - 8352#64) ↦₆₄ p2) ∗ ((sp0 - 4256#64) ↦₆₄ p3) ∗
      memRegion (sp0 - 17024#64) 480 ∗ memRegion (sp0 - 16536#64) 4088 ∗
      memRegion (sp0 - 12440#64) 4088 ∗ memRegion (sp0 - 8344#64) 4088 ∗
      memRegion (sp0 - 4248#64) 4088 ⊢
      memRegion (sp0 - 17024#64) 16864 := by
  rw [memRegion_split' (b' := sp0 - 16544#64) (n := 480) (k := (16384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 16536#64) (n := 8) (k := (16376 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 12448#64) (n := (4088 : Nat)) (k := (12288 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 12440#64) (n := 8) (k := (12280 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 8352#64) (n := (4088 : Nat)) (k := (8192 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 8344#64) (n := 8) (k := (8184 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4256#64) (n := (4088 : Nat)) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4248#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  exact entails_sub (cell_entails_memRegion8 (sp0 - 16544#64) p0) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (sp0 - 12448#64) p1) (by sep_frame)
      (entails_sub (cell_entails_memRegion8 (sp0 - 8352#64) p2) (by sep_frame)
        (entails_sub (cell_entails_memRegion8 (sp0 - 4256#64) p3) (by sep_frame) (by sep_frame))))

private theorem bv_sub_add_eq_sub (x a b c : BitVec 64) (h : -a + b = -c) :
    x - a + b = x - c := by
  bv_omega

private theorem seg1_spill [MlKemPlacement] {b : BitVec 64}
    (hbase : blkPl03.base = b) (s0 : State) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x002c#64) s0
      (memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 32 ∗
        memRegion (s0.sp - 96#64) 32 ∗ memRegion (s0.sp - 64#64) 32 ∗
        memRegion (s0.sp - 32#64) 32 ∗ F)
      (fun sm Pm =>
        sm.sp = s0.sp - 160#64 ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = s0.readReg64 .x0 ∧ sm.readReg64 .x1 = s0.readReg64 .x1 ∧
        sm.readReg64 .x2 = s0.readReg64 .x2 ∧ sm.readReg64 .x3 = s0.readReg64 .x3 ∧
        sm.readReg64 .x4 = s0.readReg64 .x4 ∧ sm.readReg64 .x5 = s0.readReg64 .x5 ∧
        sm.readReg64 .x6 = s0.readReg64 .x6 ∧
        (Pm ⊢ SavedFrame03 (s0.sp - 160#64) s0 ∗ F)) := by
  subst hbase
  have hal160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 160#64)); intro f0 f1 f2 f3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 128#64)); intro f4 f5 f6 f7
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 96#64)); intro f8 f9 f10 f11
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro f12 f13 f14 f15
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro f16 f17 f18 f19
  simp only [
    bv_sub_add_eq_sub s0.sp 160#64 8#64 152#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 16#64 144#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 24#64 136#64 rfl,
    bv_sub_add_eq_sub s0.sp 128#64 8#64 120#64 rfl,
    bv_sub_add_eq_sub s0.sp 128#64 16#64 112#64 rfl,
    bv_sub_add_eq_sub s0.sp 128#64 24#64 104#64 rfl,
    bv_sub_add_eq_sub s0.sp 96#64 8#64 88#64 rfl,
    bv_sub_add_eq_sub s0.sp 96#64 16#64 80#64 rfl,
    bv_sub_add_eq_sub s0.sp 96#64 24#64 72#64 rfl,
    bv_sub_add_eq_sub s0.sp 64#64 8#64 56#64 rfl,
    bv_sub_add_eq_sub s0.sp 64#64 16#64 48#64 rfl,
    bv_sub_add_eq_sub s0.sp 64#64 24#64 40#64 rfl,
    bv_sub_add_eq_sub s0.sp 32#64 8#64 24#64 rfl,
    bv_sub_add_eq_sub s0.sp 32#64 16#64 16#64 rfl,
    bv_sub_add_eq_sub s0.sp 32#64 24#64 8#64 rfl]
  wp_steps 11
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hal160,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
  unfold SavedFrame03
  simp only [
    bv_sub_add_eq_sub s0.sp 160#64 8#64 152#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 16#64 144#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 24#64 136#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 32#64 128#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 40#64 120#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 48#64 112#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 56#64 104#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 64#64 96#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 72#64 88#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 80#64 80#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 88#64 72#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 96#64 64#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 104#64 56#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 112#64 48#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 120#64 40#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 128#64 32#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 136#64 24#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 144#64 16#64 rfl,
    bv_sub_add_eq_sub s0.sp 160#64 152#64 8#64 rfl]
  sep_frame

private theorem seg1_probes [MlKemPlacement] {b : BitVec 64}
    (hbase : blkPl03.base = b) (sm : State) (sp0 : BitVec 64) (a : MlkemBlk03Args) (F : SepProp)
    (hpc : sm.pc = b + 0x002c#64) (hrun : sm.status = .Running)
    (hsp : sm.sp = sp0 - 160#64) (hsp0_al : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : sm.readReg64 .x0 = a.ret) (hx1 : sm.readReg64 .x1 = a.hdrA)
    (hx2 : sm.readReg64 .x2 = a.randA) (hx3 : sm.readReg64 .x3 = a.esA)
    (hx4 : sm.readReg64 .x4 = 2080#64) (hx5 : sm.readReg64 .x5 = a.ssA)
    (hx6 : sm.readReg64 .x6 = 32#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0064#64) sm
      (memRegion (sp0 - 16544#64) 8 ∗ memRegion (sp0 - 12448#64) 8 ∗
        memRegion (sp0 - 8352#64) 8 ∗ memRegion (sp0 - 4256#64) 8 ∗ F)
      (fun s1 P1 =>
        s1.sp = sp0 - 17024#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = a.ret ∧ s1.readReg64 .x1 = a.hdrA ∧
        s1.readReg64 .x2 = a.randA ∧ s1.readReg64 .x3 = a.esA ∧
        s1.readReg64 .x4 = 2080#64 ∧ s1.readReg64 .x5 = a.ssA ∧
        (P1 ⊢ ((sp0 - 16544#64) ↦₆₄ 0#64) ∗ ((sp0 - 12448#64) ↦₆₄ 0#64) ∗
          ((sp0 - 8352#64) ↦₆₄ 0#64) ∗ ((sp0 - 4256#64) ↦₆₄ 0#64) ∗ F)) := by
  subst hbase
  have hal_sp' : ((sp0 - 17024#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub sp0 17024#64 hsp0_al (by decide)
  sep_frame_apply (sepWP_elim_cell8 (a := sp0 - 16544#64)); intro p0
  sep_frame_apply (sepWP_elim_cell8 (a := sp0 - 12448#64)); intro p1
  sep_frame_apply (sepWP_elim_cell8 (a := sp0 - 8352#64)); intro p2
  sep_frame_apply (sepWP_elim_cell8 (a := sp0 - 4256#64)); intro p3
  wp_steps 10
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hal_sp',
      by simp [hx0], by simp [hx1], by simp [hx2],
      by simp [hx3], by simp [hx4], by simp [hx5], ?_⟩
  sep_frame

theorem seg1_prologue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s0 : State) (a : MlkemBlk03Args) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.ret) (hx1 : s0.readReg64 .x1 = a.hdrA)
    (hx2 : s0.readReg64 .x2 = a.randA) (hx3 : s0.readReg64 .x3 = a.esA)
    (hx4 : s0.readReg64 .x4 = 2080#64) (hx5 : s0.readReg64 .x5 = a.ssA)
    (hx6 : s0.readReg64 .x6 = 32#64) :
    let sp := s0.sp - 17024#64
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0064#64) s0
      (stackAt s0.sp 18160 ∗ F)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = a.ret ∧ s1.readReg64 .x1 = a.hdrA ∧
        s1.readReg64 .x2 = a.randA ∧ s1.readReg64 .x3 = a.esA ∧
        s1.readReg64 .x4 = 2080#64 ∧ s1.readReg64 .x5 = a.ssA ∧
        (P1 ⊢ SavedFrame03 (sp + 16864#64) s0 ∗ memRegion sp 16864 ∗ stackAt sp 1136 ∗ F)) := by
  intro sp
  have hsave_eq : sp + 16864#64 = s0.sp - 160#64 :=
    bv_sub_add_eq_sub s0.sp 17024#64 16864#64 160#64 rfl
  rw [stackAt_18160_prologue_split s0.sp]
  refine SepWP.weaken_pre
    (P' := memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 32 ∗
      memRegion (s0.sp - 96#64) 32 ∗ memRegion (s0.sp - 64#64) 32 ∗
      memRegion (s0.sp - 32#64) 32 ∗
      (memRegion (s0.sp - 16544#64) 8 ∗ memRegion (s0.sp - 12448#64) 8 ∗
        memRegion (s0.sp - 8352#64) 8 ∗ memRegion (s0.sp - 4256#64) 8 ∗
        memRegion (s0.sp - 17024#64) 480 ∗ memRegion (s0.sp - 16536#64) 4088 ∗
        memRegion (s0.sp - 12440#64) 4088 ∗ memRegion (s0.sp - 8344#64) 4088 ∗
        memRegion (s0.sp - 4248#64) 4088 ∗ stackAt (s0.sp - 17024#64) 1136 ∗ F))
    (by sep_frame) ?_
  refine SepWP.seq (seg1_spill hbase s0 _ hpc hrun hsp0) ?_
  rintro sm Pm hpc_m hrun_m ⟨hsp_m, _hal_m, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx5_m, hx6_m, hPm⟩
  refine SepWP.weaken_pre (Entails.trans hPm (by sep_frame))
    (SepWP.mono (seg1_probes hbase sm s0.sp a _ hpc_m hrun_m hsp_m hsp0
      (hx0_m.trans hx0) (hx1_m.trans hx1) (hx2_m.trans hx2) (hx3_m.trans hx3)
      (hx4_m.trans hx4) (hx5_m.trans hx5) (hx6_m.trans hx6)) ?_)
  rintro s1 P1 _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, hP1⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, Entails.trans hP1 ?_⟩
  rw [hsave_eq]; dsimp only [sp]
  exact entails_sub (probes_restore_16864 s0.sp 0#64 0#64 0#64 0#64) (by sep_frame) (by sep_frame)

/-! ## 3. `G(m || H(pk))` Setup & `B00` Call (`+0x0064 → +0x00fc`) -/

private theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1
  rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

theorem seg1_hash_prep [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (Rest : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hpc : s.pc = b + 0x0064#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = a.ret) (hx1 : s.readReg64 .x1 = a.hdrA)
    (hx2 : s.readReg64 .x2 = a.randA) (hx3 : s.readReg64 .x3 = a.esA)
    (hx4 : s.readReg64 .x4 = 2080#64) (hx5 : s.readReg64 .x5 = a.ssA) :
    let msg := a.rand ++ a.hdr64.drop 32
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x00f8#64) s
      (memRegion sp 32 ∗ memRegion (sp + 32#64) 8 ∗
        memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 2224#64) 32 ∗
        memRegion (sp + 4272#64) 32 ∗ memRegion (sp + 4304#64) 32 ∗
        memRegion (sp + 13984#64) 32 ∗
        (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 13984#64 ∧
        sm.readReg64 .x1 = sp + 4272#64 ∧
        sm.readReg64 .x2 = sp + 6832#64 ∧
        sm.readReg64 .x19 = sp + 13984#64 ∧
        sm.readReg64 .x20 = sp + 4272#64 ∧
        sm.readReg64 .x21 = a.hdrA ∧
        sm.readReg64 .x22 = sp + 6832#64 ∧
        sm.readReg64 .x23 = sp + 2456#64 ∧
        sm.readReg64 (.gpr 24#5) = sp + 2192#64 ∧
        sm.readReg64 (.gpr 25#5) = sp + 14248#64 ∧
        sm.readReg64 .x28 = sp + 13984#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 13984#64) (sp + 2192#64) (sp + 2192#64)
            msg.length msg.length ∗
          ((sp + 2192#64) ↦ₛ msg) ∗
          memRegion (sp + 4272#64) 64 ∗
          SavedArgs03 sp a ∗
          (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ Rest)) := by
  intro msg
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have htake_len : (a.hdr64.take 32).length = 32 := by simp [hhdr]
  have hdrop_len : (a.hdr64.drop 32).length = 32 := by simp [hhdr]
  have hmsg_len : msg.length = 64 := by simp [msg, hrand, hhdr]
  have hhdr_split : (a.hdrA ↦ₛ a.hdr64) =
      (a.hdrA ↦ₛ a.hdr64.take 32) ∗ ((a.hdrA + 32#64) ↦ₛ a.hdr64.drop 32) := by
    conv_lhs => rw [← List.take_append_drop 32 a.hdr64]
    rw [pointsToBytes_append, htake_len]
  have o2192_8 : sp + 2192#64 + 8#64 = sp + 2200#64 := by bv_omega
  have o2192_16 : sp + 2192#64 + 16#64 = sp + 2208#64 := by bv_omega
  have o2192_24 : sp + 2192#64 + 24#64 = sp + 2216#64 := by bv_omega
  have o2224_8 : sp + 2224#64 + 8#64 = sp + 2232#64 := by bv_omega
  have o2224_16 : sp + 2224#64 + 16#64 = sp + 2240#64 := by bv_omega
  have o2224_24 : sp + 2224#64 + 24#64 = sp + 2248#64 := by bv_omega
  have o4272_8 : sp + 4272#64 + 8#64 = sp + 4280#64 := by bv_omega
  have o4272_16 : sp + 4272#64 + 16#64 = sp + 4288#64 := by bv_omega
  have o4272_24 : sp + 4272#64 + 24#64 = sp + 4296#64 := by bv_omega
  have o4304_8 : sp + 4304#64 + 8#64 = sp + 4312#64 := by bv_omega
  have o4304_16 : sp + 4304#64 + 16#64 = sp + 4320#64 := by bv_omega
  have o4304_24 : sp + 4304#64 + 24#64 = sp + 4328#64 := by bv_omega
  have o13984_8 : sp + 13984#64 + 8#64 = sp + 13992#64 := by bv_omega
  have o13984_16 : sp + 13984#64 + 16#64 = sp + 14000#64 := by bv_omega
  have o13984_24 : sp + 13984#64 + 24#64 = sp + 14008#64 := by bv_omega
  have ohdr_8 : a.hdrA + 32#64 + 8#64 = a.hdrA + 40#64 := by bv_omega
  have ohdr_16 : a.hdrA + 32#64 + 16#64 = a.hdrA + 48#64 := by bv_omega
  have ohdr_24 : a.hdrA + 32#64 + 24#64 = a.hdrA + 56#64 := by bv_omega
  have o2192_32 : sp + 2192#64 + BitVec.ofNat 64 32 = sp + 2224#64 := by bv_omega
  sep_frame_apply (sepWP_elim_region32 (a := sp)); intro s0c s1c s2c s3c
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 32#64)); intro s4c
  sep_frame_apply (sepWP_elim_region32 (a := sp + 2192#64)); intro m0 m1 m2 m3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 2224#64)); intro m4 m5 m6 m7
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4272#64)); intro z0 z1 z2 z3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4304#64)); intro z4 z5 z6 z7
  sep_frame_apply (sepWP_elim_region32 (a := sp + 13984#64)); intro k0 k1 k2 k3
  rw [hhdr_split, ← vec2_cells_eq_bytes a.randA hrand,
    ← vec2_cells_eq_bytes (a.hdrA + 32#64) hdrop_len]
  simp only [o2192_8, o2192_16, o2192_24, o2224_8, o2224_16, o2224_24,
    o4272_8, o4272_16, o4272_24, o4304_8, o4304_16, o4304_24,
    o13984_8, o13984_16, o13984_24, ohdr_8, ohdr_16, ohdr_24]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp, by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, ?_⟩
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  simp only [htrunc]
  have hz64 :
      ((sp + 4272#64) ↦₆₄ 0#64) ∗ ((sp + 4280#64) ↦₆₄ 0#64) ∗
        ((sp + 4288#64) ↦₆₄ 0#64) ∗ ((sp + 4296#64) ↦₆₄ 0#64) ∗
        ((sp + 4304#64) ↦₆₄ 0#64) ∗ ((sp + 4312#64) ↦₆₄ 0#64) ∗
        ((sp + 4320#64) ↦₆₄ 0#64) ∗ ((sp + 4328#64) ↦₆₄ 0#64) ⊢
      memRegion (sp + 4272#64) 64 := by
    rw [memRegion_split' (b' := sp + 4304#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
    have hz1 := cells32_entails_memRegion (sp + 4272#64) 0#64 0#64 0#64 0#64
    have hz2 := cells32_entails_memRegion (sp + 4304#64) 0#64 0#64 0#64 0#64
    simp only [o4272_8, o4272_16, o4272_24] at hz1
    simp only [o4304_8, o4304_16, o4304_24] at hz2
    exact entails_sub hz1 (by sep_frame) (entails_sub hz2 (by sep_frame) (by sep_frame))
  have hmsg_pts :
      ((sp + 2192#64) ↦₆₄ (bytesToVecNat a.rand 0).extractLsb' 0 64) ∗
        ((sp + 2200#64) ↦₆₄ (bytesToVecNat a.rand 0).extractLsb' 64 64) ∗
        ((sp + 2208#64) ↦₆₄ (bytesToVecNat a.rand 1).extractLsb' 0 64) ∗
        ((sp + 2216#64) ↦₆₄ (bytesToVecNat a.rand 1).extractLsb' 64 64) ∗
        ((sp + 2224#64) ↦₆₄ (bytesToVecNat (a.hdr64.drop 32) 0).extractLsb' 0 64) ∗
        ((sp + 2232#64) ↦₆₄ (bytesToVecNat (a.hdr64.drop 32) 0).extractLsb' 64 64) ∗
        ((sp + 2240#64) ↦₆₄ (bytesToVecNat (a.hdr64.drop 32) 1).extractLsb' 0 64) ∗
        ((sp + 2248#64) ↦₆₄ (bytesToVecNat (a.hdr64.drop 32) 1).extractLsb' 64 64) =
      ((sp + 2192#64) ↦ₛ msg) := by
    dsimp only [msg]
    rw [pointsToBytes_append, hrand, o2192_32,
      ← vec2_cells_eq_bytes (sp + 2192#64) hrand,
      ← vec2_cells_eq_bytes (sp + 2224#64) hdrop_len]
    simp only [o2192_8, o2192_16, o2192_24, o2224_8, o2224_16, o2224_24]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  have hsl :
      Keccak2SlicesRW (sp + 13984#64) (sp + 2192#64) (sp + 2192#64) msg.length msg.length =
        ((sp + 13984#64) ↦₆₄ (sp + 2192#64)) ∗ ((sp + 13992#64) ↦₆₄ 64#64) ∗
        ((sp + 14000#64) ↦₆₄ (sp + 2192#64)) ∗ ((sp + 14008#64) ↦₆₄ 64#64) := by
    unfold Keccak2SlicesRW
    simp only [hmsg_len, o13984_8, o13984_16, o13984_24]
  unfold SavedArgs03
  conv_rhs => rw [← hmsg_pts, hsl]
  exact entails_sub hz64 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
