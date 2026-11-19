/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowLoop

/-!
# `generate_keypair_compressed` (`B05`): Segment 2 outer matrix `Â` loop

Composes 3 iterations of `Seg2RowLoop`, `Seg2Epi`, and `seg2_row_header_{lt3,eq3}` across
`+0x02b8 → +0x3480` into both `seg2_matrix_safe_ok` (`SafeSepWP`, unconditional) and
`seg2_matrix_ok` (`SepWP`, under `Shake128MatrixTerminates rho 3`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 Shake128MatrixTerminates Shake128SeedTerminates sampleMatrixWith sampleNtt
  sha3_512List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blkPC05 blkPl05 cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  B05LateSlots Seg2ConstSlots entails_sub sepWP_elim_cell8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG (
  Seg1Post Seg1Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (BTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (
  TreeMem memRegion_entails_exists_treeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  rowSeed rowSeeds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2ConstWordsInv Seg2RegInv entry_treeMem_join exit_treeMem_entails offSeg3Entry
  seg2_row_header_eq3 seg2_row_header_lt3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowLoop (
  seg2_row_ok seg2_row_safe_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Epi (
  RowPolyOut seg2_epi_ok)

attribute [local irreducible] blkPC05 TreeMem

/-! ## 1. Transposed Matrix `Â` Layout (`AMatrixMem`) & Pure Seed Bridges -/

/-- Transposed `3 × 3` NTT matrix `Â` (`sampleMatrixWith sampleNtt 3 rho true`) stored row-major by
    `(col, row)` at `[sp + 3744, sp + 8352)`: entry `(col, row)` (`sampleNtt (rowSeed rho row col)`)
    occupies `[sp + 3744 + 1536 * col + 512 * row .. + 512)`. -/
@[expose] noncomputable def AMatrixMem (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ RowPolyOut sp rho 2

theorem sampleMatrixWith_true_getD {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {col row : Nat} (hc : col < 3) (hr : row < 3) :
    ((sampleMatrixWith sampleNtt 3 rho true).getD col #[]).getD row zeroPoly =
      sampleNtt (rowSeed rho row col) := by
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simp [sampleMatrixWith, rowSeed, Array.getD, hc, hr, htake]
private theorem shake128MatrixTerminates_row {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (hTerm : Shake128MatrixTerminates rho 3) {row col : Nat} (hr : row < 3) (hc : col < 3) :
    Shake128SeedTerminates (rowSeeds rho row col) := by
  have h := hTerm row col hr hc
  have htake : rho.take 32 = rho := List.take_of_length_le (Nat.le_of_eq hrho)
  simpa [rowSeeds, rowSeed, htake] using h

private theorem sha3_512List_take32_len (msg : List (BitVec 8)) :
    ((sha3_512List msg).take 32).length = 32 := by
  have h64 : (sha3_512List msg).length = 64 := by simp [sha3_512List, keccakSponge]
  simp [h64]

private theorem sepWP_elim_treeMem {prog : Program} {tgt : BitVec 64} {s : State}
    {ptr : BitVec 64} {len : Nat} (hlen : len ≤ 512) {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog tgt s (TreeMem ptr len t ∗ R) post oom) :
    SepWP prog tgt s (memRegion ptr (8 * len) ∗ R) post oom :=
  SepWP.weaken_pre (sepConj_mono_left (memRegion_entails_exists_treeMem hlen))
    (SepWP.of_sepExists_left h)

/-! ## 2. Entry/Exit Stack Region Splits & `Seg2MatrixExit` -/

private theorem memRegion_432_split (sp : BitVec 64) :
    memRegion (sp + 432#64) 3312 =
      memRegion (sp + 432#64) (8 * 222) ∗ memRegion (sp + 2208#64) 1536 :=
  memRegion_split' (b := sp + 432#64) (b' := sp + 2208#64) (n := 1776) (k := (1536 : Nat))
    rfl (by bv_omega) (by decide)

private theorem memRegion_3744_split9 (sp : BitVec 64) :
    memRegion (sp + 3744#64) 4608 =
      (memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 0)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0)) 512) ∗
      (memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 1)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 1)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 1)) 512) ∗
      (memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 2)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2)) 512 ∗
       memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2)) 512) := by
  have split1536 (base : BitVec 64) :
      memRegion base 1536 =
        memRegion (base + 0#64) 512 ∗ memRegion (base + 512#64) 512 ∗
          memRegion (base + 1024#64) 512 := by
    rw [BitVec.add_zero,
      memRegion_split' (b := base) (b' := base + 512#64) (n := 512) (k := (1024 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := base + 512#64) (b' := base + 1024#64) (n := 512) (k := (512 : Nat))
        rfl (by bv_omega) (by decide)]
  rw [memRegion_split' (b := sp + 3744#64) (b' := sp + 5280#64) (n := 1536) (k := (3072 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5280#64) (b' := sp + 6816#64) (n := 1536) (k := (1536 : Nat))
        rfl (by bv_omega) (by decide),
      split1536 (sp + 3744#64), split1536 (sp + 5280#64), split1536 (sp + 6816#64)]
  simp only [show sp + 5280#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0) by bv_omega,
    show sp + 5280#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 1) by bv_omega,
    show sp + 5280#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2) by bv_omega,
    show sp + 6816#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0) by bv_omega,
    show sp + 6816#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 1) by bv_omega,
    show sp + 6816#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2) by bv_omega,
    show sp + 3744#64 + 0#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 0) from rfl,
    show sp + 3744#64 + 512#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 1) from rfl,
    show sp + 3744#64 + 1024#64 = sp + 3744#64 + BitVec.ofNat 64 (512 * 2) from rfl]
  exact sepProp_ext (by sep_frame) (by sep_frame)
private def Seg2ScratchIdle (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8352#64) 1632 ∗
  memRegion (sp + 11496#64) 5880 ∗
  memRegion (sp + 19008#64) 8832 ∗
  memRegion (sp + 28360#64) 664 ∗
  memRegion (sp + 29048#64) 360

private theorem memRegion_8352_split (sp : BitVec 64) :
    memRegion (sp + 8352#64) 21056 =
      memRegion (sp + 9984#64) 1512 ∗
      memRegion (sp + 17376#64) 1632 ∗
      memRegion (sp + 27840#64) 504 ∗
      memRegion (sp + 28344#64) 16 ∗
      memRegion (sp + 29024#64) 24 ∗
      Seg2ScratchIdle sp := by
  unfold Seg2ScratchIdle
  rw [memRegion_split' (b := sp + 8352#64) (b' := sp + 9984#64) (n := 1632) (k := (19424 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 9984#64) (b' := sp + 11496#64) (n := 1512) (k := (17912 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11496#64) (b' := sp + 17376#64) (n := 5880) (k := (12032 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 17376#64) (b' := sp + 19008#64) (n := 1632) (k := (10400 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19008#64) (b' := sp + 27840#64) (n := 8832) (k := (1568 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 27840#64) (b' := sp + 28344#64) (n := 504) (k := (1064 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28344#64) (b' := sp + 28360#64) (n := 16) (k := (1048 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28360#64) (b' := sp + 29024#64) (n := 664) (k := (384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 29024#64) (b' := sp + 29048#64) (n := 24) (k := (360 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem exit_low_rejoin (sp : BitVec 64) (tA : BTree (BitVec 64) 9)
    (h9 : tA.get 9 = sp + 8416#64) :
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 2208#64) 1536 ⊢
      ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 56#64) 80 ∗
        ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 144#64) 3600 := by
  have h56 : ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ⊢ memRegion (sp + 56#64) 8 :=
    cell_entails_memRegion8 _ _
  have h80 : memRegion (sp + 56#64) 8 ∗ memRegion (sp + 64#64) 72 = memRegion (sp + 56#64) 80 :=
    (memRegion_split' (b := sp + 56#64) (b' := sp + 64#64) (n := 8) (k := (72 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have h3600 : memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 2208#64) 1536 =
      memRegion (sp + 144#64) 3600 :=
    (memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (1536 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine entails_sub (exit_treeMem_entails sp tA h9) (by sep_frame) ?_
  refine entails_sub h56 (by sep_frame) ?_
  rw [← h80, ← h3600]
  sep_frame

/-- Postcondition entering Segment 3 (`+0x3480`, `b + offSeg3Entry`). -/
@[expose] def Seg2MatrixExit [MlKemPlacement]
    (b : BitVec 64) (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  sf.pc = b + offSeg3Entry ∧
  sf.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  Seg2RegInv sp (s0.sp - 96#64) sf ∧
  (Pf ⊢ SavedFrame05 s0.sp s0 ∗
    stackAt sp 1136 ∗
    (seedA ↦ₛ seed) ∗
    (sp ↦ₛ g.take 32) ∗
    ((sp + 32#64) ↦₆₄ seedA) ∗
    ((sp + 40#64) ↦₆₄ outPtr) ∗
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
    memRegion (sp + 56#64) 80 ∗
    ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
    memRegion (sp + 144#64) 3600 ∗
    AMatrixMem sp (g.take 32) ∗
    memRegion (sp + 8352#64) 21056 ∗
    ((sp + 29408#64) ↦ₛ g.drop 32) ∗
    memRegion (sp + 29440#64) 480 ∗
    F)
/-! ## 3. Full 3-Row `Seg2Matrix` Proofs (`SafeSepWP` & `SepWP`) -/

private def RowCells (sp : BitVec 64) (row : Nat) : SepProp :=
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗
  memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512

private theorem constWords_t5 {sp : BitVec 64} {rho : List (BitVec 8)} {tA : BTree (BitVec 64) 9}
    (h : Seg2ConstWordsInv sp rho tA) : tA.get 5 = sp + 27851#64 := by
  rcases h with ⟨_, _, _, _, h5, _⟩; exact h5

private theorem constWords_t9 {sp : BitVec 64} {rho : List (BitVec 8)} {tA : BTree (BitVec 64) 9}
    (h : Seg2ConstWordsInv sp rho tA) : tA.get 9 = sp + 8416#64 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, h9, _⟩; exact h9

private theorem seg1Post_to_seg2 [MlKemPlacement] {s0 s : State} (hp : Seg1Post s0 s) :
    Seg2RegInv (s0.sp - 30080#64) (s0.sp - 96#64) s ∧ s.readReg64 .x1 = 0#64 := by
  rcases hp with ⟨hsp, hal, hfp, hx1, hx19, hx20, hx21, hx23, hx24, hx26, hx27, hx28⟩
  exact ⟨⟨⟨hsp, hal, hfp, hx19, hx21, hx24, hx26, hx27, hx28⟩, hx20, hx23⟩, hx1⟩

private def Seg2IdlePassthrough (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
    (sp ↦ₛ g.take 32) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
    memRegion (sp + 2208#64) 1536 ∗ Seg2ScratchIdle sp ∗
    ((sp + 29408#64) ↦ₛ g.drop 32) ∗ memRegion (sp + 29440#64) 480 ∗ F

private theorem exit_full_entails (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (tA : BTree (BitVec 64) 9)
    (ht9 : tA.get 9 = s0.sp - 30080#64 + 8416#64) :
    let sp := s0.sp - 30080#64
    let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
    RowPolyOut sp rho 2 ∗ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
      memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
      memRegion (sp + 28344#64) 16 ∗ memRegion (sp + 29024#64) 24 ∗
      (RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ Seg2IdlePassthrough s0 seedA outPtr seed F) ⊢
    SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
      (sp ↦ₛ rho) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
      ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 56#64) 80 ∗
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
      memRegion (sp + 144#64) 3600 ∗ AMatrixMem sp rho ∗
      memRegion (sp + 8352#64) 21056 ∗
      ((sp + 29408#64) ↦ₛ (sha3_512List (seed.take 32 ++ [3#8])).drop 32) ∗
      memRegion (sp + 29440#64) 480 ∗ F := by
  intro sp rho
  unfold Seg2IdlePassthrough AMatrixMem
  rw [memRegion_8352_split sp]
  exact entails_sub (exit_low_rejoin sp tA ht9) (by sep_frame) (by sep_frame)
private theorem entry_spatial_prep (s0 : State) (seedA outPtr w4 : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) (tMid tHi : BTree (BitVec 64) 9) :
    let sp := s0.sp - 30080#64
    let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
    ∃ tA0 : BTree (BitVec 64) 9,
      Seg2ConstWordsInv sp rho tA0 ∧
      (TreeMem (sp + 432#64) 222 tHi ∗ TreeMem (sp + 144#64) 26 tMid ∗ ((sp + 96#64) ↦₆₄ w4) ∗
        (SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
          ((sp ↦ₛ rho) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
            ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
            ((sp + 29408#64) ↦ₛ (sha3_512List (seed.take 32 ++ [3#8])).drop 32) ∗
            memRegion (sp + 29440#64) 480) ∗
          Seg2ConstSlots sp rho ∗ memRegion (sp + 2208#64) 1536 ∗
          memRegion (sp + 3744#64) 4608 ∗ memRegion (sp + 8352#64) 21056 ∗ F) ⊢
        TreeMem (sp + 64#64) 268 tA0 ∗ memRegion (sp + 9984#64) 1512 ∗
          memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
          memRegion (sp + 29024#64) 24 ∗
          (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
            memRegion (sp + 28344#64) 16 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 0)) 512 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 0)) 512 ∗
            memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 0)) 512 ∗
            (RowCells sp 1 ∗ RowCells sp 2 ∗ Seg2IdlePassthrough s0 seedA outPtr seed F))) := by
  intro sp rho
  rcases entry_treeMem_join sp w4 rho tMid tHi with ⟨tA0, htA0, hjoin⟩
  refine ⟨tA0, htA0, ?_⟩
  unfold RowCells Seg2IdlePassthrough
  rw [memRegion_3744_split9 sp, memRegion_8352_split sp]
  exact entails_sub
    (A := Seg2ConstSlots sp rho ∗ ((sp + 96#64) ↦₆₄ w4) ∗ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
      TreeMem (sp + 144#64) 26 tMid ∗ TreeMem (sp + 432#64) 222 tHi)
    (B := ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      TreeMem (sp + 64#64) 268 tA0)
    (by rw [hjoin]; exact Entails.refl _) (by sep_frame) (by sep_frame)

private theorem seg2_epi_lt3_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hr2 : row < 2)
    {s : State} {P : SepProp}
    (hexit : Seg2Init.Seg2RowDone b sp fpVal rho row
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        memRegion (sp + 28344#64) 16 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * row)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * row)) 512 ∗ Rest) s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) s P
      (fun sf Pf =>
        sf.pc = b + 0x02b8#64 ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp fpVal sf ∧ sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
        ∃ tA : BTree (BitVec 64) 9, Seg2ConstWordsInv sp rho tA ∧
          (Pf ⊢ TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
            memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
            memRegion (sp + 29024#64) 24 ∗
            (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
              memRegion (sp + 28344#64) 16 ∗ RowPolyOut sp rho row ∗ Rest))) := by
  refine SepWP.seq (seg2_epi_ok hb hbase (by omega) hexit) ?_
  rintro sh Ph hpch hrunh ⟨hclh, hroh, hgbh, hx1h, tA, htA, hPh⟩
  refine sepWP_seq_env hclh hroh
    (SepWP.weaken_pre
      (Entails.trans hPh (show _ ⊢ TreeMem (sp + 64#64) 268 tA ∗ _ by sep_frame))
      (seg2_row_header_lt3 hb hbase sh sp fpVal (row + 1) tA _ (by omega) (constWords_t5 htA)
        hpch hrunh hgbh hx1h)) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hregf, hx1f, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hpcf, hrunf, hclf, hrof, hregf, hx1f, tA, htA, Entails.trans hPf (by sep_frame)⟩

private theorem seg2_epi_eq2_ok [MlKemPlacement] {b sp fpVal : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    {rho : List (BitVec 8)} {Rest : SepProp} {s : State} {P : SepProp}
    (hexit : Seg2Init.Seg2RowDone b sp fpVal rho 2
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        memRegion (sp + 28344#64) 16 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * 2)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * 2)) 512 ∗
        memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * 2)) 512 ∗ Rest) s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offSeg3Entry) s P
      (fun sf Pf =>
        sf.pc = b + offSeg3Entry ∧ sf.status = .Running ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        Seg2RegInv sp fpVal sf ∧
        ∃ tA : BTree (BitVec 64) 9, Seg2ConstWordsInv sp rho tA ∧
          (Pf ⊢ RowPolyOut sp rho 2 ∗
            ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
            TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
            memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
            memRegion (sp + 28344#64) 16 ∗ memRegion (sp + 29024#64) 24 ∗ Rest)) := by
  refine SepWP.seq (seg2_epi_ok hb hbase (by decide) hexit) ?_
  rintro sh Ph hpch hrunh ⟨hclh, hroh, hgbh, hx1h, tA, htA, hPh⟩
  refine sepWP_seq_env hclh hroh
    (SepWP.weaken_pre
      (Entails.trans hPh (show _ ⊢ TreeMem (sp + 64#64) 268 tA ∗ _ by sep_frame))
      (seg2_row_header_eq3 hb hbase sh sp fpVal tA _ (constWords_t5 htA) hpch hrunh hgbh hx1h)) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hregf, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hpcf, hrunf, hclf, hrof, hregf, tA, htA, Entails.trans hPf (by sep_frame)⟩

attribute [local irreducible] RowPolyOut

theorem seg2_matrix_safe_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    (hpc : s.pc = b + 0x02b8#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpost : Seg1Post s0 s) :
    SafeSepWP (blkPC05.rebase b (fun _ => none)) s
      (Seg1Spatial s0 seedA outPtr seed F)
      (Seg2MatrixExit b s0 seedA outPtr seed F) := by
  let sp := s0.sp - 30080#64
  let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
  have hrho : rho.length = 32 := sha3_512List_take32_len _
  rcases seg1Post_to_seg2 hpost with ⟨hreg0, hx1_0⟩
  refine SafeSepWP.of_sepWP (mid := s.pc) ?_
  dsimp only [Seg1Spatial, B05LateSlots]
  rw [memRegion_432_split sp, show (208 : Nat) = 8 * 26 from rfl]
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) 8 ∗
    (memRegion (sp + 144#64) (8 * 26) ∗ memRegion (sp + 432#64) (8 * 222) ∗ _)) (by sep_frame) ?_
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 96#64)); intro w4
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) (8 * 26) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 26) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 432#64) (8 * 222) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_spatial_prep s0 seedA outPtr w4 seed F tMid tHi with ⟨tA0, htA0, hprep⟩
  refine SepWP.done rfl hrun ?_
  let idle := Seg2IdlePassthrough s0 seedA outPtr seed F
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 0) (by decide) htA0 hpc hrun hcl hro hreg0 hx1_0)
    fun sm0 Pm0 hex0 => SafeSepWP.of_sepWP <| SepWP.mono
      (seg2_epi_lt3_ok hb hbase (row := 0) (Rest := RowCells sp 1 ∗ RowCells sp 2 ∗ idle) (by decide) hex0) ?_)
    (Entails.trans (by sep_frame) hprep)
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx1_1, tA1, htA1, hP1⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 1) (by decide) htA1 hpc1 hrun1 hcl1 hro1 hreg1 hx1_1)
    fun sm1 Pm1 hex1 => SafeSepWP.of_sepWP <| SepWP.mono
      (seg2_epi_lt3_ok hb hbase (row := 1) (Rest := RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle) (by decide) hex1) ?_)
    (Entails.trans hP1 (by dsimp only [RowCells]; sep_frame))
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx1_2, tA2, htA2, hP2⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg2_row_safe_ok hb hbase hrho (row := 2) (by decide) htA2 hpc2 hrun2 hcl2 hro2 hreg2 hx1_2)
    fun sm2 Pm2 hex2 => SafeSepWP.of_sepWP <| SepWP.mono
      (seg2_epi_eq2_ok hb hbase (Rest := RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ idle) hex2) ?_)
    (Entails.trans hP2 (by dsimp only [RowCells]; sep_frame))
  rintro s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, tA3, htA3, hP3⟩
  exact SafeSepWP.done ⟨hpc3, hrun3, hcl3, hro3, hreg3,
    Entails.trans hP3 (exit_full_entails s0 seedA outPtr seed F tA3 (constWords_t9 htA3))⟩

theorem seg2_matrix_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    (hTerm : Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3)
    (hpc : s.pc = b + 0x02b8#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpost : Seg1Post s0 s) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offSeg3Entry) s
      (Seg1Spatial s0 seedA outPtr seed F)
      (Seg2MatrixExit b s0 seedA outPtr seed F) := by
  let sp := s0.sp - 30080#64
  let rho := (sha3_512List (seed.take 32 ++ [3#8])).take 32
  have hrho : rho.length = 32 := sha3_512List_take32_len _
  rcases seg1Post_to_seg2 hpost with ⟨hreg0, hx1_0⟩
  dsimp only [Seg1Spatial, B05LateSlots]
  rw [memRegion_432_split sp, show (208 : Nat) = 8 * 26 from rfl]
  refine SepWP.weaken_pre (P' := memRegion (sp + 96#64) 8 ∗
    (memRegion (sp + 144#64) (8 * 26) ∗ memRegion (sp + 432#64) (8 * 222) ∗ _)) (by sep_frame) ?_
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 96#64)); intro w4
  refine SepWP.weaken_pre (P' := memRegion (sp + 144#64) (8 * 26) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 26) (by decide) fun tMid => ?_
  refine SepWP.weaken_pre (P' := memRegion (sp + 432#64) (8 * 222) ∗ _) (by sep_frame) ?_
  refine sepWP_elim_treeMem (len := 222) (by decide) fun tHi => ?_
  rcases entry_spatial_prep s0 seedA outPtr w4 seed F tMid tHi with ⟨tA0, htA0, hprep⟩
  let idle := Seg2IdlePassthrough s0 seedA outPtr seed F
  let epiF (r : Nat) (R : SepProp) : SepProp :=
    ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
      memRegion (sp + 28344#64) 16 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (512 * r)) 512 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (1536 + 512 * r)) 512 ∗
      memRegion (sp + 3744#64 + BitVec.ofNat 64 (3072 + 512 * r)) 512 ∗ R
  let rowPre (tA : BTree (BitVec 64) 9) (FF : SepProp) : SepProp :=
    TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
      memRegion (sp + 17376#64) 1632 ∗ memRegion (sp + 27840#64) 504 ∗
      memRegion (sp + 29024#64) 24 ∗ FF
  refine SepWP.weaken_pre (P' := rowPre tA0 (epiF 0 (RowCells sp 1 ∗ RowCells sp 2 ∗ idle)))
    (Entails.trans (by sep_frame) (Entails.trans hprep (by dsimp only [rowPre, epiF]; sep_frame))) ?_
  refine SepWP.seq (seg2_row_ok hb hbase hrho (row := 0) (by decide)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by decide) hc) htA0
    (F := epiF 0 (RowCells sp 1 ∗ RowCells sp 2 ∗ idle)) hpc hrun hcl hro hreg0 hx1_0) ?_
  rintro sm0 Pm0 _ _ hex0
  refine SepWP.seq
    (seg2_epi_lt3_ok hb hbase (row := 0) (Rest := RowCells sp 1 ∗ RowCells sp 2 ∗ idle) (by decide) hex0) ?_
  rintro s1 P1 _ _ ⟨hpc1, hrun1, hcl1, hro1, hreg1, hx1_1, tA1, htA1, hP1⟩
  refine SepWP.weaken_pre (P' := rowPre tA1 (epiF 1 (RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle)))
    (Entails.trans hP1 (by dsimp only [rowPre, epiF, RowCells]; sep_frame)) ?_
  refine SepWP.seq (seg2_row_ok hb hbase hrho (row := 1) (by decide)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by decide) hc) htA1
    (F := epiF 1 (RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle)) hpc1 hrun1 hcl1 hro1 hreg1 hx1_1) ?_
  rintro sm1 Pm1 _ _ hex1
  refine SepWP.seq
    (seg2_epi_lt3_ok hb hbase (row := 1) (Rest := RowPolyOut sp rho 0 ∗ RowCells sp 2 ∗ idle) (by decide) hex1) ?_
  rintro s2 P2 _ _ ⟨hpc2, hrun2, hcl2, hro2, hreg2, hx1_2, tA2, htA2, hP2⟩
  refine SepWP.weaken_pre (P' := rowPre tA2 (epiF 2 (RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ idle)))
    (Entails.trans hP2 (by dsimp only [rowPre, epiF, RowCells]; sep_frame)) ?_
  refine SepWP.seq (seg2_row_ok hb hbase hrho (row := 2) (by decide)
    (fun c hc => shake128MatrixTerminates_row hrho hTerm (by decide) hc) htA2
    (F := epiF 2 (RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ idle)) hpc2 hrun2 hcl2 hro2 hreg2 hx1_2) ?_
  rintro sm2 Pm2 _ _ hex2
  refine SepWP.mono
    (seg2_epi_eq2_ok hb hbase (Rest := RowPolyOut sp rho 0 ∗ RowPolyOut sp rho 1 ∗ idle) hex2) ?_
  rintro s3 P3 _ _ ⟨hpc3, hrun3, hcl3, hro3, hreg3, tA3, htA3, hP3⟩
  exact ⟨hpc3, hrun3, hcl3, hro3, hreg3,
    Entails.trans hP3 (exit_full_entails s0 seedA outPtr seed F tA3 (constWords_t9 htA3))⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix
