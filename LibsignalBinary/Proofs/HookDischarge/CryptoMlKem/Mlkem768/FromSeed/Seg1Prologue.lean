/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge

/-!
# `generate_keypair_compressed` (`B05`) — Segment 1a Prologue (`+0x0000 .. +0x0040`)

Covers:
1. Shared stack-slot bundles (`Seg2ConstSlots`, `B05LateSlots`) and `SepWP` region-elimination
   combinators (`sepWP_elim_cell8`, `sepWP_elim_vec128`, `sepWP_elim_poly32`, `sepWP_elim_bytes`).
2. Callee-saved register spill `SavedFrame05 s0.sp s0` (`[s0.sp - 160, s0.sp)`) and 7-iteration
   `-fstack-clash-protection` page-probe loop (`+0x0000 .. +0x0040`), yielding
   `SavedFrame05 s0.sp s0 ∗ memRegion (s0.sp - 30080#64) 29920 ∗ stackAt (s0.sp - 30080#64) 1136`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (packLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion32_cells
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05
  blk05_code_eq
  blk05_tree_size
  blkLib05
  blkPC05
  blkPl05
  blkPlaceable05
  blkTree05
  cell_entails_memRegion8
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  Vec128At
  Vec32
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x0000 → 0x0040]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC05

/-! ## 1. Stack Slot Bundles & Shared Combinators -/

/-- Read-only stack slots at `sp` used by `Seg2` (`SampleNTT` matrix loop). -/
@[expose] def Seg2ConstSlots (sp : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
  ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
  Vec128At (sp + 64#64) 0x000000000000000000000000001f0200#128 ∗
  Vec128At (sp + 80#64) 0x000000000000000000000000001f0100#128 ∗
  ((sp + 104#64) ↦₆₄ (sp + 27851#64)) ∗
  ((sp + 112#64) ↦₆₄ (sp + 9995#64)) ∗
  ((sp + 120#64) ↦₆₄ (sp + 11288#64)) ∗
  ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
  Vec128At (sp + 352#64) 0xffffffffffffffffffffffffff0000ff#128 ∗
  Vec128At (sp + 368#64) (packLane64 rho 24 ++ packLane64 rho 24) ∗
  Vec128At (sp + 384#64) (packLane64 rho 16 ++ packLane64 rho 16) ∗
  Vec128At (sp + 400#64) (packLane64 rho 8 ++ packLane64 rho 8) ∗
  Vec128At (sp + 416#64) (packLane64 rho 0 ++ packLane64 rho 0)

/-- Stack slots at `sp` untouched by `Seg2` and consumed in `Seg3`..`Seg5` (`rho`, `seedA`,
    `outPtr`, `sHat` base pointer `sp + 8416`, `sigma`, and high scratch `[29440, 29920)`). -/
@[expose] def B05LateSlots (sp seedA outPtr : BitVec 64)
    (rho sigma : List (BitVec 8)) : SepProp :=
  (sp ↦ₛ rho) ∗
  ((sp + 32#64) ↦₆₄ seedA) ∗
  ((sp + 40#64) ↦₆₄ outPtr) ∗
  memRegion (sp + 96#64) 8 ∗
  ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
  ((sp + 29408#64) ↦ₛ sigma) ∗
  memRegion (sp + 29440#64) 480

theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

theorem vec128At_entails_memRegion16 (a : BitVec 64) (v : BitVec 128) :
    Vec128At a v ⊢ memRegion a 16 := by
  unfold Vec128At
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)

theorem sepWP_elim_cell8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target s ((a ↦₆₄ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post :=
  SepWP.memRegion8_cell a h

theorem sepWP_elim_vec128 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 128, SepWP prog target s (Vec128At a v ∗ R0) post) :
    SepWP prog target s (memRegion a 16 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := a)); intro lo
  sep_frame_apply (sepWP_elim_cell8 (a := a + 8#64)); intro hi
  have hvec : Vec128At a (hi ++ lo) = (a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi) := by
    unfold Vec128At
    have h0 : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
    have h1 : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
    rw [h0, h1]
  refine SepWP.weaken_pre ?_ (h (hi ++ lo))
  rw [hvec]
  sep_frame

theorem sepWP_elim_bytes {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) {R0 : SepProp}
    {post : State → SepProp → Prop}
    (h : ∀ bs : List (BitVec 8), bs.length = n → SepWP prog target s ((a ↦ₛ bs) ∗ R0) post) :
    SepWP prog target s (memRegion a n ∗ R0) post :=
  SepWP.memRegion_bytes a n hn rfl h

theorem sepWP_elim_poly32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Vec32, SepWP prog target s (Poly32Mem a t ∗ R0) post) :
    SepWP prog target s (memRegion a 512 ∗ R0) post := by
  refine sepWP_elim_bytes 512 (by decide) fun bs hlen => ?_
  have hpoly : (a ↦ₛ bs) = Poly32Mem a (Vec32.ofFn (Encaps2.VecMem.bytesToVecNat bs)) := by
    rw [Encaps2.VecMem.poly32Mem_ofFn]
    exact Encaps2.VecMem.pointsToBytes_eq_vecRangeMem 32 a hlen
  rw [hpoly]
  exact h _

/-! ## 2. Sub-Segment 1a: Callee-Saved Spill & 7-Page Stack Probe (`+0x0000 → +0x0040`) -/

private theorem seg1_spill [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 : State) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0030#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 160#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x9 = s0.sp - 28832#64 ∧
        s1.readReg64 .fp = s0.sp - 96#64 ∧
        (P1 ⊢ SavedFrame05 s0.sp s0 ∗ F)) := by
  subst hbase
  have h160 : memRegion (s0.sp - 160#64) 160 =
      memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 32 ∗
        memRegion (s0.sp - 96#64) 32 ∗ memRegion (s0.sp - 64#64) 32 ∗
        memRegion (s0.sp - 32#64) 32 := by
    rw [memRegion_split' (b' := s0.sp - 128#64) (n := 32) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := s0.sp - 96#64) (n := 32) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := s0.sp - 64#64) (n := 32) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := s0.sp - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
  rw [h160]
  apply memRegion32_cells (s0.sp - 160#64); intro c0 c1 c2 c3
  apply memRegion32_cells (s0.sp - 128#64); intro c4 c5 c6 c7
  apply memRegion32_cells (s0.sp - 96#64); intro c8 c9 c10 c11
  apply memRegion32_cells (s0.sp - 64#64); intro c12 c13 c14 c15
  apply memRegion32_cells (s0.sp - 32#64); intro c16 c17 c18 c19
  have hsp160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  have a17 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  have a18 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_omega
  have a19 : s0.sp - 32#64 + 24#64 = s0.sp - 8#64 := by bv_omega
  rw [a17, a18, a19]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simpa [State.spAligned] using hsp160, by simp, by simp,
      by simp, by simp, ?_⟩
  unfold SavedFrame05
  sep_frame

private theorem probe_page_step [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (x9 diff : BitVec 64) (F : SepProp)
    (hpc : s.pc = b + 0x0030#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = x9 + diff)
    (hsp_al : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = x9)
    (hne : (x9 + (diff - 4096#64) != x9) = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0030#64) s
      (memRegion (x9 + (diff - 4096#64)) 4096 ∗ F)
      (fun s1 P1 =>
        s1.sp = x9 + (diff - 4096#64) ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x9 = x9 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        (P1 ⊢ memRegion (x9 + (diff - 4096#64)) 4096 ∗ F)) := by
  subst hbase
  let nextSp := x9 + (diff - 4096#64)
  have hsub : x9 + diff - 4096#64 = nextSp := by dsimp [nextSp]; bv_omega
  have hnext_al : ((x9 + diff - 4096#64) &&& 15#64 == 0#64) = true := by
    rw [← hsp]
    exact spAligned_sub s.sp 4096#64 hsp_al (by decide)
  have hnext_al' : (nextSp &&& 15#64 == 0#64) = true := hsub ▸ hnext_al
  have hne' : (nextSp != x9) = true := hne
  rw [memRegion_split' (b' := nextSp + 8#64) (n := 8) (k := (4088 : Nat))
    rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := nextSp)); intro p0
  wp_step
  wp_step
  wp_step
  wp_step
  refine SepWP.done (by simp) (by simp [hrun])
    ⟨by simp [nextSp], by simpa [State.spAligned] using hnext_al',
      by simp, by simp, by simp [hx9], by simp, ?_⟩
  have hfold : (nextSp ↦₆₄ 0#64) ∗ memRegion (nextSp + 8#64) 4088 ⊢
      memRegion nextSp 4096 := by
    rw [memRegion_split' (b' := nextSp + 8#64) (n := 8) (k := (4088 : Nat))
      rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  exact entails_sub hfold (by sep_frame) (by sep_frame)

private theorem probe_page_last [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (x9 : BitVec 64) (F : SepProp)
    (hpc : s.pc = b + 0x0030#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = x9 + 4096#64)
    (hsp_al : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = x9) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0040#64) s
      (memRegion x9 4096 ∗ F)
      (fun s1 P1 =>
        s1.sp = x9 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        (P1 ⊢ memRegion x9 4096 ∗ F)) := by
  subst hbase
  have hsub : x9 + 4096#64 - 4096#64 = x9 := by bv_omega
  have hnext_al : ((x9 + 4096#64 - 4096#64) &&& 15#64 == 0#64) = true := by
    rw [← hsp]
    exact spAligned_sub s.sp 4096#64 hsp_al (by decide)
  have hx9_al : (x9 &&& 15#64 == 0#64) = true := hsub ▸ hnext_al
  rw [memRegion_split' (b' := x9 + 8#64) (n := 8) (k := (4088 : Nat))
    rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := x9)); intro p0
  wp_step
  wp_step
  wp_step
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simpa [State.spAligned] using hx9_al,
      by simp, by simp, by simp, ?_⟩
  have hfold : (x9 ↦₆₄ 0#64) ∗ memRegion (x9 + 8#64) 4088 ⊢ memRegion x9 4096 := by
    rw [memRegion_split' (b' := x9 + 8#64) (n := 8) (k := (4088 : Nat))
      rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  exact entails_sub hfold (by sep_frame) (by sep_frame)

private theorem bne_add_pos (x9 d : BitVec 64) (hd : d ≠ 0#64) :
    (x9 + d != x9) = true := by
  rw [bne_iff_ne]
  intro heq
  apply hd
  bv_omega

theorem seg1_spill_and_probe [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 : State) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro0 : MlKemRoOk mlkemMpl s0.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0040#64) s0
      (stackAt s0.sp 31216 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 28832#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .fp = s0.sp - 96#64 ∧
        (P1 ⊢ SavedFrame05 s0.sp s0 ∗ memRegion (s0.sp - 30080#64) 29920 ∗
          stackAt (s0.sp - 30080#64) 1136 ∗ F)) := by
  let x9 := s0.sp - 28832#64
  have htop : stackAt s0.sp 31216 =
      memRegion (s0.sp - 160#64) 160 ∗
        memRegion (s0.sp - 30080#64) 1248 ∗
        memRegion x9 4096 ∗
        memRegion (x9 + 4096#64) 4096 ∗
        memRegion (x9 + 8192#64) 4096 ∗
        memRegion (x9 + 12288#64) 4096 ∗
        memRegion (x9 + 16384#64) 4096 ∗
        memRegion (x9 + 20480#64) 4096 ∗
        memRegion (x9 + 24576#64) 4096 ∗
        stackAt (s0.sp - 30080#64) 1136 := by
    unfold stackAt
    have hs1 : s0.sp - 30080#64 - BitVec.ofNat 64 1136 = s0.sp - BitVec.ofNat 64 31216 := by
      bv_omega
    rw [hs1,
      memRegion_split' (b' := s0.sp - 30080#64) (n := 1136) (k := (30080 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9) (n := 1248) (k := (28832 : Nat))
        rfl (by dsimp [x9]; bv_omega) (by decide),
      memRegion_split' (b' := x9 + 4096#64) (n := 4096) (k := (24736 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 8192#64) (n := 4096) (k := (20640 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 12288#64) (n := 4096) (k := (16544 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 16384#64) (n := 4096) (k := (12448 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 20480#64) (n := 4096) (k := (8352 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 24576#64) (n := 4096) (k := (4256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := s0.sp - 160#64) (n := 4096) (k := 160)
        rfl (by dsimp [x9]; bv_omega) (by decide)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [htop]
  refine sepWP_seq_env hcl0 hro0
    (SepWP.weaken_pre (by sep_frame) (seg1_spill hb hbase s0 _ hpc hrun hsp0)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hal1, hx0_1, hx1_1, hx9_1, hfp1, hP1⟩
  have stepProbe := fun {s : State} {P : SepProp} {d : BitVec 64}
      (hd : (d - 4096#64) ≠ 0#64) (Rest : SepProp)
      (hP : P ⊢ memRegion (x9 + (d - 4096#64)) 4096 ∗ Rest)
      (hpc_s : s.pc = b + 0x0030#64) (hrun_s : s.status = .Running)
      (hsp_s : s.sp = x9 + d) (hal_s : s.spAligned = true)
      (hx9_s : s.readReg64 .x9 = x9) =>
    SepWP.weaken_pre hP
      (probe_page_step hb hbase s x9 d Rest hpc_s hrun_s hsp_s hal_s hx9_s
        (bne_add_pos x9 (d - 4096#64) hd))
  refine sepWP_seq_env hcl1 hro1
    (stepProbe (d := 28672#64) (by decide) _
      (Entails.trans hP1 (by rw [show (28672#64 : BitVec 64) - 4096#64 = 24576#64 by decide]; sep_frame))
      hpc1 hrun1 (by rw [hsp1]; dsimp [x9]; bv_omega) hal1 hx9_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hal2, hx0_2, hx1_2, hx9_2, hfp2, hP2⟩
  refine sepWP_seq_env hcl2 hro2
    (stepProbe (d := 24576#64) (by decide) _
      (Entails.trans hP2 (by
        rw [show (28672#64 : BitVec 64) - 4096#64 = 24576#64 by decide,
            show (24576#64 : BitVec 64) - 4096#64 = 20480#64 by decide]; sep_frame))
      hpc2 hrun2 (by simpa using hsp2) hal2 hx9_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hal3, hx0_3, hx1_3, hx9_3, hfp3, hP3⟩
  refine sepWP_seq_env hcl3 hro3
    (stepProbe (d := 20480#64) (by decide) _
      (Entails.trans hP3 (by
        rw [show (24576#64 : BitVec 64) - 4096#64 = 20480#64 by decide,
            show (20480#64 : BitVec 64) - 4096#64 = 16384#64 by decide]; sep_frame))
      hpc3 hrun3 (by simpa using hsp3) hal3 hx9_3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hal4, hx0_4, hx1_4, hx9_4, hfp4, hP4⟩
  refine sepWP_seq_env hcl4 hro4
    (stepProbe (d := 16384#64) (by decide) _
      (Entails.trans hP4 (by
        rw [show (20480#64 : BitVec 64) - 4096#64 = 16384#64 by decide,
            show (16384#64 : BitVec 64) - 4096#64 = 12288#64 by decide]; sep_frame))
      hpc4 hrun4 (by simpa using hsp4) hal4 hx9_4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hal5, hx0_5, hx1_5, hx9_5, hfp5, hP5⟩
  refine sepWP_seq_env hcl5 hro5
    (stepProbe (d := 12288#64) (by decide) _
      (Entails.trans hP5 (by
        rw [show (16384#64 : BitVec 64) - 4096#64 = 12288#64 by decide,
            show (12288#64 : BitVec 64) - 4096#64 = 8192#64 by decide]; sep_frame))
      hpc5 hrun5 (by simpa using hsp5) hal5 hx9_5) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hal6, hx0_6, hx1_6, hx9_6, hfp6, hP6⟩
  refine sepWP_seq_env hcl6 hro6
    (stepProbe (d := 8192#64) (by decide) _
      (Entails.trans hP6 (by
        rw [show (12288#64 : BitVec 64) - 4096#64 = 8192#64 by decide,
            show (8192#64 : BitVec 64) - 4096#64 = 4096#64 by decide]; sep_frame))
      hpc6 hrun6 (by simpa using hsp6) hal6 hx9_6) ?_
  rintro s7 P7 hpc7 hrun7 _ _ ⟨hsp7, hal7, hx0_7, hx1_7, hx9_7, hfp7, hP7⟩
  refine SepWP.mono
    (SepWP.weaken_pre
      (Entails.trans hP7 (by
        rw [show (8192#64 : BitVec 64) - 4096#64 = 4096#64 by decide]; sep_frame))
      (probe_page_last hb hbase s7 x9 _ hpc7 hrun7 (by simpa using hsp7) hal7 hx9_7)) ?_
  rintro s8 P8 _ _ ⟨hsp8, hal8, hx0_8, hx1_8, hfp8, hP8⟩
  refine ⟨hsp8, hal8,
    by rw [hx0_8, hx0_7, hx0_6, hx0_5, hx0_4, hx0_3, hx0_2, hx0_1],
    by rw [hx1_8, hx1_7, hx1_6, hx1_5, hx1_4, hx1_3, hx1_2, hx1_1],
    by rw [hfp8, hfp7, hfp6, hfp5, hfp4, hfp3, hfp2, hfp1],
    Entails.trans hP8 ?_⟩
  have h29920 : memRegion (s0.sp - 30080#64) 29920 =
      memRegion (s0.sp - 30080#64) 1248 ∗
        memRegion x9 4096 ∗ memRegion (x9 + 4096#64) 4096 ∗
        memRegion (x9 + 8192#64) 4096 ∗ memRegion (x9 + 12288#64) 4096 ∗
        memRegion (x9 + 16384#64) 4096 ∗ memRegion (x9 + 20480#64) 4096 ∗
        memRegion (x9 + 24576#64) 4096 := by
    rw [memRegion_split' (b' := x9) (n := 1248) (k := (28672 : Nat))
        rfl (by dsimp [x9]; bv_omega) (by decide),
      memRegion_split' (b' := x9 + 4096#64) (n := 4096) (k := (24576 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 8192#64) (n := 4096) (k := (20480 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 12288#64) (n := 4096) (k := (16384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 16384#64) (n := 4096) (k := (12288 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 20480#64) (n := 4096) (k := (8192 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b' := x9 + 24576#64) (n := 4096) (k := (4096 : Nat))
        rfl (by bv_omega) (by decide)]
  rw [h29920]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue

