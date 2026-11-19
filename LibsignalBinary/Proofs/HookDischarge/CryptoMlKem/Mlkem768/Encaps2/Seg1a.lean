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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import

/-!
# `encapsulate2` (`B20`) — Segment 1a (`+0x0000 .. +0x0188`)

Prologue (`SavedFrame20 s0.sp s0` at `[s0.sp - 128, s0.sp)`, `sp = s0.sp - 6128#64`, `x19 = ret`),
`.rodata.cst16.3` load, initial `m` staging, and copying `rHat[0]` (`+0x006c .. +0x00e8`) and
`rHat[1]` (`+0x00e8 .. +0x0188`), plus shared 128-bit load/store step macros.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData05Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  fetch_rebase_ldst128Lo12_site
  mlkemMpl
  resolve_ro05
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16_3_vec
  mlkemData05Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20
  UnspilledSaved20
  blk20_code_eq
  blk20_tree_size
  blkLib20
  blkPC20
  blkPl20
  blkPlaceable20
  blkTree20
  step_ldrQ128_ro
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8
  Oct8Mem
  Poly32Mem
  SepLoad128
  SepStore128
  Spill13
  Spill13Mem
  Vec128At
  Vec32
  step_ldpQ128
  step_ldrQ128
  step_stpQ128
  step_strQ128
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0000 → 0x0184]
gen_placed_odd_sites blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0000 → 0x0068]

@[simp, arm64_norm]
private theorem blkPC20_rebase_fetchOff_44 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC20.rebase b X).fetch (b + BitVec.ofNat 64 68) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 3)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl20.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib20) (prog := blkPC20) (pl := blkPl20)
    (b := b) (X := X) (off := 68)
    (r := { off := 68, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" })
    rfl blkPlaceable20 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 68)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 17) blk20_code_eq blk20_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl20_ρ [MlKemPlacement] (sym : String) :
    blkPl20.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC20

/-! ## 0. Shared Memory Elimination & 128-Bit Step Macros -/

theorem sepWP_elim_cell8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target s ((a ↦₆₄ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post :=
  SepWP.memRegion8_cell a h

theorem sepWP_elim_region32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 : BitVec 64,
      SepWP prog target s
        ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗ R0)
        post) :
    SepWP prog target s (memRegion a 32 ∗ R0) post := by
  have hsplit : memRegion a 32 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗
        memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 := by
    rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  sep_frame_apply (sepWP_elim_cell8 (a := a)); intro v0
  sep_frame_apply (sepWP_elim_cell8 (a := a + 8#64)); intro v1
  sep_frame_apply (sepWP_elim_cell8 (a := a + 16#64)); intro v2
  sep_frame_apply (sepWP_elim_cell8 (a := a + 24#64)); intro v3
  refine SepWP.weaken_pre ?_ (h v0 v1 v2 v3)
  sep_frame

theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

theorem spAligned_of_chk {s' : State} {sp : BitVec 64}
    (hsp' : s'.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) :
    s'.spAligned = true := by
  simp only [State.spAligned, hsp']
  exact hchk

theorem spAligned_of_sp_eq {s s' : State} {sp : BitVec 64}
    (hsp_al : s.spAligned = true) (hsp : s.sp = sp) (hsp' : s'.sp = sp) :
    s'.spAligned = true := by
  simp only [State.spAligned, hsp', ← hsp]
  exact hsp_al

theorem trans_unspilled {s0 s1 s2 : State}
    (h01 : UnspilledSaved20 s0 s1) (h12 : UnspilledSaved20 s1 s2) :
    UnspilledSaved20 s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1,
    h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩

syntax "seg1_load128_leaf " num : tactic
macro_rules
  | `(tactic| seg1_load128_leaf $k) => `(tactic| (
      apply SepLoad128.left
      first
      | (apply SepLoad128.vec32 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepLoad128.spill13 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepLoad128.oct8 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepLoad128.vec128At; bv_omega)))

syntax "seg1_load128 " num num : tactic
macro_rules
  | `(tactic| seg1_load128 0 $k) => `(tactic| seg1_load128_leaf $k)
  | `(tactic| seg1_load128 1 $k) => `(tactic| (apply SepLoad128.right; seg1_load128_leaf $k))
  | `(tactic| seg1_load128 2 $k) => `(tactic| (apply SepLoad128.right; apply SepLoad128.right; seg1_load128_leaf $k))
  | `(tactic| seg1_load128 3 $k) => `(tactic| (apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.right; seg1_load128_leaf $k))
  | `(tactic| seg1_load128 4 $k) => `(tactic| (apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.right; seg1_load128_leaf $k))

syntax "seg1_store128_leaf " num : tactic
macro_rules
  | `(tactic| seg1_store128_leaf $k) => `(tactic| (
      apply SepStore128.left
      first
      | (apply SepStore128.vec32 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepStore128.spill13 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepStore128.oct8 (k := $k); { decide }; { bv_omega }; { rfl })
      | (apply SepStore128.vec128At; bv_omega)))

syntax "seg1_store128 " num num : tactic
macro_rules
  | `(tactic| seg1_store128 0 $k) => `(tactic| seg1_store128_leaf $k)
  | `(tactic| seg1_store128 1 $k) => `(tactic| (apply SepStore128.right; seg1_store128_leaf $k))
  | `(tactic| seg1_store128 2 $k) => `(tactic| (apply SepStore128.right; apply SepStore128.right; seg1_store128_leaf $k))
  | `(tactic| seg1_store128 3 $k) => `(tactic| (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; seg1_store128_leaf $k))
  | `(tactic| seg1_store128 4 $k) => `(tactic| (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; seg1_store128_leaf $k))

macro "step_ldrQ " pos:num k:num : tactic => `(tactic| (
  apply step_ldrQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · seg1_load128 $pos $k
  · wp_norm_lhs))

macro "step_ldpQ " pos:num k1:num k2:num : tactic => `(tactic| (
  apply step_ldpQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · rfl
  · seg1_load128 $pos $k1
  · seg1_load128 $pos $k2
  · wp_norm_lhs))

macro "step_strQ " pos:num k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · seg1_store128 $pos $k
  · wp_norm_lhs
  intro _))

macro "step_stpQ " pos:num k1:num k2:num : tactic => `(tactic| (
  apply step_stpQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · seg1_store128 $pos $k1
  · seg1_store128 $pos $k2
  · wp_norm_lhs
  intro _))

/-! ## 1. Prologue & Early Sub-Segments (`+0x0000 → +0x0188`) -/

private theorem stackAt_prologue_split (sp0 : BitVec 64) :
    stackAt sp0 6128 =
      memRegion (sp0 - 4224#64) 8 ∗
      memRegion (sp0 - 6128#64) 8 ∗
      memRegion (sp0 - 128#64) 32 ∗
      memRegion (sp0 - 96#64) 32 ∗
      memRegion (sp0 - 64#64) 32 ∗
      memRegion (sp0 - 32#64) 32 ∗
      memRegion (sp0 - 6120#64) 1896 ∗
      memRegion (sp0 - 4216#64) 4088 := by
  unfold stackAt
  have h0 : memRegion (sp0 - BitVec.ofNat 64 6128) 6128 = memRegion (sp0 - 6128#64) 6128 := rfl
  rw [h0,
    memRegion_split' (b' := sp0 - 128#64) (n := 6000) (k := 128) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 6120#64) (n := 8) (k := (5992 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4224#64) (n := 1896) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 4216#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 96#64) (n := 32) (k := 96) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 64#64) (n := 32) (k := 64) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp0 - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem probes_restore_6000 (sp0 v0 v1 : BitVec 64) :
    ((sp0 - 6128#64) ↦₆₄ v0) ∗ memRegion (sp0 - 6120#64) 1896 ∗
      ((sp0 - 4224#64) ↦₆₄ v1) ∗ memRegion (sp0 - 4216#64) 4088 ⊢
      memRegion (sp0 - 6128#64) 6000 := by
  have hsplit : memRegion (sp0 - 6128#64) 6000 =
      memRegion (sp0 - 6128#64) 8 ∗ memRegion (sp0 - 6120#64) 1896 ∗
        memRegion (sp0 - 4224#64) 8 ∗ memRegion (sp0 - 4216#64) 4088 := by
    rw [memRegion_split' (b' := sp0 - 6120#64) (n := 8) (k := (5992 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4224#64) (n := 1896) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4216#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  exact entails_sub (pointsTo64_entails_memRegion (sp0 - 6128#64) v0) (by sep_frame)
    (entails_sub (pointsTo64_entails_memRegion (sp0 - 4224#64) v1) (by sep_frame) (by sep_frame))

theorem seg1_prologue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 : State) (ret esA ekA : BitVec 64) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx8 : s0.readReg64 .x8 = ret)
    (hx0 : s0.readReg64 .x0 = esA)
    (hx1 : s0.readReg64 .x1 = ekA) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x003c#64) s0
      (stackAt s0.sp 6128 ∗ F)
      (fun s1 P1 =>
        s1.sp = sp ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = esA ∧
        s1.readReg64 .x1 = ekA ∧
        s1.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.3") ∧
        s1.readReg64 .x19 = ret ∧
        UnspilledSaved20 s0 s1 ∧
        (P1 ⊢ SavedFrame20 s0.sp s0 ∗ memRegion sp 6000 ∗ F)) := by
  intro sp
  subst hbase
  rw [stackAt_prologue_split s0.sp]
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 4224#64)); intro p0
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 6128#64)); intro p1
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 128#64)); intro f0 f1 f2 f3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 96#64)); intro f4 f5 f6 f7
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro f8 f9 f10 f11
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro f12 f13 f14 f15
  have a1 : s0.sp - 128#64 + 8#64 = s0.sp - 120#64 := by bv_omega
  have a2 : s0.sp - 128#64 + 16#64 = s0.sp - 112#64 := by bv_omega
  have a3 : s0.sp - 128#64 + 24#64 = s0.sp - 104#64 := by bv_omega
  have a5 : s0.sp - 96#64 + 8#64 = s0.sp - 88#64 := by bv_omega
  have a6 : s0.sp - 96#64 + 16#64 = s0.sp - 80#64 := by bv_omega
  have a7 : s0.sp - 96#64 + 24#64 = s0.sp - 72#64 := by bv_omega
  have a9 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have a10 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have a11 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_omega
  have a13 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  have a14 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_omega
  have a15 : s0.sp - 32#64 + 24#64 = s0.sp - 8#64 := by bv_omega
  rw [a1, a2, a3, a5, a6, a7, a9, a10, a11, a13, a14, a15]
  have hsp128 : ((s0.sp - 128#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 128#64 hsp0 (by decide)
  have hsp4224 : ((s0.sp - 128#64 - 4096#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 128#64) 4096#64 hsp128 (by decide)
  have hsp6128 : ((s0.sp - 128#64 - 4096#64 - 1904#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 128#64 - 4096#64) 1904#64 hsp4224 (by decide)
  have hsp_eq : s0.sp - 128#64 - 4096#64 - 1904#64 = sp := by dsimp [sp]; bv_omega
  have hsp6128' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp_eq]; exact hsp6128
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [sp],
      spAligned_of_chk (by simp [sp]) hsp6128',
      by simp [hx0], by simp [hx1], by simp, by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  unfold SavedFrame20
  exact entails_sub (probes_restore_6000 s0.sp 0#64 0#64) (by sep_frame) (by sep_frame)

theorem seg1_setup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s : State) (sp esA ekA : BitVec 64) (r0 s5488 : Vec32) (m0 m1 : BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x003c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = esA)
    (hx1 : s.readReg64 .x1 = ekA)
    (hx9 : s.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.3")) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x006c#64) s
      (Vec128At (esA + 2048#64) m0 ∗
        Vec128At (esA + 2064#64) m1 ∗
        Poly32Mem esA r0 ∗
        Poly32Mem (sp + 5488#64) s5488 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = ekA ∧
        s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = sp + 5488#64 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = ekA + 384#64 ∧
        s'.readReg64 .x21 = sp + 3952#64 ∧
        s'.readReg64 .x22 = ekA + 384#64 ∧
        s'.readVReg128 0#5 = r0.v0 ∧
        s'.readVReg128 2#5 = r0.v1 ∧
        s'.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Vec128At (esA + 2048#64) m0 ∗
          Vec128At (esA + 2064#64) m1 ∗
          Poly32Mem esA r0 ∗
          Poly32Mem (sp + 5488#64) ((s5488.set 0 m0).set 1 m1) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldrQ 0 0
  step_ldrQ 1 0
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, hx9, pageOf_add_lo12Of])
    hro.cst16_3 mlkemData05Bytes_length cst16_3_vec (by wp_norm_lhs) ?_
  wp_step; wp_step; wp_step
  step_strQ 3 0
  step_ldpQ 2 0 1
  step_strQ 3 1
  wp_step; wp_step; wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp [hx0], by simp [hx1], by simp,
      by simp,
      by simp, by simp,
      by simp,
      by simp,
      by simp [Vec32.get], by simp [Vec32.get], by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      by sep_frame⟩

theorem seg1_copy_r0 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (r0 t0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x006c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA)
    (hq0 : s.readVReg128 0#5 = r0.v0)
    (hq2 : s.readVReg128 2#5 = r0.v1) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x00e8#64) s
      (Poly32Mem esA r0 ∗ Poly32Mem (sp + 208#64) t0 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Poly32Mem esA r0 ∗ Poly32Mem (sp + 208#64) r0 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_stpQ 1 0 1
  step_ldpQ 0 2 3; step_stpQ 1 2 3
  step_ldpQ 0 4 5; step_stpQ 1 4 5
  step_ldpQ 0 6 7; step_stpQ 1 6 7
  step_ldpQ 0 8 9; step_stpQ 1 8 9
  step_ldpQ 0 10 11; step_stpQ 1 10 11
  step_ldpQ 0 12 13; step_stpQ 1 12 13
  step_ldpQ 0 14 15; step_stpQ 1 14 15
  step_ldpQ 0 16 17; step_stpQ 1 16 17
  step_ldpQ 0 18 19; step_stpQ 1 18 19
  step_ldpQ 0 20 21; step_stpQ 1 20 21
  step_ldpQ 0 22 23; step_stpQ 1 22 23
  step_ldpQ 0 24 25; step_stpQ 1 24 25
  step_ldpQ 0 26 27; step_stpQ 1 26 27
  step_ldpQ 0 28 29; step_stpQ 1 28 29
  step_ldpQ 0 30 31; step_stpQ 1 30 31
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp [hx0], by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  simp only [Vec32.set, Vec32.get]
  exact Entails.refl _

theorem seg1_copy_r1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (r1 r2 t1 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x00e8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0188#64) s
      (Poly32Mem (esA + 512#64) r1 ∗ Poly32Mem (esA + 1024#64) r2 ∗
        Poly32Mem (sp + 720#64) t1 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 1#5 = r2.v2 ∧
        s'.readVReg128 2#5 = r2.v0 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Poly32Mem (esA + 512#64) r1 ∗ Poly32Mem (esA + 1024#64) r2 ∗
          Poly32Mem (sp + 720#64) r1 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldpQ 0 0 1; step_stpQ 2 0 1
  step_ldpQ 0 2 3; step_stpQ 2 2 3
  step_ldpQ 0 4 5; step_stpQ 2 4 5
  step_ldpQ 0 6 7; step_stpQ 2 6 7
  step_ldpQ 0 8 9; step_stpQ 2 8 9
  step_ldpQ 0 10 11; step_stpQ 2 10 11
  step_ldpQ 0 12 13; step_stpQ 2 12 13
  step_ldpQ 0 14 15; step_stpQ 2 14 15
  step_ldpQ 0 16 17; step_stpQ 2 16 17
  step_ldpQ 0 18 19; step_stpQ 2 18 19
  step_ldpQ 0 20 21; step_strQ 2 20
  step_ldpQ 0 22 23; step_strQ 2 21; step_strQ 2 22
  step_ldpQ 0 24 25; step_strQ 2 23; step_strQ 2 24
  step_ldpQ 0 26 27; step_strQ 2 25; step_strQ 2 26
  step_ldpQ 0 28 29; step_strQ 2 27; step_strQ 2 28
  step_ldpQ 0 30 31; step_strQ 2 29
  step_ldrQ 1 0; step_strQ 2 31
  step_ldrQ 1 2; step_strQ 2 30
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp [hx0], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [Vec32.get], by simp [Vec32.get], by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  simp only [Vec32.set, Vec32.get]
  exact Entails.refl _

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
