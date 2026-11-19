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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `kyber_encapsulate` (`B07`) — Segment 1a1 (`+0x0000 .. +0x00ac`)

1. `SpilledMsgWords` (`[sp + 16 .. sp + 144)`, `32 × 4` B) predicate for the 32 zero-extended
   bytes of `m = sha3_256List rand` spilled in `Seg1a` and reloaded in `Seg5a`.
2. Prologue (`+0x0000 → +0x0030`, spilling `SavedFrame07 s0.sp s0`), 8-iteration `4096`-byte
   stack-probe loop (`+0x0030 → +0x0040`), frame allocation (`sp = s0.sp - 33104#64`), and the
   first `B02` (`keccak2::<136, 6>`) call (`+0x0040 → +0x00ac`) computing `m = sha3_256List rand`
   while keeping `(rA ↦ₛ rand)` intact.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW
  keccak2_136_6_RW1Spec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  sha3_256
  sha3_256List
  sha3_512
  sha3_512List
  shake256
  shake256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6 (
  blk02_keccak2_136_6_RW1_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepStore128
  SepWP.of_memRegion_vecRangeMem
  Vec128At
  VecRangeMem
  step_strQ128
  vec128At_eq_pointsToBytes
  vecRangeMem_entails_memRegion
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub
  sepWP_elim_cell8
  sepWP_elim_region32
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07
  blk07_code_eq
  blk07_tree_size
  blkLib07
  blkPC07
  blkPl07
  blkPlaceable07
  blkTree07
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x0000 → 0x00a8]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

theorem blk02_rw1_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 2)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_6_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk02_keccak2_136_6_RW1_ok

@[simp] theorem sha3_256List_len (msg : List (BitVec 8)) : (sha3_256List msg).length = 32 :=
  (sha3_256 msg).2

@[simp] theorem sha3_512List_len (msg : List (BitVec 8)) : (sha3_512List msg).length = 64 :=
  (sha3_512 msg).2

@[simp] theorem shake256List_len (n : Nat) (msg : List (BitVec 8)) :
    (shake256List n msg).length = n :=
  (shake256 n msg).2

attribute [local irreducible] blkPC07 sha3_256List

/-! ## 1. Spilled Message Word Slots (`[sp + 16 .. sp + 144)`) -/

/-- Zero-extended 32-bit word for byte `j` of `m`. -/
@[expose] def msgW32 (m : List (BitVec 8)) (j : Nat) : BitVec 32 :=
  (m.getD j 0#8).zeroExtend 32

/-- Low 16 spilled message words (`[sp + 16 .. sp + 80)`). -/
@[expose] def SpilledMsgLo (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  ((sp + 16#64) ↦₃₂ msgW32 m 3) ∗ ((sp + 20#64) ↦₃₂ msgW32 m 0) ∗
  ((sp + 24#64) ↦₃₂ msgW32 m 1) ∗ ((sp + 28#64) ↦₃₂ msgW32 m 4) ∗
  ((sp + 32#64) ↦₃₂ msgW32 m 5) ∗ ((sp + 36#64) ↦₃₂ msgW32 m 7) ∗
  ((sp + 40#64) ↦₃₂ msgW32 m 6) ∗ ((sp + 44#64) ↦₃₂ msgW32 m 2) ∗
  ((sp + 48#64) ↦₃₂ msgW32 m 8) ∗ ((sp + 52#64) ↦₃₂ msgW32 m 9) ∗
  ((sp + 56#64) ↦₃₂ msgW32 m 11) ∗ ((sp + 60#64) ↦₃₂ msgW32 m 10) ∗
  ((sp + 64#64) ↦₃₂ msgW32 m 12) ∗ ((sp + 68#64) ↦₃₂ msgW32 m 13) ∗
  ((sp + 72#64) ↦₃₂ msgW32 m 14) ∗ ((sp + 76#64) ↦₃₂ msgW32 m 15)

/-- High 16 spilled message words (`[sp + 80 .. sp + 144)`). -/
@[expose] def SpilledMsgHi (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  ((sp + 80#64) ↦₃₂ msgW32 m 17) ∗ ((sp + 84#64) ↦₃₂ msgW32 m 16) ∗
  ((sp + 88#64) ↦₃₂ msgW32 m 18) ∗ ((sp + 92#64) ↦₃₂ msgW32 m 19) ∗
  ((sp + 96#64) ↦₃₂ msgW32 m 21) ∗ ((sp + 100#64) ↦₃₂ msgW32 m 20) ∗
  ((sp + 104#64) ↦₃₂ msgW32 m 22) ∗ ((sp + 108#64) ↦₃₂ msgW32 m 23) ∗
  ((sp + 112#64) ↦₃₂ msgW32 m 25) ∗ ((sp + 116#64) ↦₃₂ msgW32 m 24) ∗
  ((sp + 120#64) ↦₃₂ msgW32 m 26) ∗ ((sp + 124#64) ↦₃₂ msgW32 m 29) ∗
  ((sp + 128#64) ↦₃₂ msgW32 m 27) ∗ ((sp + 132#64) ↦₃₂ msgW32 m 30) ∗
  ((sp + 136#64) ↦₃₂ msgW32 m 28) ∗ ((sp + 140#64) ↦₃₂ msgW32 m 31)

/-- All 32 spilled message words (`[sp + 16 .. sp + 144)`). -/
@[expose] def SpilledMsgWords (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  SpilledMsgLo sp m ∗ SpilledMsgHi sp m

theorem pair32_entails_memRegion8 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) ⊢ memRegion a 8 := by
  rw [pointsTo32_pair a lo hi]
  exact cell_entails_memRegion8 a (hi ++ lo)

private theorem pairs8_entails_memRegion64 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗
      ((a + 8#64) ↦₃₂ w2) ∗ ((a + 12#64) ↦₃₂ w3) ∗
      ((a + 16#64) ↦₃₂ w4) ∗ ((a + 20#64) ↦₃₂ w5) ∗
      ((a + 24#64) ↦₃₂ w6) ∗ ((a + 28#64) ↦₃₂ w7) ∗
      ((a + 32#64) ↦₃₂ w8) ∗ ((a + 36#64) ↦₃₂ w9) ∗
      ((a + 40#64) ↦₃₂ w10) ∗ ((a + 44#64) ↦₃₂ w11) ∗
      ((a + 48#64) ↦₃₂ w12) ∗ ((a + 52#64) ↦₃₂ w13) ∗
      ((a + 56#64) ↦₃₂ w14) ∗ ((a + 60#64) ↦₃₂ w15)) ⊢ memRegion a 64 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 56) rfl rfl (by decide),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 40#64) (b' := a + 48#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 48#64) (b' := a + 56#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  have hp (off : BitVec 64) (lo hi : BitVec 32) :
      (((a + off) ↦₃₂ lo) ∗ ((a + (off + 4#64)) ↦₃₂ hi)) ⊢ memRegion (a + off) 8 := by
    simpa [show a + off + 4#64 = a + (off + 4#64) by bv_omega] using
      pair32_entails_memRegion8 (a + off) lo hi
  have p0 := pair32_entails_memRegion8 a w0 w1
  exact entails_sub p0 (by sep_frame)
    (entails_sub (hp 8#64 w2 w3) (by sep_frame)
    (entails_sub (hp 16#64 w4 w5) (by sep_frame)
    (entails_sub (hp 24#64 w6 w7) (by sep_frame)
    (entails_sub (hp 32#64 w8 w9) (by sep_frame)
    (entails_sub (hp 40#64 w10 w11) (by sep_frame)
    (entails_sub (hp 48#64 w12 w13) (by sep_frame)
    (entails_sub (hp 56#64 w14 w15) (by sep_frame) (by sep_frame))))))))

theorem spilledMsgLo_entails_memRegion64 (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledMsgLo sp m ⊢ memRegion (sp + 16#64) 64 := by
  simpa [SpilledMsgLo, BitVec.add_assoc] using
    pairs8_entails_memRegion64 (sp + 16#64)
      (msgW32 m 3) (msgW32 m 0) (msgW32 m 1) (msgW32 m 4)
      (msgW32 m 5) (msgW32 m 7) (msgW32 m 6) (msgW32 m 2)
      (msgW32 m 8) (msgW32 m 9) (msgW32 m 11) (msgW32 m 10)
      (msgW32 m 12) (msgW32 m 13) (msgW32 m 14) (msgW32 m 15)

theorem spilledMsgHi_entails_memRegion64 (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledMsgHi sp m ⊢ memRegion (sp + 80#64) 64 := by
  simpa [SpilledMsgHi, BitVec.add_assoc] using
    pairs8_entails_memRegion64 (sp + 80#64)
      (msgW32 m 17) (msgW32 m 16) (msgW32 m 18) (msgW32 m 19)
      (msgW32 m 21) (msgW32 m 20) (msgW32 m 22) (msgW32 m 23)
      (msgW32 m 25) (msgW32 m 24) (msgW32 m 26) (msgW32 m 29)
      (msgW32 m 27) (msgW32 m 30) (msgW32 m 28) (msgW32 m 31)

theorem spilledMsgWords_entails_memRegion128 (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledMsgWords sp m ⊢ memRegion (sp + 16#64) 128 := by
  rw [memRegion_split' (b := sp + 16#64) (b' := sp + 80#64) (n := 64) (k := 64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (spilledMsgLo_entails_memRegion64 sp m) (spilledMsgHi_entails_memRegion64 sp m)

/-! ## 2. Prologue (`+0x0000 → +0x0030`) & 8-Iteration Stack Probe (`+0x0030 → +0x0040`) -/

theorem stackAt_34240_split (sp0 : BitVec 64) :
    let sp := sp0 - 33104#64
    stackAt sp0 34240 =
      stackAt sp 1136 ∗ memRegion sp 176 ∗
      memRegion (sp0 - 32928#64) 32768 ∗ memRegion (sp0 - 160#64) 160 := by
  intro sp
  unfold stackAt
  have h0 : memRegion (sp0 - BitVec.ofNat 64 34240) 34240 = memRegion (sp0 - 34240#64) 34240 := rfl
  have h1 : memRegion (sp - BitVec.ofNat 64 1136) 1136 = memRegion (sp0 - 34240#64) 1136 :=
    congrArg (memRegion · 1136) (by dsimp only [sp]; bv_omega)
  rw [h0, h1,
    memRegion_split' (b := sp0 - 34240#64) (b' := sp) (n := (1136 : Nat)) (k := (33104 : Nat))
      rfl (by dsimp only [sp]; bv_omega) (by decide),
    memRegion_split' (b := sp) (b' := sp0 - 32928#64) (n := 176) (k := (32928 : Nat))
      rfl (by dsimp only [sp]; bv_omega) (by decide),
    memRegion_split' (b := sp0 - 32928#64) (b' := sp0 - 160#64) (n := (32768 : Nat)) (k := 160)
      rfl (by bv_omega) (by decide)]

theorem stackAt_1136_split_1040 (sp : BitVec 64) :
    stackAt sp 1136 = memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 := by
  unfold stackAt
  have h0 : memRegion (sp - BitVec.ofNat 64 1136) 1136 = memRegion (sp - 1136#64) 1136 := rfl
  have h1 : memRegion (sp - BitVec.ofNat 64 1040) 1040 = memRegion (sp - 1040#64) 1040 := rfl
  rw [h0, h1,
    memRegion_split' (b := sp - 1136#64) (b' := sp - 1040#64) (n := 96) (k := (1040 : Nat))
      rfl (by bv_omega) (by decide)]

theorem stackAt_1136_split_720 (sp : BitVec 64) :
    stackAt sp 1136 = memRegion (sp - 1136#64) 416 ∗ stackAt sp 720 := by
  unfold stackAt
  have h0 : memRegion (sp - BitVec.ofNat 64 1136) 1136 = memRegion (sp - 1136#64) 1136 := rfl
  have h1 : memRegion (sp - BitVec.ofNat 64 720) 720 = memRegion (sp - 720#64) 720 := rfl
  rw [h0, h1,
    memRegion_split' (b := sp - 1136#64) (b' := sp - 720#64) (n := 416) (k := 720)
      rfl (by bv_omega) (by decide)]

theorem seg1a_prologue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 : State) (ret pkA rA : BitVec 64) (Rest : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = pkA) (hx2 : s0.readReg64 .x2 = rA) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0030#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = s0.sp - 160#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = ret ∧
        s1.readReg64 .x1 = pkA ∧
        s1.readReg64 .x2 = rA ∧
        s1.readReg64 .x9 = s0.sp - 32928#64 ∧
        s1.readReg64 .fp = s0.sp - 96#64 ∧
        (P1 ⊢ SavedFrame07 s0.sp s0 ∗ Rest)) := by
  subst hbase
  have hsplit : memRegion (s0.sp - 160#64) 160 =
      memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 32 ∗
      memRegion (s0.sp - 96#64) 32 ∗ memRegion (s0.sp - 64#64) 32 ∗
      memRegion (s0.sp - 32#64) 32 := by
    rw [memRegion_split' (b' := s0.sp - 128#64) (n := 32) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := s0.sp - 128#64) (b' := s0.sp - 96#64) (n := 32) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b := s0.sp - 96#64) (b' := s0.sp - 64#64) (n := 32) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := s0.sp - 64#64) (b' := s0.sp - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 160#64)); intro c0 c1 c2 c3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 128#64)); intro c4 c5 c6 c7
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 96#64)); intro c8 c9 c10 c11
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro c12 c13 c14 c15
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro c16 c17 c18 c19
  have hsp160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hsp160,
      by simp [hx0], by simp [hx1], by simp [hx2], by simp, by simp, ?_⟩
  unfold SavedFrame07
  sep_frame

theorem stackProbe8_ok [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (base : BitVec 64) (Rest : SepProp) :
    ∀ (rem : Nat), 1 ≤ rem → rem ≤ 8 → ∀ (s : State),
      s.pc = b + 0x0030#64 →
      s.status = .Running →
      s.sp = base + BitVec.ofNat 64 (4096 * rem) →
      s.spAligned = true →
      s.readReg64 .x9 = base →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0040#64) s
        (memRegion base (4096 * rem) ∗ Rest)
        (fun s' P' =>
          s'.sp = base ∧
          s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧
          s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x2 = s.readReg64 .x2 ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          (P' ⊢ memRegion base (4096 * rem) ∗ Rest)) := by
  subst hbase
  intro rem
  induction rem generalizing Rest with
  | zero => intro h1; omega
  | succ rem' ih =>
    intro _ hle s hpc hrun hsp hspA hx9
    let sp' := base + BitVec.ofNat 64 (4096 * rem')
    have hmul : BitVec.ofNat 64 (4096 * (rem' + 1)) = BitVec.ofNat 64 (4096 * rem') + 4096#64 := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mul_succ]
    have hsp_eq : s.sp = sp' + 4096#64 := by
      dsimp only [sp']; rw [hsp, hmul]; bv_omega
    have hsp' : s.sp - 4096#64 = sp' := by
      rw [hsp_eq]; bv_omega
    have hchk : (sp' &&& 15#64 == 0#64) = true := by
      rw [← hsp']
      exact spAligned_sub s.sp 4096#64 (by simpa [State.spAligned] using hspA) (by decide)
    clear hsp hmul
    have hreg_split : memRegion base (4096 * (rem' + 1)) =
        memRegion base (4096 * rem') ∗ memRegion sp' 8 ∗ memRegion (sp' + 8#64) 4088 := by
      rw [memRegion_split' (b := base) (b' := sp') (n := 4096 * rem') (k := (4096 : Nat))
          (by omega) rfl (by omega),
        memRegion_split' (b := sp') (b' := sp' + 8#64) (n := 8) (k := (4088 : Nat))
          rfl rfl (by decide)]
    rw [hreg_split]
    sep_frame_apply (sepWP_elim_cell8 (a := sp')); intro p0
    wp_steps 4
    wp_if hne
    · rcases rem' with _ | rem''
      · have hbase0 : sp' = base := by dsimp only [sp']; simp
        simp [hbase0] at hne
      · refine SepWP.weaken_pre
          (show _ ⊢ memRegion base (4096 * (rem'' + 1)) ∗ (memRegion sp' 4096 ∗ Rest) by
            exact entails_sub (cell_entails_memRegion8 sp' 0#64) (by sep_frame) (by sep_frame)) ?_
        refine SepWP.mono
          (ih (memRegion sp' 4096 ∗ Rest) (by omega) (by omega) _
            (by wp_norm_lhs) (by simp [hrun])
            (by simp; rfl) (spAligned_of_chk (by simp) hchk) (by simp [hx9])) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx0_f, hx1_f, hx2_f, hfp_f, hPf⟩
        refine ⟨hsp_f, hspA_f, by simpa using hx0_f, by simpa using hx1_f,
          by simpa using hx2_f, by simpa using hfp_f, ?_⟩
        refine Entails.trans hPf ?_
        rw [memRegion_split' (b := sp') (b' := sp' + 8#64) (n := 8) (k := (4088 : Nat))
            rfl rfl (by decide)]
        sep_frame
    · have hrem0 : rem' = 0 := by
        have hbv : sp' = base := by simpa using hne
        have hd : BitVec.ofNat 64 (4096 * rem') = 0#64 := by
          dsimp only [sp'] at hbv; bv_omega
        have hnat := congrArg BitVec.toNat hd
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
        simpa using hnat
      subst hrem0
      have hbase0 : sp' = base := by dsimp only [sp']; simp
      refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
        ⟨by simpa using hbase0, spAligned_of_chk rfl hchk,
          by simp, by simp, by simp, by simp, ?_⟩
      dsimp only [sp']
      exact entails_sub (cell_entails_memRegion8 (base + BitVec.ofNat 64 (4096 * 0)) 0#64)
        (by sep_frame) (by sep_frame)

/-! ## 3. Frame Setup & `m = sha3_256List rand` (`+0x0040 → +0x00ac`) -/

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

theorem seg1a_setup_hash_rand [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp fpVal ret pkA rA : BitVec 64) (rand : List (BitVec 8)) (Rest : SepProp)
    (hrnd : rand.length = 32)
    (hpc : s.pc = b + 0x0040#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp + 176#64) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = ret) (hx1 : s.readReg64 .x1 = pkA)
    (hx2 : s.readReg64 .x2 = rA) (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x00ac#64) s
      ((rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
        memRegion (sp + 8#64) 8 ∗ memRegion (sp + 216#64) 8 ∗
        memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
        memRegion (sp + 28848#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.readReg64 .x19 = pkA + 384#64 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = pkA + 384#64 ∧
        sf.readReg64 .x22 = sp + 26768#64 ∧
        sf.readReg64 .x23 = sp + 2560#64 ∧
        sf.readReg64 .x24 = sp + 27032#64 ∧
        sf.readReg64 .fp = fpVal ∧
        (Pf ⊢ (rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
          ((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
          memRegion (sp + 2560#64) 32 ∗
          Keccak2SlicesRW (sp + 12832#64) rA rA 32 32 ∗
          ((sp + 28848#64) ↦ₛ sha3_256List rand) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 168#64) s
      ((rA ↦ₛ rand) ∗ stackAt sp 1136 ∗
        memRegion (sp + 8#64) 8 ∗ memRegion (sp + 216#64) 8 ∗
        memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
        memRegion (sp + 28848#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 12832#64 ∧
        sm.readReg64 .x1 = sp + 28848#64 ∧
        sm.readReg64 .x2 = sp + 2560#64 ∧
        sm.readReg64 .x19 = pkA + 384#64 ∧
        sm.readReg64 .x20 = pkA ∧
        sm.readReg64 .x21 = pkA + 384#64 ∧
        sm.readReg64 .x22 = sp + 26768#64 ∧
        sm.readReg64 .x23 = sp + 2560#64 ∧
        sm.readReg64 .x24 = sp + 27032#64 ∧
        sm.readReg64 .fp = fpVal ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 12832#64) rA rA rand.length rand.length ∗
          (rA ↦ₛ rand) ∗ memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 2560#64) 32 ∗
          stackAt sp 1040 ∗
          (((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 216#64) ↦₆₄ (sp + 29112#64)) ∗
            memRegion (sp - 1136#64) 96 ∗ Rest))) := by
    rw [stackAt_1136_split_1040 sp]
    sep_frame_apply (sepWP_elim_cell8 (a := sp + 8#64)); intro c8
    sep_frame_apply (sepWP_elim_cell8 (a := sp + 216#64)); intro c216
    sep_frame_apply (sepWP_elim_region32 (a := sp + 12832#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 28848#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f28 => ?_
    dsimp only [VecRangeMem]
    simp only [sepConj_emp]
    have ha28_16 : sp + 28848#64 + 16#64 = sp + 28864#64 := by bv_omega
    wp_steps 22
    refine step_strQ128 (wb := none) (ea := sp + 28864#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha28_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 28848#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    have hz28 : Vec128At (sp + 28848#64) 0#128 ∗ Vec128At (sp + 28848#64 + 16#64) 0#128 ⊢
        memRegion (sp + 28848#64) 32 := by
      simpa [VecRangeMem, sepConj_emp] using
        vecRangeMem_entails_memRegion 2 (sp + 28848#64) (fun _ => 0#128)
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, spAligned_of_chk (by simp) hsp_chk,
        by simp, by simp, by simp,
        by simp, by simp, by simp,
        by simp, by simp, by simp,
        by simp [hfp], ?_⟩
    unfold Keccak2SlicesRW
    rw [hrnd]
    have ha1 : sp + 12832#64 + 8#64 = sp + 12840#64 := by bv_omega
    have ha2 : sp + 12832#64 + 16#64 = sp + 12848#64 := by bv_omega
    have ha3 : sp + 12832#64 + 24#64 = sp + 12856#64 := by bv_omega
    simp only [ha1, ha2, ha3]
    exact entails_sub hz28 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpc_m hrun_m hcl_m hro_m
    ⟨hsp_m, hspA_m, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hfp_m, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : rand.length < 2 ^ 32 := by rw [hrnd]; decide
  wp_call (blk02_rw1_07 blkPl07.base) (sp + 12832#64, rA, sp + 28848#64, sp + 2560#64, rand)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hm_len : (sha3_256List rand).length = 32 := sha3_256List_len rand
  have hout1 : ((sp + 2560#64) ↦ₛ sha3_256List rand) ⊢ memRegion (sp + 2560#64) 32 := by
    rw [← hm_len]; exact pointsToBytes_entails_memRegion _ _
  rw [hsp_m, hrnd, stackAt_1136_split_1040 sp]
  exact entails_sub hout1 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
