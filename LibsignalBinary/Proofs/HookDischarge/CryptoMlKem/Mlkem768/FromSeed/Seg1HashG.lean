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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Zero

/-!
# `generate_keypair_compressed` (`B05`) — Segment 1c `SHA3-512` & Constant Staging (`+0x01a8 .. +0x02b8`)

Covers:
1. `B00` (`keccak2::<72, 6>`) `SHA3-512(seed.take 32 ++ [3#8])` call (`+0x01a8 .. +0x0214`).
2. Staging `rho`, `sigma`, 2-lane duplicated `rho` vectors, pointer spill slots, and `.rodata`
   constants (`cst16.0`, `cst16.1`, `cst16.2`, `KECCAK_RC`) before jumping to `+0x02b8`
   (`+0x0214 .. +0x02b8`).
3. End-to-end prologue theorem `seg1_prologue_ok` (`b → b + 0x02b8#64`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  fetch_rebase_ldst128Lo12_site
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk00
  resolve_ro01
  resolve_ro02
  resolve_ro03
  resolve_ro04
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16_0_vec
  cst16_1_vec
  cst16_2_vec
  mlkemData02Bytes_length
  mlkemData03Bytes_length
  mlkemData04Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakSponge
  packLane64
  sha3_512List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6 (
  blk00_keccak2_72_6_RW1_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion32_cells
  readLE_8_eq_packLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128
  SepStore128
  Vec128At
  VecRangeMem
  bytesToVecNat
  pointsToBytes_eq_vecRangeMem
  step_ldpQ128
  step_ldrQ128
  step_stpQ128
  step_strQ128
  vecRangeMem_entails_memRegion
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  B05LateSlots
  Seg2ConstSlots
  entails_sub
  seg1_spill_and_probe
  sepWP_elim_bytes
  sepWP_elim_cell8
  sepWP_elim_vec128
  vec128At_entails_memRegion16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Zero (seg1_zero_setup)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x01a8 → 0x02a4]
gen_placed_odd_sites blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x0258 → 0x0288]

@[simp, arm64_norm]
private theorem blkPC05_rebase_fetchOff_284 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC05.rebase b X).fetch (b + BitVec.ofNat 64 644) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl05.ρ "libcrux_ml_kem:.rodata.cst16.0")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib05) (prog := blkPC05) (pl := blkPl05)
    (b := b) (X := X) (off := 644)
    (r := { off := 644, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" })
    rfl blkPlaceable05 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 644)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 161) blk05_code_eq blk05_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC05_rebase_fetchOff_294 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC05.rebase b X).fetch (b + BitVec.ofNat 64 660) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl05.ρ "libcrux_ml_kem:.rodata.cst16.1")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib05) (prog := blkPC05) (pl := blkPl05)
    (b := b) (X := X) (off := 660)
    (r := { off := 660, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" })
    rfl blkPlaceable05 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 660)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 165) blk05_code_eq blk05_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC05_rebase_fetchOff_29c [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC05.rebase b X).fetch (b + BitVec.ofNat 64 668) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 0)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl05.ρ "libcrux_ml_kem:.rodata.cst16.2")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib05) (prog := blkPC05) (pl := blkPl05)
    (b := b) (X := X) (off := 668)
    (r := { off := 668, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" })
    rfl blkPlaceable05 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 668)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 167) blk05_code_eq blk05_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

attribute [local irreducible] blkLib05

private theorem sha3_512List_length (msg : List (BitVec 8)) :
    (sha3_512List msg).length = 64 := by
  simp [sha3_512List, keccakSponge]

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

/-- Register invariant entering `Seg2` (`SampleNTT` matrix loop) at `b + 0x02b8#64`. -/
@[expose] def Seg1Post [MlKemPlacement] (s0 s : State) : Prop :=
  let sp := s0.sp - 30080#64
  s.sp = sp ∧
  s.spAligned = true ∧
  s.readReg64 .fp = s0.sp - 96#64 ∧
  s.readReg64 .x1 = 0#64 ∧
  s.readReg64 .x19 = sp + 17376#64 ∧
  s.readReg64 .x20 = sp + 27851#64 ∧
  s.readReg64 .x21 = sp + 29024#64 ∧
  s.readReg64 .x23 = 256#64 ∧
  s.readReg64 .x24 =
    mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ∧
  s.readReg64 .x26 = sp + 27840#64 ∧
  s.readReg64 .x27 = 544#64 ∧
  s.readReg64 .x28 = sp + 28104#64

/-- Spatial assertion entering `Seg2` at `b + 0x02b8#64`. -/
@[expose] def Seg1Spatial (s0 : State) (seedA outPtr : BitVec 64)
    (seed : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  SavedFrame05 s0.sp s0 ∗
    stackAt sp 1136 ∗
    (seedA ↦ₛ seed) ∗
    B05LateSlots sp seedA outPtr (g.take 32) (g.drop 32) ∗
    Seg2ConstSlots sp (g.take 32) ∗
    memRegion (sp + 144#64) 208 ∗
    memRegion (sp + 432#64) 3312 ∗
    memRegion (sp + 3744#64) 4608 ∗
    memRegion (sp + 8352#64) 21056 ∗
    F

/-! ## 1. Helpers & Sub-Segment 1c-1: `G(d || [3])` Input Prep & `B00` Call (`+0x01a8 → +0x0214`) -/

private theorem spAligned_of_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) :
    s.spAligned = true := by
  simpa [State.spAligned, hsp] using hchk

private theorem aligned16_add_of_dvd (sp : BitVec 64) (n : Nat)
    (hsp : (sp &&& 15#64 == 0#64) = true) (hdvd : 16 ∣ n) :
    ((sp + BitVec.ofNat 64 n) &&& 15#64 == 0#64) = true := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [BitVec.ofNat_mul]
  generalize BitVec.ofNat 64 k = q
  revert hsp
  bv_bits

private theorem orr_11_of_aligned16 (x : BitVec 64) (hx : (x &&& 15#64 == 0#64) = true) :
    (x ||| 11#64) = x + 11#64 := by
  have hx0 : x &&& 15#64 = 0#64 := of_decide_eq_true hx
  have h15 : (15#64 &&& 11#64 : BitVec 64) = 11#64 := by decide
  have hdisj : x &&& 11#64 = 0#64 := by
    rw [← h15, ← BitVec.and_assoc, hx0]
    decide
  exact (BitVec.add_eq_or_of_and_eq_zero x 11#64 hdisj).symm

private theorem cells32_entails_memRegion (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      memRegion a 32 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by omega)]
  exact entails_sub (cell_entails_memRegion8 a v0) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (a + 8#64) v1) (by sep_frame)
      (entails_sub (cell_entails_memRegion8 (a + 16#64) v2) (by sep_frame)
        (entails_sub (cell_entails_memRegion8 (a + 24#64) v3) (by sep_frame) (by sep_frame))))

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

private theorem stackAt_1136_split_720 (sp : BitVec 64) :
    stackAt sp 1136 = stackAt sp 720 ∗ memRegion (sp - 1136#64) 416 := by
  unfold stackAt
  have hb : sp - BitVec.ofNat 64 1136 = sp - 1136#64 := rfl
  have hb' : sp - BitVec.ofNat 64 720 = sp - 720#64 := rfl
  rw [hb, hb', memRegion_split' (b := sp - 1136#64) (b' := sp - 720#64) (n := 416) (k := 720)
    rfl (by bv_omega) (by omega)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem seg1_hash_prep [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal seedA : BitVec 64) (seed : List (BitVec 8)) (s4 : State) (Rest : SepProp)
    (hseed : seed.length = 64)
    (hpc : s4.pc = b + 0x01a8#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp) (hsp_al : s4.spAligned = true)
    (hfp : s4.readReg64 .fp = fpVal)
    (hx19 : s4.readReg64 .x19 = sp + 17376#64)
    (hx20 : s4.readReg64 .x20 = seedA)
    (hx22 : s4.readReg64 .x22 = sp + 2208#64)
    (hx23 : s4.readReg64 .x23 = sp + 27840#64)
    (hx24 : s4.readReg64 .x24 = sp + 9984#64)
    (hx26 : s4.readReg64 .x26 = sp + 27840#64)
    (hx28 : s4.readReg64 .x28 = sp + 28104#64) :
    let msg := seed.take 32 ++ [3#8]
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0210#64) s4
      ((seedA ↦ₛ seed) ∗
        memRegion (sp + 32#64) 8 ∗
        memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 10016#64) 32 ∗
        memRegion (sp + 27840#64) 32 ∗ memRegion (sp + 27872#64) 1 ∗
        memRegion (sp + 29024#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = fpVal ∧
        sm.readReg64 .x0 = sp + 29024#64 ∧
        sm.readReg64 .x1 = sp + 9984#64 ∧
        sm.readReg64 .x2 = sp + 17376#64 ∧
        sm.readReg64 .x19 = sp + 17376#64 ∧
        sm.readReg64 .x20 = sp + 17376#64 ∧
        sm.readReg64 .x21 = sp + 29024#64 ∧
        sm.readReg64 .x22 = sp + 2208#64 ∧
        sm.readReg64 .x23 = sp + 27840#64 ∧
        sm.readReg64 .x24 = sp + 9984#64 ∧
        sm.readReg64 .x26 = sp + 27840#64 ∧
        sm.readReg64 .x28 = sp + 28104#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 29024#64) (sp + 27840#64) (sp + 27840#64)
            msg.length msg.length ∗
          ((sp + 27840#64) ↦ₛ msg) ∗
          memRegion (sp + 9984#64) 64 ∗
          ((sp + 32#64) ↦₆₄ seedA) ∗
          (seedA ↦ₛ seed) ∗ Rest)) := by
  intro msg
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have htake_len : (seed.take 32).length = 32 := by simp [hseed]
  have hmsg_len : msg.length = 33 := by simp [msg, hseed]
  have hseed_split : (seedA ↦ₛ seed) =
      (seedA ↦ₛ seed.take 32) ∗ ((seedA + 32#64) ↦ₛ seed.drop 32) := by
    conv_lhs => rw [← List.take_append_drop 32 seed]
    rw [pointsToBytes_append, htake_len]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 32#64)); intro c32
  apply memRegion32_cells (sp + 9984#64); intro z0 z1 z2 z3
  apply memRegion32_cells (sp + 10016#64); intro z4 z5 z6 z7
  apply memRegion32_cells (sp + 27840#64); intro d0 d1 d2 d3
  sep_frame_apply (sepWP_elim_bytes (a := sp + 27872#64) 1); intro b32 hb32
  rcases List.length_eq_one_iff.mp hb32 with ⟨b0, rfl⟩
  apply memRegion32_cells (sp + 29024#64); intro k0 k1 k2 k3
  rw [hseed_split, ← vec2_cells_eq_bytes seedA htake_len,
    show sp + 27872#64 = (sp + 27840#64) + 32#64 by bv_omega]
  simp only [show sp + 29024#64 + 8#64 = sp + 29032#64 by bv_omega,
    show sp + 29024#64 + 16#64 = sp + 29040#64 by bv_omega,
    show sp + 29024#64 + 24#64 = sp + 29048#64 by bv_omega]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hal_sp,
      by simp [hfp],
      by simp,
      by simp,
      by simp,
      by simp [hx19],
      by simp,
      by simp,
      by simp [hx22], by simp [hx23], by simp [hx24],
      by simp [hx26], by simp [hx28], ?_⟩
  have htrunc (v : BitVec 128) : v.setWidth 64 = v.extractLsb' 0 64 := by bv_bits
  have hw1 : ByteSlice.write8 [b0] 0 3#8 = [3#8] := rfl
  simp only [htrunc, hw1]
  have hz64 :
      ((sp + 9984#64) ↦₆₄ 0#64) ∗ ((sp + 9992#64) ↦₆₄ 0#64) ∗
        ((sp + 10000#64) ↦₆₄ 0#64) ∗ ((sp + 10008#64) ↦₆₄ 0#64) ∗
        ((sp + 10016#64) ↦₆₄ 0#64) ∗ ((sp + 10024#64) ↦₆₄ 0#64) ∗
        ((sp + 10032#64) ↦₆₄ 0#64) ∗ ((sp + 10040#64) ↦₆₄ 0#64) ⊢
      memRegion (sp + 9984#64) 64 := by
    rw [memRegion_split' (b' := sp + 10016#64) (n := 32) (k := 32) rfl (by bv_omega) (by omega)]
    have hz1 := cells32_entails_memRegion (sp + 9984#64) 0#64 0#64 0#64 0#64
    have hz2 := cells32_entails_memRegion (sp + 10016#64) 0#64 0#64 0#64 0#64
    simp only [show sp + 9984#64 + 8#64 = sp + 9992#64 by bv_omega,
      show sp + 9984#64 + 16#64 = sp + 10000#64 by bv_omega,
      show sp + 9984#64 + 24#64 = sp + 10008#64 by bv_omega] at hz1
    simp only [show sp + 10016#64 + 8#64 = sp + 10024#64 by bv_omega,
      show sp + 10016#64 + 16#64 = sp + 10032#64 by bv_omega,
      show sp + 10016#64 + 24#64 = sp + 10040#64 by bv_omega] at hz2
    exact entails_sub hz1 (by sep_frame) (entails_sub hz2 (by sep_frame) (by sep_frame))
  have hmsg_pts :
      ((sp + 27840#64) ↦₆₄ (bytesToVecNat (seed.take 32) 0).extractLsb' 0 64) ∗
        ((sp + 27848#64) ↦₆₄ (bytesToVecNat (seed.take 32) 0).extractLsb' 64 64) ∗
        ((sp + 27856#64) ↦₆₄ (bytesToVecNat (seed.take 32) 1).extractLsb' 0 64) ∗
        ((sp + 27864#64) ↦₆₄ (bytesToVecNat (seed.take 32) 1).extractLsb' 64 64) ∗
        (((sp + 27840#64) + 32#64) ↦ₛ [3#8]) =
      ((sp + 27840#64) ↦ₛ msg) := by
    dsimp only [msg]
    rw [pointsToBytes_append, htake_len,
      show sp + 27840#64 + BitVec.ofNat 64 32 = (sp + 27840#64) + 32#64 from rfl,
      ← vec2_cells_eq_bytes (sp + 27840#64) htake_len]
    simp only [show sp + 27840#64 + 8#64 = sp + 27848#64 by bv_omega,
      show sp + 27840#64 + 16#64 = sp + 27856#64 by bv_omega,
      show sp + 27840#64 + 24#64 = sp + 27864#64 by bv_omega]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  have hsl :
      Keccak2SlicesRW (sp + 29024#64) (sp + 27840#64) (sp + 27840#64) msg.length msg.length =
        ((sp + 29024#64) ↦₆₄ (sp + 27840#64)) ∗ ((sp + 29032#64) ↦₆₄ 33#64) ∗
        ((sp + 29040#64) ↦₆₄ (sp + 27840#64)) ∗ ((sp + 29048#64) ↦₆₄ 33#64) := by
    unfold Keccak2SlicesRW
    simp only [hmsg_len,
      show sp + 29024#64 + 8#64 = sp + 29032#64 by bv_omega,
      show sp + 29024#64 + 16#64 = sp + 29040#64 by bv_omega,
      show sp + 29024#64 + 24#64 = sp + 29048#64 by bv_omega]
  conv_rhs => rw [← hmsg_pts, hsl]
  exact entails_sub hz64 (by sep_frame) (by sep_frame)

private theorem seg1_b00_call [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (msg : List (BitVec 8)) (sm : State) (Rest : SepProp)
    (hmsg_len : msg.length = 33)
    (hpc : sm.pc = b + 0x0210#64) (hrun : sm.status = .Running)
    (hsp : sm.sp = sp) (hsp_al : sm.spAligned = true)
    (hfp : sm.readReg64 .fp = fpVal)
    (hx0 : sm.readReg64 .x0 = sp + 29024#64)
    (hx1 : sm.readReg64 .x1 = sp + 9984#64)
    (hx2 : sm.readReg64 .x2 = sp + 17376#64)
    (hx19 : sm.readReg64 .x19 = sp + 17376#64)
    (hx20 : sm.readReg64 .x20 = sp + 17376#64)
    (hx21 : sm.readReg64 .x21 = sp + 29024#64)
    (hx22 : sm.readReg64 .x22 = sp + 2208#64)
    (hx23 : sm.readReg64 .x23 = sp + 27840#64)
    (hx24 : sm.readReg64 .x24 = sp + 9984#64)
    (hx26 : sm.readReg64 .x26 = sp + 27840#64)
    (hx28 : sm.readReg64 .x28 = sp + 28104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem)
    (hro : MlKemRoOk mlkemMpl sm.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0214#64) sm
      (Keccak2SlicesRW (sp + 29024#64) (sp + 27840#64) (sp + 27840#64)
          msg.length msg.length ∗
        ((sp + 27840#64) ↦ₛ msg) ∗
        memRegion (sp + 9984#64) 64 ∗
        memRegion (sp + 17376#64) 64 ∗
        stackAt sp 1136 ∗ Rest)
      (fun sk Pk =>
        sk.sp = sp ∧ sk.spAligned = true ∧
        sk.readReg64 .fp = fpVal ∧
        sk.readReg64 .x19 = sp + 17376#64 ∧
        sk.readReg64 .x20 = sp + 17376#64 ∧
        sk.readReg64 .x21 = sp + 29024#64 ∧
        sk.readReg64 .x22 = sp + 2208#64 ∧
        sk.readReg64 .x23 = sp + 27840#64 ∧
        sk.readReg64 .x24 = sp + 9984#64 ∧
        sk.readReg64 .x26 = sp + 27840#64 ∧
        sk.readReg64 .x28 = sp + 28104#64 ∧
        (Pk ⊢ ((sp + 9984#64) ↦ₛ sha3_512List msg) ∗
          memRegion (sp + 17376#64) 64 ∗
          memRegion (sp + 27840#64) 33 ∗
          memRegion (sp + 29024#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have hmsg_lt : msg.length < 72 := by omega
  rw [stackAt_1136_split_720 sp]
  wp_cut_codeLoaded; wp_step
  have hro' : MlKemRoOk mlkemMpl
      ((sm.writeReg64 .lr (blkPl05.base + 532#64)).setPC (mlkemMpl.base 0)).mem := hro
  wp_mlkem_call blk00_keccak2_72_6_RW1_ok
    (sp + 29024#64, sp + 27840#64, sp + 9984#64, sp + 17376#64, msg)
  have hsp_fin : sf.sp = sp := hsp_sf.trans hsp
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_fin, spAligned_of_chk hsp_fin hal_sp,
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hsl : Keccak2SlicesRW (sp + 29024#64) (sp + 27840#64) (sp + 27840#64)
      msg.length msg.length ⊢ memRegion (sp + 29024#64) 32 := by
    unfold Keccak2SlicesRW
    exact cells32_entails_memRegion (sp + 29024#64) _ _ _ _
  have hm_ent : ((sp + 27840#64) ↦ₛ msg) ⊢ memRegion (sp + 27840#64) 33 := by
    simpa [hmsg_len] using pointsToBytes_entails_memRegion (sp + 27840#64) msg
  have ho1 : ((sp + 17376#64) ↦ₛ sha3_512List msg) ⊢ memRegion (sp + 17376#64) 64 := by
    simpa [sha3_512List_length] using
      pointsToBytes_entails_memRegion (sp + 17376#64) (sha3_512List msg)
  exact entails_sub hsl (by sep_frame)
    (entails_sub hm_ent (by sep_frame)
      (entails_sub ho1 (by sep_frame) (by sep_frame)))

/-! ## 2. Sub-Segment 1c-2: Constant Staging (`+0x0214 → +0x02b8`) & `seg1_prologue_ok` -/

@[simp] private theorem extractLsb64_lo_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[simp] private theorem extractLsb64_hi_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

@[simp] private theorem truncate64_append (hi lo : BitVec 64) :
    (hi ++ lo).truncate 64 = lo := by bv_bits

private theorem seg1_consts_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (sk : State) (g : List (BitVec 8)) (Rest : SepProp)
    (hg : g.length = 64)
    (hpc : sk.pc = b + 0x0214#64) (hrun : sk.status = .Running)
    (hsp : sk.sp = sp) (hsp_al : sk.spAligned = true)
    (hfp : sk.readReg64 .fp = fpVal)
    (hx19 : sk.readReg64 .x19 = sp + 17376#64)
    (hx20 : sk.readReg64 .x20 = sp + 17376#64)
    (hx21 : sk.readReg64 .x21 = sp + 29024#64)
    (hx22 : sk.readReg64 .x22 = sp + 2208#64)
    (hx23 : sk.readReg64 .x23 = sp + 27840#64)
    (hx24 : sk.readReg64 .x24 = sp + 9984#64)
    (hx26 : sk.readReg64 .x26 = sp + 27840#64)
    (hx28 : sk.readReg64 .x28 = sp + 28104#64) :
    let rho := g.take 32
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0258#64) sk
      (((sp + 9984#64) ↦ₛ g) ∗
        memRegion (sp + 48#64) 16 ∗
        memRegion (sp + 29408#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = fpVal ∧
        sm.readReg64 .x1 = 0#64 ∧
        sm.readReg64 .x9 = sp + 9995#64 ∧
        sm.readReg64 .x10 = sp + 11288#64 ∧
        sm.readReg64 .x19 = sp + 17376#64 ∧
        sm.readReg64 .x20 = sp + 27851#64 ∧
        sm.readReg64 .x21 = sp + 29024#64 ∧
        sm.readReg64 .x26 = sp + 27840#64 ∧
        sm.readReg64 .x27 = 544#64 ∧
        sm.readReg64 .x28 = sp + 28104#64 ∧
        sm.readVReg128 0#5 = packLane64 rho 8 ++ packLane64 rho 8 ∧
        sm.readVReg128 1#5 = packLane64 rho 0 ++ packLane64 rho 0 ∧
        sm.readVReg128 2#5 = bytesToVecNat rho 1 ∧
        sm.readVReg128 3#5 = bytesToVecNat rho 0 ∧
        (Pm ⊢ ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
          ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
          ((sp + 29408#64) ↦ₛ g.drop 32) ∗
          memRegion (sp + 9984#64) 64 ∗ Rest)) := by
  intro rho
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have hal9984 : ((sp + 9984#64) &&& 15#64 == 0#64) = true :=
    aligned16_add_of_dvd sp 9984 hal_sp (by omega)
  have hal27840 : ((sp + 27840#64) &&& 15#64 == 0#64) = true :=
    aligned16_add_of_dvd sp 27840 hal_sp (by omega)
  have horr9984 : ((sp + 9984#64) ||| 11#64) = sp + 9995#64 := by
    rw [orr_11_of_aligned16 _ hal9984]; clear * -; bv_omega
  have horr27840 : ((sp + 27840#64) ||| 11#64) = sp + 27851#64 := by
    rw [orr_11_of_aligned16 _ hal27840]; clear * -; bv_omega
  have hrho : rho.length = 32 := by simp [rho, hg]
  have hsig : (g.drop 32).length = 32 := by simp [hg]
  have hg_split : ((sp + 9984#64) ↦ₛ g) =
      ((sp + 9984#64) ↦ₛ rho) ∗ ((sp + 10016#64) ↦ₛ g.drop 32) := by
    dsimp only [rho]
    conv_lhs => rw [← List.take_append_drop 32 g]
    rw [pointsToBytes_append, hrho, show sp + 9984#64 + BitVec.ofNat 64 32 = sp + 10016#64 by clear * -; bv_omega]
  rw [memRegion_split' (b := sp + 48#64) (b' := sp + 56#64) (n := 8) (k := 8) rfl (by clear * -; bv_omega) (by clear * -; omega)]
  apply memRegion32_cells (sp + 29408#64); intro s0c s1c s2c s3c
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 48#64)); intro c48
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 56#64)); intro c56
  rw [hg_split, ← vec2_cells_eq_bytes (sp + 9984#64) hrho,
    ← vec2_cells_eq_bytes (sp + 10016#64) hsig]
  simp only [bitvec64_add_add_fold]
  wp_steps
  have htrunc (v : BitVec 128) : v.setWidth 64 = v.extractLsb' 0 64 := by bv_bits
  have hv3_hi : (bytesToVecNat rho 0).extractLsb' 64 64 = packLane64 rho 8 := by
    simp [bytesToVecNat, readLE_8_eq_packLane64]
  have hv3_lo : (bytesToVecNat rho 0).extractLsb' 0 64 = packLane64 rho 0 := by
    simp [bytesToVecNat, readLE_8_eq_packLane64]
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hal_sp,
      by simp [hfp], by simp,
      by simp,
      by simp,
      by simp [hx19],
      by simp,
      by simp [hx21],
      by simp [hx26],
      by simp,
      by simp [hx28],
      by simp [hv3_hi],
      by simp; rw [htrunc, hv3_lo],
      by simp; bv_bits,
      by simp; bv_bits, ?_⟩
  have hs_pts := vec2_cells_eq_bytes (sp + 29408#64) hsig
  simp only [bitvec64_add_add_fold] at hs_pts
  have hg_mem :
      ((sp + 9984#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
        ((sp + 9992#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
        ((sp + 10000#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
        ((sp + 10008#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
        ((sp + 10016#64) ↦₆₄ (bytesToVecNat (g.drop 32) 0).extractLsb' 0 64) ∗
        ((sp + 10024#64) ↦₆₄ (bytesToVecNat (g.drop 32) 0).extractLsb' 64 64) ∗
        ((sp + 10032#64) ↦₆₄ (bytesToVecNat (g.drop 32) 1).extractLsb' 0 64) ∗
        ((sp + 10040#64) ↦₆₄ (bytesToVecNat (g.drop 32) 1).extractLsb' 64 64) ⊢
      memRegion (sp + 9984#64) 64 := by
    rw [memRegion_split' (b' := sp + 10016#64) (n := 32) (k := 32) rfl (by clear * -; bv_omega) (by clear * -; omega)]
    have hc1 := cells32_entails_memRegion (sp + 9984#64)
      ((bytesToVecNat rho 0).extractLsb' 0 64) ((bytesToVecNat rho 0).extractLsb' 64 64)
      ((bytesToVecNat rho 1).extractLsb' 0 64) ((bytesToVecNat rho 1).extractLsb' 64 64)
    have hc2 := cells32_entails_memRegion (sp + 10016#64)
      ((bytesToVecNat (g.drop 32) 0).extractLsb' 0 64) ((bytesToVecNat (g.drop 32) 0).extractLsb' 64 64)
      ((bytesToVecNat (g.drop 32) 1).extractLsb' 0 64) ((bytesToVecNat (g.drop 32) 1).extractLsb' 64 64)
    simp only [bitvec64_add_add_fold] at hc1 hc2
    exact entails_sub hc1 (by sep_frame) (entails_sub hc2 (by sep_frame) (by sep_frame))
  refine entails_sub hg_mem (by sep_frame) ?_
  conv_rhs => rw [← hs_pts]
  simp only [htrunc]
  sep_frame

private theorem seg1_consts_b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (s0 sm : State) (rho : List (BitVec 8)) (Rest : SepProp)
    (hrho : rho.length = 32)
    (hsp_eq : sp = s0.sp - 30080#64) (hfp_eq : fpVal = s0.sp - 96#64)
    (hpc : sm.pc = b + 0x0258#64) (hrun : sm.status = .Running)
    (hsp : sm.sp = sp) (hsp_al : sm.spAligned = true)
    (hfp : sm.readReg64 .fp = fpVal)
    (hx1 : sm.readReg64 .x1 = 0#64)
    (hx9 : sm.readReg64 .x9 = sp + 9995#64)
    (hx10 : sm.readReg64 .x10 = sp + 11288#64)
    (hx19 : sm.readReg64 .x19 = sp + 17376#64)
    (hx20 : sm.readReg64 .x20 = sp + 27851#64)
    (hx21 : sm.readReg64 .x21 = sp + 29024#64)
    (hx26 : sm.readReg64 .x26 = sp + 27840#64)
    (hx27 : sm.readReg64 .x27 = 544#64)
    (hx28 : sm.readReg64 .x28 = sp + 28104#64)
    (hv0 : sm.readVReg128 0#5 = packLane64 rho 8 ++ packLane64 rho 8)
    (hv1 : sm.readVReg128 1#5 = packLane64 rho 0 ++ packLane64 rho 0)
    (hv2 : sm.readVReg128 2#5 = bytesToVecNat rho 1)
    (hv3 : sm.readVReg128 3#5 = bytesToVecNat rho 0)
    (hro : MlKemRoOk mlkemMpl sm.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) sm
      (((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗
        ((sp + 56#64) ↦₆₄ (sp + 17392#64)) ∗
        ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
        memRegion sp 32 ∗
        memRegion (sp + 64#64) 32 ∗
        memRegion (sp + 104#64) 24 ∗
        memRegion (sp + 352#64) 80 ∗ Rest)
      (fun s P =>
        Seg1Post s0 s ∧
        (P ⊢ Seg2ConstSlots sp rho ∗ (sp ↦ₛ rho) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  rw [memRegion_split' (b := sp) (b' := sp + 16#64) (n := 16) (k := 16) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 64#64) (b' := sp + 80#64) (n := 16) (k := 16) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 104#64) (b' := sp + 112#64) (n := 8) (k := 16) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 112#64) (b' := sp + 120#64) (n := 8) (k := 8) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 352#64) (b' := sp + 368#64) (n := 16) (k := 64) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 368#64) (b' := sp + 384#64) (n := 16) (k := 48) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 384#64) (b' := sp + 400#64) (n := 16) (k := 32) rfl (by clear * -; bv_omega) (by clear * -; omega),
    memRegion_split' (b := sp + 400#64) (b' := sp + 416#64) (n := 16) (k := 16) rfl (by clear * -; bv_omega) (by clear * -; omega)]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 104#64)); intro c104
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 112#64)); intro c112
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 120#64)); intro c120
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 64#64)); intro v64
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 80#64)); intro v80
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 352#64)); intro v352
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 384#64)); intro v384
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 368#64)); intro v368
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 16#64)); intro v16
  sep_frame_apply (sepWP_elim_vec128 (a := sp)); intro v0
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 416#64)); intro v416
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 400#64)); intro v400
  apply SepWP.seq_frozen (mid := blkPl05.base + 644#64) (fun _ _ hr hkf => hr.of_keepsFrozen hkf) hro
  wp_step
  refine step_stpQ128 (wb := none) (ea := sp + 400#64) (ea16 := sp + 416#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by clear * -; bv_omega) (by simp [hv0]; rfl) (by simp [hv1]; rfl)
    (SepStore128.vec128At rfl).left (SepStore128.vec128At rfl).left.right (by wp_norm_lhs) ?_
  intro m1
  wp_steps 2
  refine SepWP.step_stp64 (wb := none) (ea := sp + 112#64) (ea2 := sp + 120#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by clear * -; bv_omega) (by simp [hx9]; rfl) (by simp [hx10]; rfl)
    (SepStore64.here rfl).left.right.right.right.right.right.right.right.right.right.right
    (SepStore64.here rfl).left.right.right.right.right.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m1b
  wp_steps 3
  wp_step
  refine step_stpQ128 (wb := none) (ea := sp) (ea16 := sp + 16#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) rfl (by simp [hv3]; rfl) (by simp [hv2]; rfl)
    (SepStore128.vec128At rfl).left.right.right (SepStore128.vec128At rfl).left.right.right.right
    (by wp_norm_lhs) ?_
  intro m2
  have htrunc (v : BitVec 128) : v.setWidth 64 = v.extractLsb' 0 64 := by bv_bits
  have hv2_hi : (bytesToVecNat rho 1).extractLsb' 64 64 = packLane64 rho 24 := by
    simp [bytesToVecNat, readLE_8_eq_packLane64]
  have hv2_lo : (bytesToVecNat rho 1).extractLsb' 0 64 = packLane64 rho 16 := by
    simp [bytesToVecNat, readLE_8_eq_packLane64]
  refine step_stpQ128 (wb := none) (ea := sp + 368#64) (ea16 := sp + 384#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by clear * -; bv_omega)
    (by simp [hv2_hi]; rfl) (by simp; rw [htrunc, hv2_lo])
    (SepStore128.vec128At rfl).left.right.right.right.right
    (SepStore128.vec128At rfl).left.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) (fun hro1 => ?_)
  apply SepWP.seq_frozen (mid := blkPl05.base + 660#64) (fun _ _ hr hkf => hr.of_keepsFrozen hkf) hro1
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun]) (by simp [wp_norm, arm64_norm, blkPC05_rebase_fetchOff_284]; exact ⟨rfl, rfl⟩) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro1.cst16_0 mlkemData02Bytes_length cst16_0_vec (by wp_norm_lhs) ?_
  wp_step
  refine SepWP.step_str64 (wb := none) (ea := sp + 104#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by simp [hx20]; rfl)
    (SepStore64.here rfl).left.right.right.right.right.right.right.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m3b
  refine step_strQ128 (wb := none) (ea := sp + 352#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by simp; rfl)
    (SepStore128.vec128At rfl).left.right.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) (fun hro2 => ?_)
  apply SepWP.seq_frozen (mid := blkPl05.base + 668#64) (fun _ _ hr hkf => hr.of_keepsFrozen hkf) hro2
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun]) (by simp [wp_norm, arm64_norm, blkPC05_rebase_fetchOff_294]; exact ⟨rfl, rfl⟩) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro2.cst16_1 mlkemData03Bytes_length cst16_1_vec (by wp_norm_lhs) ?_
  refine step_strQ128 (wb := none) (ea := sp + 80#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by simp; rfl)
    (SepStore128.vec128At rfl).left.right.right.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m5
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) (fun hro3 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun]) (by simp [wp_norm, arm64_norm, blkPC05_rebase_fetchOff_29c]; exact ⟨rfl, rfl⟩) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro3.cst16_2 mlkemData04Bytes_length cst16_2_vec (by wp_norm_lhs) ?_
  refine step_strQ128 (wb := none) (ea := sp + 64#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hal_sp])
    (by simp [evalAddrMode, hsp]) (by simp; rfl)
    (SepStore128.vec128At rfl).left.right.right.right.right.right.right.right.right
    (by wp_norm_lhs) ?_
  intro m6
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp, hsp_eq], spAligned_of_chk (by simp [hsp]) hal_sp,
      by simp [hfp, hfp_eq], by simp [hx1],
      by simp [hx19, hsp_eq],
      by simp [hx20, hsp_eq],
      by simp [hx21, hsp_eq],
      by simp,
      by simp,
      by simp [hx26, hsp_eq],
      by simp [hx27],
      by simp [hx28, hsp_eq]⟩, ?_⟩
  rw [pointsToBytes_eq_vecRangeMem 2 sp hrho]
  simp only [VecRangeMem]
  unfold Seg2ConstSlots
  sep_frame

private theorem seg1_consts [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (s0 sk : State) (g : List (BitVec 8)) (Rest : SepProp)
    (hg : g.length = 64)
    (hsp_eq : sp = s0.sp - 30080#64) (hfp_eq : fpVal = s0.sp - 96#64)
    (hpc : sk.pc = b + 0x0214#64) (hrun : sk.status = .Running)
    (hsp : sk.sp = sp) (hsp_al : sk.spAligned = true)
    (hfp : sk.readReg64 .fp = fpVal)
    (hx19 : sk.readReg64 .x19 = sp + 17376#64)
    (hx20 : sk.readReg64 .x20 = sp + 17376#64)
    (hx21 : sk.readReg64 .x21 = sp + 29024#64)
    (hx22 : sk.readReg64 .x22 = sp + 2208#64)
    (hx23 : sk.readReg64 .x23 = sp + 27840#64)
    (hx24 : sk.readReg64 .x24 = sp + 9984#64)
    (hx26 : sk.readReg64 .x26 = sp + 27840#64)
    (hx28 : sk.readReg64 .x28 = sp + 28104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sk.mem)
    (hro : MlKemRoOk mlkemMpl sk.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) sk
      (((sp + 9984#64) ↦ₛ g) ∗
        ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
        memRegion sp 32 ∗
        memRegion (sp + 48#64) 48 ∗
        memRegion (sp + 104#64) 24 ∗
        memRegion (sp + 352#64) 80 ∗
        memRegion (sp + 29408#64) 32 ∗ Rest)
      (fun s P =>
        Seg1Post s0 s ∧
        (P ⊢ Seg2ConstSlots sp (g.take 32) ∗
          (sp ↦ₛ g.take 32) ∗
          ((sp + 29408#64) ↦ₛ g.drop 32) ∗
          memRegion (sp + 9984#64) 64 ∗ Rest)) := by
  rw [memRegion_split' (b := sp + 48#64) (b' := sp + 64#64) (n := 16) (k := 32) rfl (by clear * -; bv_omega) (by clear * -; omega)]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg1_consts_a hb hbase sp fpVal sk g _ hg hpc hrun hsp hsp_al hfp
        hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx28) ?_)
  rintro sm Pm hpcm hrunm _ hrom
    ⟨hspm, halm, hfpm, hx1m, hx9m, hx10m, hx19m, hx20m, hx21m, hx26m, hx27m, hx28m,
     hv0m, hv1m, hv2m, hv3m, hPm⟩
  have hrho : (g.take 32).length = 32 := by simp [hg]
  refine SepWP.weaken_pre (Entails.trans hPm (by sep_frame))
    (SepWP.mono
      (seg1_consts_b hb hbase sp fpVal s0 sm (g.take 32) _ hrho hsp_eq hfp_eq
        hpcm hrunm hspm halm hfpm hx1m hx9m hx10m hx19m hx20m hx21m hx26m hx27m hx28m
        hv0m hv1m hv2m hv3m hrom) ?_)
  rintro s P _ _ ⟨hpost, hP⟩
  exact ⟨hpost, Entails.trans hP (by sep_frame)⟩

private theorem split_29776_outer (sp : BitVec 64) :
    memRegion (sp + 144#64) 29776 =
      memRegion (sp + 144#64) 208 ∗
      memRegion (sp + 352#64) 80 ∗
      memRegion (sp + 432#64) 3312 ∗
      memRegion (sp + 3744#64) 4608 ∗
      memRegion (sp + 8352#64) 21056 ∗
      memRegion (sp + 29408#64) 32 ∗
      memRegion (sp + 29440#64) 480 := by
  rw [memRegion_split' (b' := sp + 352#64) (n := 208) (k := (29568 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 432#64) (n := 80) (k := (29488 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 3744#64) (n := (3312 : Nat)) (k := (26176 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 8352#64) (n := (4608 : Nat)) (k := (21568 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29408#64) (n := (21056 : Nat)) (k := 512) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29440#64) (n := 32) (k := 480) rfl (by bv_omega) (by omega)]

private theorem split_21056_prep (sp : BitVec 64) :
    memRegion (sp + 8352#64) 21056 =
      memRegion (sp + 9984#64) 32 ∗
      memRegion (sp + 10016#64) 32 ∗
      memRegion (sp + 17376#64) 64 ∗
      memRegion (sp + 27840#64) 32 ∗
      memRegion (sp + 27872#64) 1 ∗
      memRegion (sp + 29024#64) 32 ∗
      memRegion (sp + 8352#64) 1632 ∗
      memRegion (sp + 10048#64) 7328 ∗
      memRegion (sp + 17440#64) 10400 ∗
      memRegion (sp + 27873#64) 1151 ∗
      memRegion (sp + 29056#64) 352 := by
  rw [memRegion_split' (b' := sp + 9984#64) (n := (1632 : Nat)) (k := (19424 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 10016#64) (n := 32) (k := (19392 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 10048#64) (n := 32) (k := (19360 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 17376#64) (n := (7328 : Nat)) (k := (12032 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 17440#64) (n := 64) (k := (11968 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 27840#64) (n := (10400 : Nat)) (k := (1568 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 27872#64) (n := 32) (k := (1536 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 27873#64) (n := 1) (k := (1535 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29024#64) (n := (1151 : Nat)) (k := 384) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29056#64) (n := 32) (k := 352) rfl (by bv_omega) (by omega)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem join_21056_post (sp : BitVec 64) :
    memRegion (sp + 8352#64) 21056 =
      memRegion (sp + 8352#64) 1632 ∗
      memRegion (sp + 9984#64) 64 ∗
      memRegion (sp + 10048#64) 7328 ∗
      memRegion (sp + 17376#64) 64 ∗
      memRegion (sp + 17440#64) 10400 ∗
      memRegion (sp + 27840#64) 33 ∗
      memRegion (sp + 27873#64) 1151 ∗
      memRegion (sp + 29024#64) 32 ∗
      memRegion (sp + 29056#64) 352 := by
  rw [memRegion_split' (b' := sp + 9984#64) (n := (1632 : Nat)) (k := (19424 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 10048#64) (n := 64) (k := (19360 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 17376#64) (n := (7328 : Nat)) (k := (12032 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 17440#64) (n := 64) (k := (11968 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 27840#64) (n := (10400 : Nat)) (k := (1568 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 27873#64) (n := 33) (k := (1535 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29024#64) (n := (1151 : Nat)) (k := 384) rfl (by bv_omega) (by omega),
    memRegion_split' (b' := sp + 29056#64) (n := 32) (k := 352) rfl (by bv_omega) (by omega)]

theorem seg1_prologue_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    (hseed : seed.length = 64)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = seedA) (hx1 : s0.readReg64 .x1 = outPtr)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x02b8#64) s0
      (stackAt s0.sp 31216 ∗ (seedA ↦ₛ seed) ∗ F)
      (fun s P =>
        Seg1Post s0 s ∧ (P ⊢ Seg1Spatial s0 seedA outPtr seed F)) := by
  let sp := s0.sp - 30080#64
  refine sepWP_seq_env hcl hro
    (seg1_spill_and_probe hb hbase s0 ((seedA ↦ₛ seed) ∗ F) hpc hrun hsp0 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hal1, hx0_1, hx1_1, hfp1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
    (sepWP_seq_env hcl1 hro1
      (seg1_zero_setup hb hbase s0 s1 seedA outPtr _ hpc1 hrun1 hsp1 hal1
        (hx0_1.trans hx0) (hx1_1.trans hx1) hfp1 hcl1 hro1) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hal4, hfp4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx26_4, hx28_4, hP4⟩
  have hsplit_40 : memRegion sp 40 = memRegion sp 32 ∗ memRegion (sp + 32#64) 8 :=
    memRegion_split' (b := sp) (b' := sp + 32#64) (n := 32) (k := 8) rfl (by clear * -; bv_omega) (by clear * -; omega)
  have hsplit_80 : memRegion (sp + 48#64) 80 =
      memRegion (sp + 48#64) 48 ∗ memRegion (sp + 96#64) 8 ∗ memRegion (sp + 104#64) 24 := by
    rw [memRegion_split' (b := sp + 48#64) (b' := sp + 96#64) (n := 48) (k := 32) rfl (by clear * -; bv_omega) (by clear * -; omega),
      memRegion_split' (b := sp + 96#64) (b' := sp + 104#64) (n := 8) (k := 24) rfl (by clear * -; bv_omega) (by clear * -; omega)]
  refine SepWP.weaken_pre
    (Entails.trans hP4 (by
      dsimp only [sp]
      rw [hsplit_40, hsplit_80, split_29776_outer sp, split_21056_prep sp]
      sep_frame))
    (sepWP_seq_env hcl4 hro4
      (seg1_hash_prep hb hbase sp (s0.sp - 96#64) seedA seed s4 _ hseed
        hpc4 hrun4 hsp4 hal4 hfp4 hx19_4 hx20_4 hx22_4 hx23_4 hx24_4 hx26_4 hx28_4) ?_)
  rintro sm Pm hpcm hrunm hclm hrom
    ⟨hspm, halm, hfpm, hx0m, hx1m, hx2m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx26m, hx28m, hPm⟩
  have hmsg_len : (seed.take 32 ++ [3#8]).length = 33 := by simp [hseed]
  refine SepWP.weaken_pre (Entails.trans hPm (by sep_frame))
    (sepWP_seq_env hclm hrom
      (seg1_b00_call hb hbase sp (s0.sp - 96#64) (seed.take 32 ++ [3#8]) sm _ hmsg_len
        hpcm hrunm hspm halm hfpm hx0m hx1m hx2m
        hx19m hx20m hx21m hx22m hx23m hx24m hx26m hx28m hclm hrom) ?_)
  rintro sk Pk hpck hrunk hclk hrok
    ⟨hspk, halk, hfpk, hx19k, hx20k, hx21k, hx22k, hx23k, hx24k, hx26k, hx28k, hPk⟩
  have hg_len : (sha3_512List (seed.take 32 ++ [3#8])).length = 64 := sha3_512List_length _
  refine SepWP.weaken_pre (Entails.trans hPk (by sep_frame))
    (SepWP.mono
      (seg1_consts hb hbase sp (s0.sp - 96#64) s0 sk _ _ hg_len rfl rfl hpck hrunk hspk halk hfpk
        hx19k hx20k hx21k hx22k hx23k hx24k hx26k hx28k hclk hrok) ?_)
  rintro s P _ _ ⟨hpost, hP⟩
  refine ⟨hpost, Entails.trans hP ?_⟩
  unfold Seg1Spatial B05LateSlots
  dsimp only [sp]
  rw [join_21056_post sp]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG
