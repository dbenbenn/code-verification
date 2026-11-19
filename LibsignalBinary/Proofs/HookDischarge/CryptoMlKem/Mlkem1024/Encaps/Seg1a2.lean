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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `kyber_encapsulate` (`B07`) — Segment 1a2 (`+0x00ac .. +0x0228`)

1. Stages all 32 bytes of `m = sha3_256List rand` from `sp + 28848` into both
   `SpilledMsgWords sp m` (`[sp + 16 .. sp + 144)`) and `((sp + 2432#64) ↦ₛ m)`
   (`+0x00ac → +0x0220`, split at `+0x0188` to keep active spatial atoms ≤ 36).
2. Zeroes `[sp + 32896 .. sp + 32928)` (`stp q0, q0, [x29, #-112]`) and invokes `B02`
   (`keccak2::<136, 6>`) at `+0x0224` on `(pkA ↦ₛ pk)` (`1568` B), producing
   `hPk = sha3_256List pk` at `sp + 32896` while keeping `(pkA ↦ₛ pk)` intact.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepStore128
  SepWP.of_memRegion_vecRangeMem
  Vec128At
  VecRangeMem
  step_stpQ128
  vecRangeMem_entails_memRegion
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_cell8
  sepWP_elim_region32
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq
  blk07_tree_size
  blkLib07
  blkPC07
  blkPl07
  blkPlaceable07
  blkTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  SpilledMsgHi
  SpilledMsgLo
  SpilledMsgWords
  blk02_rw1_07
  msgW32
  sha3_256List_len
  stackAt_1136_split_1040
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x00ac → 0x0224]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem trunc32_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 32 = b.zeroExtend 32 := by bv_omega

@[simp, arm64_norm, wp_norm]
private theorem trunc8_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 8 = b := by bv_omega

attribute [local irreducible] blkPC07 SpilledMsgLo SpilledMsgHi sha3_256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 trunc32_zext64_8 trunc8_zext64_8

/-! ## 1. Subword & Byte-Cell Elimination Helpers -/

private theorem sepWP_elim_pair32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ w0 w1 : BitVec 32,
      SepWP prog target s (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1)) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  refine sepWP_elim_cell8 fun v => ?_
  have hv : (v.extractLsb' 32 32) ++ (v.truncate 32) = v := by bv_bits
  rw [← hv, ← pointsTo32_pair a (v.truncate 32) (v.extractLsb' 32 32)]
  exact h _ _

private theorem sepWP_elim_words8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32,
      SepWP prog target s
        (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗ ((a + 8#64) ↦₃₂ w2) ∗ ((a + 12#64) ↦₃₂ w3) ∗
          ((a + 16#64) ↦₃₂ w4) ∗ ((a + 20#64) ↦₃₂ w5) ∗ ((a + 24#64) ↦₃₂ w6) ∗
          ((a + 28#64) ↦₃₂ w7)) ∗ R0) post) :
    SepWP prog target s (memRegion a 32 ∗ R0) post := by
  have hsplit : memRegion a 32 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 := by
    rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 24) rfl rfl (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  sep_frame_apply (sepWP_elim_pair32 (a := a)); intro w0 w1
  sep_frame_apply (sepWP_elim_pair32 (a := a + 8#64)); intro w2 w3
  sep_frame_apply (sepWP_elim_pair32 (a := a + 16#64)); intro w4 w5
  sep_frame_apply (sepWP_elim_pair32 (a := a + 24#64)); intro w6 w7
  refine SepWP.weaken_pre ?_ (h w0 w1 w2 w3 w4 w5 w6 w7)
  have e12 : a + 8#64 + 4#64 = a + 12#64 := by bv_omega
  have e20 : a + 16#64 + 4#64 = a + 20#64 := by bv_omega
  have e28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
  simp only [e12, e20, e28]
  sep_frame

private theorem sepWP_elim_bytes2 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ b0 b1 : BitVec 8,
      SepWP prog target s (((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) ∗ R0) post) :
    SepWP prog target s (memRegion a 2 ∗ R0) post := by
  rw [memRegion_eq_exists_bytes a 2 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hbs => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try simp at hbs
  simpa [pointsToBytes_cons, pointsToBytes_nil, sepConj_assoc] using h b0 b1

private theorem list8_eq_getD (bs : List (BitVec 8)) (h : bs.length = 8) :
    bs = [bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
          bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8, bs.getD 7 0#8] := by
  rcases bs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all

private theorem pointsToBytes8_eq (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7]) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
       ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) := by
  simp [pointsToBytes_cons, pointsToBytes_nil]

private theorem sepWP_elim_bytes8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      SepWP prog target s
        (((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
          ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) ∗ R0)
        post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  rw [memRegion_eq_exists_bytes a 8 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hbs => ?_
  rw [list8_eq_getD bs hbs, pointsToBytes8_eq]
  exact h _ _ _ _ _ _ _ _

private theorem pointsToBytes_slice8 (a : BitVec 64) (m : List (BitVec 8)) (off : Nat)
    (hoff : off + 8 ≤ m.length) :
    ((a ↦₈ m.getD off 0#8) ∗ ((a + 1#64) ↦₈ m.getD (off + 1) 0#8) ∗
     ((a + 2#64) ↦₈ m.getD (off + 2) 0#8) ∗ ((a + 3#64) ↦₈ m.getD (off + 3) 0#8) ∗
     ((a + 4#64) ↦₈ m.getD (off + 4) 0#8) ∗ ((a + 5#64) ↦₈ m.getD (off + 5) 0#8) ∗
     ((a + 6#64) ↦₈ m.getD (off + 6) 0#8) ∗ ((a + 7#64) ↦₈ m.getD (off + 7) 0#8)) =
      (a ↦ₛ (m.drop off).take 8) := by
  have hlen : ((m.drop off).take 8).length = 8 := by rw [List.length_take, List.length_drop]; omega
  conv => rhs; rw [list8_eq_getD _ hlen]
  have hg (k : Nat) (hk : k < 8) : ((m.drop off).take 8).getD k 0#8 = m.getD (off + k) 0#8 := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide), hg 3 (by decide),
    hg 4 (by decide), hg 5 (by decide), hg 6 (by decide), hg 7 (by decide), Nat.add_zero]
  exact (pointsToBytes8_eq a _ _ _ _ _ _ _ _).symm

private theorem take8_append_drop8_take8 (m : List (BitVec 8)) (_hm : 16 ≤ m.length) :
    (m.drop 0).take 8 ++ (m.drop 8).take 8 = m.take 16 := by
  have h16 : m.take 16 = (m.take 16).take 8 ++ (m.take 16).drop 8 :=
    (List.take_append_drop 8 (m.take 16)).symm
  rw [h16]
  simp [List.take_take, List.drop_take]

private theorem drop16_take8_append_drop24 (m : List (BitVec 8)) (hm : m.length = 32) :
    (m.drop 16).take 8 ++ (m.drop 24).take 8 = m.drop 16 := by
  have h16 : m.drop 16 = (m.drop 16).take 8 ++ (m.drop 16).drop 8 :=
    (List.take_append_drop 8 (m.drop 16)).symm
  have hd : (m.drop 16).drop 8 = (m.drop 24).take 8 := by
    rw [List.drop_drop, show 16 + 8 = 24 from rfl, List.take_of_length_le (by simp [hm])]
  conv => rhs; rw [h16, hd]

/-! ## 2. Part 1 (`+0x00ac → +0x0188`): Low Spills & First 18 Message Bytes -/

private theorem seg1a2_part1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (m : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32)
    (hpc : s.pc = b + 0x00ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx20 : s.readReg64 .x20 = pkA)
    (hx21 : s.readReg64 .x21 = pkA + 384#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 2560#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0188#64) s
      (((sp + 28848#64) ↦ₛ m) ∗ memRegion (sp + 16#64) 72 ∗
        memRegion (sp + 2432#64) 18 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = sp + 12832#64 ∧
        s1.readReg64 .x1 = sp + 32896#64 ∧
        s1.readReg64 .x2 = sp + 2560#64 ∧
        s1.readReg64 .x8 = (m.getD 20 0#8).zeroExtend 64 ∧
        s1.readReg64 .x9 = (m.getD 19 0#8).zeroExtend 64 ∧
        s1.readReg64 .x10 = (m.getD 18 0#8).zeroExtend 64 ∧
        s1.readReg64 .x11 = (m.getD 21 0#8).zeroExtend 64 ∧
        s1.readReg64 .x19 = pkA + 384#64 ∧
        s1.readReg64 .x20 = pkA ∧
        s1.readReg64 .x21 = pkA + 384#64 ∧
        s1.readReg64 .x22 = sp + 26768#64 ∧
        s1.readReg64 .x23 = sp + 2560#64 ∧
        s1.readReg64 .x24 = sp + 27032#64 ∧
        s1.readReg64 .fp = sp + 33008#64 ∧
        s1.readVReg128 0#5 = 0#128 ∧
        (P1 ⊢ ((sp + 28848#64) ↦ₛ m) ∗ SpilledMsgLo sp m ∗
          ((sp + 80#64) ↦₃₂ msgW32 m 17) ∗ ((sp + 84#64) ↦₃₂ msgW32 m 16) ∗
          ((sp + 2432#64) ↦ₛ m.take 16) ∗
          ((sp + 2448#64) ↦₈ m.getD 16 0#8) ∗ ((sp + 2449#64) ↦₈ m.getD 17 0#8) ∗ Rest)) := by
  subst hbase
  have hspA : s.spAligned = true := spAligned_of_chk hsp hsp_chk
  have hsplitW : memRegion (sp + 16#64) 72 =
      memRegion (sp + 16#64) 32 ∗ memRegion (sp + 48#64) 32 ∗ memRegion (sp + 80#64) 8 := by
    rw [memRegion_split' (b' := sp + 48#64) (n := 32) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 48#64) (b' := sp + 80#64) (n := 32) (k := 8) rfl (by bv_omega) (by decide)]
  have hsplitB : memRegion (sp + 2432#64) 18 =
      memRegion (sp + 2432#64) 8 ∗ memRegion (sp + 2440#64) 8 ∗ memRegion (sp + 2448#64) 2 := by
    rw [memRegion_split' (b' := sp + 2440#64) (n := 8) (k := 10) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2440#64) (b' := sp + 2448#64) (n := 8) (k := 2) rfl (by bv_omega) (by decide)]
  rw [hsplitW, hsplitB]
  sep_frame_apply (sepWP_elim_words8 (a := sp + 16#64)); intro w0 w1 w2 w3 w4 w5 w6 w7
  sep_frame_apply (sepWP_elim_words8 (a := sp + 48#64)); intro w8 w9 w10 w11 w12 w13 w14 w15
  sep_frame_apply (sepWP_elim_pair32 (a := sp + 80#64)); intro w16 w17
  sep_frame_apply (sepWP_elim_bytes8 (a := sp + 2432#64)); intro b0 b1 b2 b3 b4 b5 b6 b7
  sep_frame_apply (sepWP_elim_bytes8 (a := sp + 2440#64)); intro b8 b9 b10 b11 b12 b13 b14 b15
  sep_frame_apply (sepWP_elim_bytes2 (a := sp + 2448#64)); intro b16 b17
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hx22], by simp [hx23], by simp [hx24],
      by simp [hfp], by simp, ?_⟩
  delta SpilledMsgLo
  dsimp only [msgW32]
  have hb0 := pointsToBytes_slice8 (sp + 2432#64) m 0 (by omega)
  have hb8 := pointsToBytes_slice8 (sp + 2440#64) m 8 (by omega)
  have htake16 : ((sp + 2432#64) ↦ₛ m.take 16) =
      ((sp + 2432#64) ↦ₛ (m.drop 0).take 8) ∗ ((sp + 2440#64) ↦ₛ (m.drop 8).take 8) := by
    rw [← take8_append_drop8_take8 m (by omega), pointsToBytes_append]
    have hl : ((m.drop 0).take 8).length = 8 := by rw [List.length_take, List.length_drop]; omega
    rw [hl]
    have ha : sp + 2432#64 + BitVec.ofNat 64 8 = sp + 2440#64 := by bv_omega
    rw [ha]
  rw [htake16, ← hb0, ← hb8]
  simp only [Nat.zero_add, BitVec.add_assoc]
  sep_frame

/-! ## 3. Part 2 (`+0x0188 → +0x0228`): High Spills & `B02` (`hPk = sha3_256List pk`) -/

private theorem seg1a2_part2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (m : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32)
    (hpc : s.pc = b + 0x0188#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sp + 12832#64)
    (hx1 : s.readReg64 .x1 = sp + 32896#64)
    (hx2 : s.readReg64 .x2 = sp + 2560#64)
    (hx8 : s.readReg64 .x8 = (m.getD 20 0#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (m.getD 19 0#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (m.getD 18 0#8).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (m.getD 21 0#8).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx20 : s.readReg64 .x20 = pkA)
    (hx21 : s.readReg64 .x21 = pkA + 384#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 2560#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hfp : s.readReg64 .fp = sp + 33008#64)
    (hv0 : s.readVReg128 0#5 = 0#128) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0224#64) s
      (((sp + 28848#64) ↦ₛ m) ∗
        ((sp + 80#64) ↦₃₂ msgW32 m 17) ∗ ((sp + 84#64) ↦₃₂ msgW32 m 16) ∗
        memRegion (sp + 88#64) 56 ∗
        ((sp + 2448#64) ↦₈ m.getD 16 0#8) ∗ ((sp + 2449#64) ↦₈ m.getD 17 0#8) ∗
        memRegion (sp + 2450#64) 14 ∗
        memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 32896#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 12832#64 ∧
        sm.readReg64 .x1 = sp + 32896#64 ∧
        sm.readReg64 .x2 = sp + 2560#64 ∧
        sm.readReg64 .x19 = pkA + 384#64 ∧
        sm.readReg64 .x20 = pkA ∧
        sm.readReg64 .x21 = pkA + 384#64 ∧
        sm.readReg64 .x22 = sp + 26768#64 ∧
        sm.readReg64 .x23 = sp + 2560#64 ∧
        sm.readReg64 .x24 = sp + 27032#64 ∧
        sm.readReg64 .fp = sp + 33008#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 12832#64) pkA pkA 1568 1568 ∗
          memRegion (sp + 32896#64) 32 ∗
          (((sp + 28848#64) ↦ₛ m) ∗ SpilledMsgHi sp m ∗
            ((sp + 2448#64) ↦ₛ m.drop 16) ∗ Rest))) := by
  subst hbase
  have hspA : s.spAligned = true := spAligned_of_chk hsp hsp_chk
  have hsplitW : memRegion (sp + 88#64) 56 =
      memRegion (sp + 88#64) 32 ∗ memRegion (sp + 120#64) 8 ∗
      memRegion (sp + 128#64) 8 ∗ memRegion (sp + 136#64) 8 := by
    rw [memRegion_split' (b' := sp + 120#64) (n := 32) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 120#64) (b' := sp + 128#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 128#64) (b' := sp + 136#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  have hsplitB : memRegion (sp + 2450#64) 14 =
      memRegion (sp + 2450#64) 2 ∗ memRegion (sp + 2452#64) 2 ∗
      memRegion (sp + 2454#64) 2 ∗ memRegion (sp + 2456#64) 8 := by
    rw [memRegion_split' (b' := sp + 2452#64) (n := 2) (k := 12) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2452#64) (b' := sp + 2454#64) (n := 2) (k := 10) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2454#64) (b' := sp + 2456#64) (n := 2) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplitW, hsplitB]
  sep_frame_apply (sepWP_elim_words8 (a := sp + 88#64)); intro w18 w19 w20 w21 w22 w23 w24 w25
  sep_frame_apply (sepWP_elim_pair32 (a := sp + 120#64)); intro w26 w27
  sep_frame_apply (sepWP_elim_pair32 (a := sp + 128#64)); intro w28 w29
  sep_frame_apply (sepWP_elim_pair32 (a := sp + 136#64)); intro w30 w31
  sep_frame_apply (sepWP_elim_bytes2 (a := sp + 2450#64)); intro b18 b19
  sep_frame_apply (sepWP_elim_bytes2 (a := sp + 2452#64)); intro b20 b21
  sep_frame_apply (sepWP_elim_bytes2 (a := sp + 2454#64)); intro b22 b23
  sep_frame_apply (sepWP_elim_bytes8 (a := sp + 2456#64)); intro b24 b25 b26 b27 b28 b29 b30 b31
  sep_frame_apply (sepWP_elim_region32 (a := sp + 12832#64)); intro s0_c s1_c s2_c s3_c
  refine SepWP.of_memRegion_vecRangeMem 2 (sp + 32896#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun f32 => ?_
  dsimp only [VecRangeMem]
  simp only [sepConj_emp]
  have ha32_16 : sp + 32896#64 + 16#64 = sp + 32912#64 := by bv_omega
  wp_steps 38
  refine step_stpQ128 (wb := none) (ea := sp + 32896#64) (ea16 := sp + 32912#64)
    (v1 := 0#128) (v2 := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode, hfp]) ha32_16 (by simp [hv0]) (by simp [hv0])
    (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
    (SepStore128.left (SepStore128.right (SepStore128.vec128At ha32_16)))
    (by wp_norm_lhs) ?_
  intro _
  have hz32 : Vec128At (sp + 32896#64) 0#128 ∗ Vec128At (sp + 32896#64 + 16#64) 0#128 ⊢
      memRegion (sp + 32896#64) 32 := by
    simpa [VecRangeMem, sepConj_emp] using
      vecRangeMem_entails_memRegion 2 (sp + 32896#64) (fun _ => 0#128)
  refine SepWP.weaken_pre (sepConj_mono_left hz32) ?_
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp [hx0], by simp [hx1], by simp [hx2],
      by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hx22], by simp [hx23], by simp [hx24],
      by simp [hfp], ?_⟩
  delta SpilledMsgHi
  dsimp only [msgW32]
  unfold Keccak2SlicesRW
  have hb16 := pointsToBytes_slice8 (sp + 2448#64) m 16 (by omega)
  have hb24 := pointsToBytes_slice8 (sp + 2456#64) m 24 (by omega)
  have hdrop16 : ((sp + 2448#64) ↦ₛ m.drop 16) =
      ((sp + 2448#64) ↦ₛ (m.drop 16).take 8) ∗ ((sp + 2456#64) ↦ₛ (m.drop 24).take 8) := by
    conv => lhs; rw [← drop16_take8_append_drop24 m hm]
    rw [pointsToBytes_append]
    have hl : ((m.drop 16).take 8).length = 8 := by simp [hm]
    have ha : sp + 2448#64 + BitVec.ofNat 64 8 = sp + 2456#64 := by bv_omega
    rw [hl, ha]
  rw [hdrop16, ← hb16, ← hb24]
  simp only [BitVec.add_assoc]
  sep_frame

theorem keccak2SlicesRW_entails_memRegion32 (sA p1 p2 : BitVec 64) (n1 n2 : Nat) :
    Keccak2SlicesRW sA p1 p2 n1 n2 ⊢ memRegion sA 32 := by
  unfold Keccak2SlicesRW
  rw [memRegion_split' (b' := sA + 8#64) (n := 8) (k := 24) rfl rfl (by decide),
    memRegion_split' (b := sA + 8#64) (b' := sA + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sA + 16#64) (b' := sA + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion sA p1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (sA + 8#64) (BitVec.ofNat 64 n1))
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (sA + 16#64) p2)
        (ProofLib.pointsTo64_entails_memRegion (sA + 24#64) (BitVec.ofNat 64 n2))))

theorem seg1a2_hash_pk [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (pk m : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568) (hm : m.length = 32)
    (hpc : s.pc = b + 0x00ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx20 : s.readReg64 .x20 = pkA)
    (hx21 : s.readReg64 .x21 = pkA + 384#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 2560#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0228#64) s
      ((pkA ↦ₛ pk) ∗ stackAt sp 1136 ∗
        memRegion (sp + 16#64) 128 ∗ memRegion (sp + 2432#64) 32 ∗
        memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
        ((sp + 28848#64) ↦ₛ m) ∗ memRegion (sp + 32896#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = pkA + 384#64 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = pkA + 384#64 ∧
        sf.readReg64 .x22 = sp + 26768#64 ∧
        sf.readReg64 .x23 = sp + 2560#64 ∧
        sf.readReg64 .x24 = sp + 27032#64 ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ (pkA ↦ₛ pk) ∗ stackAt sp 1136 ∗
          SpilledMsgWords sp m ∗ ((sp + 2432#64) ↦ₛ m) ∗
          memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 32 ∗
          memRegion (sp + 28848#64) 32 ∗
          ((sp + 32896#64) ↦ₛ sha3_256List pk) ∗ Rest)) := by
  subst hbase
  have h128 : memRegion (sp + 16#64) 128 = memRegion (sp + 16#64) 72 ∗ memRegion (sp + 88#64) 56 :=
    memRegion_split' (b' := sp + 88#64) (n := 72) (k := 56) rfl (by bv_omega) (by decide)
  have h32 : memRegion (sp + 2432#64) 32 = memRegion (sp + 2432#64) 18 ∗ memRegion (sp + 2450#64) 14 :=
    memRegion_split' (b' := sp + 2450#64) (n := 18) (k := 14) rfl (by bv_omega) (by decide)
  rw [h128, h32, stackAt_1136_split_1040 sp]
  refine SepWP.weaken_pre (show _ ⊢ ((sp + 28848#64) ↦ₛ m) ∗ memRegion (sp + 16#64) 72 ∗
      memRegion (sp + 2432#64) 18 ∗ ((pkA ↦ₛ pk) ∗ stackAt sp 1040 ∗ memRegion (sp - 1136#64) 96 ∗
        memRegion (sp + 88#64) 56 ∗ memRegion (sp + 2450#64) 14 ∗ memRegion (sp + 2560#64) 32 ∗
        memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 32896#64) 32 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg1a2_part1 hb rfl s sp pkA m _ hm hpc hrun hsp hsp_chk
    hx19 hx20 hx21 hx22 hx23 hx24 hfp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, _, hx0_1, hx1_1, hx2_1, hx8_1, hx9_1, hx10_1, hx11_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hfp1, hv0_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
      ((sp + 28848#64) ↦ₛ m) ∗ ((sp + 80#64) ↦₃₂ msgW32 m 17) ∗ ((sp + 84#64) ↦₃₂ msgW32 m 16) ∗
      memRegion (sp + 88#64) 56 ∗ ((sp + 2448#64) ↦₈ m.getD 16 0#8) ∗
      ((sp + 2449#64) ↦₈ m.getD 17 0#8) ∗ memRegion (sp + 2450#64) 14 ∗
      memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 32896#64) 32 ∗
      ((pkA ↦ₛ pk) ∗ stackAt sp 1040 ∗ memRegion (sp - 1136#64) 96 ∗
        SpilledMsgLo sp m ∗ ((sp + 2432#64) ↦ₛ m.take 16) ∗ memRegion (sp + 2560#64) 32 ∗ Rest)
      by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1 (seg1a2_part2 hb rfl s1 sp pkA m _ hm hpc1 hrun1 hsp1 hsp_chk
    hx0_1 hx1_1 hx2_1 hx8_1 hx9_1 hx10_1 hx11_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hfp1 hv0_1) ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hfpm, hPm⟩
  have hPm' : Pm ⊢ Keccak2SlicesRW (sp + 12832#64) pkA pkA pk.length pk.length ∗
      (pkA ↦ₛ pk) ∗ memRegion (sp + 32896#64) 32 ∗ memRegion (sp + 2560#64) 32 ∗
      stackAt sp 1040 ∗
      (memRegion (sp - 1136#64) 96 ∗ SpilledMsgLo sp m ∗ SpilledMsgHi sp m ∗
        ((sp + 2432#64) ↦ₛ m.take 16) ∗ ((sp + 2448#64) ↦ₛ m.drop 16) ∗
        ((sp + 28848#64) ↦ₛ m) ∗ Rest) := by
    rw [hpk]; exact Entails.trans hPm (by sep_frame)
  refine SepWP.weaken_pre hPm' ?_
  have hlt : pk.length < 2 ^ 32 := by rw [hpk]; decide
  wp_call (blk02_rw1_07 blkPl07.base) (sp + 12832#64, pkA, sp + 32896#64, sp + 2560#64, pk)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hm_join : ((sp + 2432#64) ↦ₛ m.take 16) ∗ ((sp + 2448#64) ↦ₛ m.drop 16) =
      ((sp + 2432#64) ↦ₛ m) := by
    have hp := pointsToBytes_take_drop (sp + 2432#64) 16 m (by simp [hm])
    have ha : sp + 2432#64 + BitVec.ofNat 64 16 = sp + 2448#64 := by clear * -; bv_omega
    rw [ha] at hp; exact hp.symm
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 12832#64) pkA pkA pk.length pk.length
  have hout1 : ((sp + 2560#64) ↦ₛ sha3_256List pk) ⊢ memRegion (sp + 2560#64) 32 := by
    rw [← sha3_256List_len pk]; exact pointsToBytes_entails_memRegion _ _
  have hm_reg : ((sp + 28848#64) ↦ₛ m) ⊢ memRegion (sp + 28848#64) 32 := by
    rw [← hm]; exact pointsToBytes_entails_memRegion _ _
  unfold SpilledMsgWords
  rw [hspm, ← hm_join]
  refine Entails.trans
    (Q := memRegion (sp + 12832#64) 32 ∗
      (pkA ↦ₛ pk) ∗ ((sp + 32896#64) ↦ₛ sha3_256List pk) ∗
      memRegion (sp + 2560#64) 32 ∗ stackAt sp 1040 ∗
      (memRegion (sp - 1136#64) 96 ∗ SpilledMsgLo sp m ∗ SpilledMsgHi sp m ∗
        ((sp + 2432#64) ↦ₛ m.take 16) ∗ ((sp + 2448#64) ↦ₛ m.drop 16) ∗
        memRegion (sp + 28848#64) 32 ∗ Rest))
    ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hout1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hm_reg))))))))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2
