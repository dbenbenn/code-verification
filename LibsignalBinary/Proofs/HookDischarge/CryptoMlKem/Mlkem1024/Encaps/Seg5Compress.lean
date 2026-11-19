/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd

/-!
# `kyber_encapsulate` (`B07`) — Segment 5 `compress_5` + `serialize_5` (`+0x9d34 .. +0x9ed4`)

Proves the 16-iteration `compress_and_serialize_5` loop (`+0x9d34 .. +0x9ed4`) writing `c₂` (`160` B)
at `[sp + 24512, sp + 24672)` immediately after `c₁` (`[sp + 23104, sp + 24512)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid (neonSerialize5Bytes neonSerialize5Half)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress (ByteRangeMem sepWP_elim_byteRange step_str8_byteRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd (exec_umov_h0 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5 exec_umov_h6)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Add (offSeg5Compress)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd
  (c10321340Vec c1664Vec c2097120Vec c31Vec c3329Vec compress5EvOut compress5OdOut
   compress5_trn1_eq lane16_neonCompress8h_5_mask neonCompressSerialize5Poly
   neonCompressSerialize5Poly_eq neonCompressSerialize5Poly_length offSeg5SerLoop
   offSeg5SerStore offSeg5Tail seg5_inner_simd seg5_ser_header ser5_b0 ser5_b1
   ser5_b2 ser5_b3 ser5_b4)
export LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd
  (neonCompressSerialize5Poly neonCompressSerialize5Poly_eq neonCompressSerialize5Poly_length offSeg5Tail)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5CompressSimd.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x9e10 → 0x9ed0]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm]
theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym
end Simp
open scoped Simp

private theorem byteRangeMem_split5 (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 10 a f = ByteRangeMem 5 a f ∗ ByteRangeMem 5 (a + 5#64) (fun i => f (i + 5)) := by
  dsimp only [ByteRangeMem]; simp only [sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd, Nat.add_assoc]

private theorem byteRangeMem5_eq_cells (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 5 a f =
      (a ↦₈ f 0) ∗ ((a + 1#64) ↦₈ f 1) ∗ ((a + 2#64) ↦₈ f 2) ∗ ((a + 3#64) ↦₈ f 3) ∗ ((a + 4#64) ↦₈ f 4) := by
  dsimp only [ByteRangeMem]; simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem cells5_eq_neonSerialize5Half (a : BitVec 64) (v : BitVec 128) :
    let c : Fin 8 → BitVec 16 := fun j => lane16 v j &&& 0x001f#16
    (a ↦₈ (c 0 ||| (c 1 <<< 5)).truncate 8) ∗ ((a + 1#64) ↦₈ ((c 1 >>> 3) ||| (c 2 <<< 2) ||| (c 3 <<< 7)).truncate 8) ∗
    ((a + 2#64) ↦₈ ((c 3 >>> 1) ||| (c 4 <<< 4)).truncate 8) ∗ ((a + 3#64) ↦₈ ((c 4 >>> 4) ||| (c 5 <<< 1) ||| (c 6 <<< 6)).truncate 8) ∗
    ((a + 4#64) ↦₈ ((c 6 >>> 2) ||| (c 7 <<< 3)).truncate 8) = (a ↦ₛ neonSerialize5Half v) := by
  dsimp only [neonSerialize5Half]; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem cells10_eq_neonSerialize5Bytes (a : BitVec 64) (v0 v1 : BitVec 128) :
    (a ↦ₛ neonSerialize5Half v0) ∗ ((a + 5#64) ↦ₛ neonSerialize5Half v1) = (a ↦ₛ neonSerialize5Bytes v0 v1) := by
  rw [neonSerialize5Bytes, pointsToBytes_append, show (neonSerialize5Half v0).length = 5 by rfl]

private def ser5Chunk (v : Poly16) (c : Nat) : List (BitVec 8) :=
  neonSerialize5Bytes (neonCompress8h 5 (polyVecNat v (2 * c))) (neonCompress8h 5 (polyVecNat v (2 * c + 1)))

private def ser5Prefix (v : Poly16) (c : Nat) : List (BitVec 8) := ((List.range c).map (ser5Chunk v)).flatten

private theorem ser5Chunk_length (v : Poly16) (c : Nat) : (ser5Chunk v c).length = 10 := rfl

private theorem ser5Prefix_length (v : Poly16) (c : Nat) : (ser5Prefix v c).length = 10 * c := by
  induction c with
  | zero => simp [ser5Prefix]
  | succ n ih =>
    rw [show ser5Prefix v (n + 1) = ser5Prefix v n ++ ser5Chunk v n by simp [ser5Prefix, List.range_succ, List.flatten_append]]
    rw [List.length_append, ih, ser5Chunk_length]; omega

private theorem ser5Prefix_succ (v : Poly16) (c : Nat) : ser5Prefix v (c + 1) = ser5Prefix v c ++ ser5Chunk v c := by
  simp [ser5Prefix, List.range_succ, List.flatten_append]

private theorem ser5Prefix_sixteen (v : Poly16) : ser5Prefix v 16 = neonCompressSerialize5Poly v := rfl

private theorem ser5_prefix_append_chunk (dst : BitVec 64) (v : Poly16) (c : Nat) :
    (dst ↦ₛ ser5Prefix v c) ∗ ((dst + BitVec.ofNat 64 (10 * c)) ↦ₛ ser5Chunk v c) = (dst ↦ₛ ser5Prefix v (c + 1)) := by
  rw [ser5Prefix_succ, pointsToBytes_append, ser5Prefix_length]

attribute [local irreducible]
  blkPC07 polyVecNat dup8x16 lane16 simdTrn1_8h neonCompress8h

attribute [local wp_norm ↓ high]
  exec_umov_h0 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5 exec_umov_h6

private theorem trunc32_zext64_shl (x : BitVec 16) (n : Nat) :
    ((x.zeroExtend 64) <<< n).truncate 32 = (x.zeroExtend 32) <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, hi, show i < 64 by omega, decide_true, Bool.true_and]
  by_cases hn : i < n
  · simp [hn]
  · simp [hn, show i - n < 32 by omega, show i - n < 64 by omega]

local macro "s5_strb " ea:term:arg hx11:term:arg hrun:term:arg
    pcOff:num nextOff:num k:num rt:term:arg : tactic => `(tactic|
  (refine step_str8_byteRange blkPl07.base $ea $pcOff $nextOff 10 $k .x11 $rt _ _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp) rfl
      (by simp [$hx11:term]) rfl rfl ?_;
   intro _))

private theorem zext64_trunc32 (x : BitVec 32) : (x.zeroExtend 64).truncate 32 = x := by bv_bits

set_option maxRecDepth 8000 in
private theorem seg5_inner_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (ea : BitVec 64) (evOut0 odOut0 vFirst evOut1 odOut1 vSecond : BitVec 128)
    (Rest : SepProp)
    (hpc : s.pc = b + offSeg5SerStore) (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = ea)
    (hx12 : s.readReg64 .x12 = (((lane16 odOut0 6).zeroExtend 32) <<< 3).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = (((lane16 odOut1 6).zeroExtend 32) <<< 3).zeroExtend 64)
    (hv5 : s.readVReg128 5#5 = vFirst) (hv6 : s.readVReg128 6#5 = vSecond)
    (hd5 : vFirst = simdTrn1_8h evOut0 odOut0 &&& dup8x16 0x001f#16)
    (hd6 : vSecond = simdTrn1_8h evOut1 odOut1 &&& dup8x16 0x001f#16)
    (hm5 : ∀ j : Fin 8, lane16 vFirst j &&& 0x001f#16 = lane16 vFirst j)
    (hm6 : ∀ j : Fin 8, lane16 vSecond j &&& 0x001f#16 = lane16 vSecond j) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 40656) s
      (memRegion ea 10 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        s2.readReg64 .x8 = s.readReg64 .x8 ∧ s2.readReg64 .x9 = s.readReg64 .x9 ∧
        s2.readReg64 .x10 = s.readReg64 .x10 ∧ s2.readReg64 .fp = s.readReg64 .fp ∧
        s2.readVReg128 0#5 = s.readVReg128 0#5 ∧ s2.readVReg128 1#5 = s.readVReg128 1#5 ∧
        s2.readVReg128 2#5 = s.readVReg128 2#5 ∧ s2.readVReg128 3#5 = s.readVReg128 3#5 ∧
        s2.readVReg128 4#5 = s.readVReg128 4#5 ∧
        (P2 ⊢ (ea ↦ₛ neonSerialize5Bytes vFirst vSecond) ∗ Rest)) := by
  subst hbase
  apply sepWP_elim_byteRange 10 (by decide); intro f0
  wp_steps 18; s5_strb ea hx11 hrun 40536 40540 4 .x12
  wp_steps 11; s5_strb ea hx11 hrun 40584 40588 0 .x15
  wp_steps 2;  s5_strb ea hx11 hrun 40596 40600 7 .x12
  wp_steps 7
  s5_strb ea hx11 hrun 40628 40632 2 .x19; s5_strb ea hx11 hrun 40632 40636 5 .x2
  s5_strb ea hx11 hrun 40636 40640 3 .x16; s5_strb ea hx11 hrun 40640 40644 8 .x15
  s5_strb ea hx11 hrun 40644 40648 1 .x14; s5_strb ea hx11 hrun 40648 40652 6 .x12
  s5_strb ea hx11 hrun 40652 40656 9 .x13
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp [State.spAligned], by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, ?_⟩
  rw [byteRangeMem_split5, byteRangeMem5_eq_cells, byteRangeMem5_eq_cells]
  simp only [arm64_norm, Function.update, Nat.reduceEqDiff,
    trunc32_zext64_shl, zext64_trunc32, ← hd5, ← hd6]
  rw [ser5_b0 _ _ (hm5 0) (hm5 1), ser5_b0 _ _ (hm6 0) (hm6 1),
      ser5_b1 _ _ _ (hm5 1) (hm5 2), ser5_b1 _ _ _ (hm6 1) (hm6 2),
      ser5_b2 _ _ (hm5 3) (hm5 4), ser5_b2 _ _ (hm6 3) (hm6 4),
      ser5_b3 _ _ _ (hm5 4) (hm5 5) (hm5 6), ser5_b3 _ _ _ (hm6 4) (hm6 5) (hm6 6),
      ser5_b4 evOut0 odOut0 vFirst hd5, ser5_b4 evOut1 odOut1 vSecond hd6]
  rw [← cells10_eq_neonSerialize5Bytes, ← cells5_eq_neonSerialize5Half ea vFirst,
      ← cells5_eq_neonSerialize5Half (ea + 5#64) vSecond]
  sep_frame

private theorem seg5_inner_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (v : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5SerLoop) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = sp + BitVec.ofNat 64 (30912 + 32 * c))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c))
    (hx10 : s.readReg64 .x10 = sp + 23104#64)
    (hv0 : s.readVReg128 0#5 = c31Vec) (hv1 : s.readVReg128 1#5 = c3329Vec)
    (hv2 : s.readVReg128 2#5 = c2097120Vec) (hv3 : s.readVReg128 3#5 = c1664Vec)
    (hv4 : s.readVReg128 4#5 = c10321340Vec) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if c + 1 < 16 then b + offSeg5SerLoop else b + offSeg5Tail) s
      (PolyMem (sp + 30896#64) (polyVecNat v) ∗
        memRegion (sp + BitVec.ofNat 64 (24512 + 10 * c)) 10 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = sp + BitVec.ofNat 64 (30912 + 32 * (c + 1)) ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * (c + 1)) ∧
        sf.readReg64 .x10 = sp + 23104#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = c31Vec ∧ sf.readVReg128 1#5 = c3329Vec ∧
        sf.readVReg128 2#5 = c2097120Vec ∧ sf.readVReg128 3#5 = c1664Vec ∧
        sf.readVReg128 4#5 = c10321340Vec ∧
        (Pf ⊢ PolyMem (sp + 30896#64) (polyVecNat v) ∗
          ((sp + BitVec.ofNat 64 (24512 + 10 * c)) ↦ₛ ser5Chunk v c) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro
    (seg5_inner_simd hb hbase s sp hc v _ hpc hrun hsp hx8 hx9 hx10 hv0 hv1 hv2 hv3 hv4) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hx11_1, hfp1, hx12_1, hx13_1,
      hv5_1, hv6_1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (SepWP.weaken_pre
      (show PolyMem (sp + 30896#64) (polyVecNat v) ∗ (memRegion _ 10 ∗ Rest) ⊢
          memRegion _ 10 ∗ (PolyMem (sp + 30896#64) (polyVecNat v) ∗ Rest) by sep_frame)
      (seg5_inner_store hb hbase s1 _
        (compress5EvOut (polyVecNat v (2 * c))) (compress5OdOut (polyVecNat v (2 * c))) _
        (compress5EvOut (polyVecNat v (2 * c + 1))) (compress5OdOut (polyVecNat v (2 * c + 1))) _ _
        hpc1 hrun1 hx11_1 hx12_1 hx13_1 hv5_1 hv6_1
        (compress5_trn1_eq _).symm (compress5_trn1_eq _).symm
        (fun j => lane16_neonCompress8h_5_mask _ j)
        (fun j => lane16_neonCompress8h_5_mask _ j))) ?_
  rintro s2 P2 hpc2 hrun2 _ _
    ⟨hsp2, hspA2, hpst2, hx8_2, hx9_2, hx10_2, hfp2, hv0_2, hv1_2, hv2_2, hv3_2, hv4_2, hP2⟩
  subst hbase
  have hspA2' : s2.spAligned = true := hspA2.trans (hspA1.trans hspA)
  by_cases hlt : c + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have htaken : ConditionHolds .NE s2.pstate = true := by
      rw [hpst2, hpst1, conditionHolds_ne_subsPState64]
      rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
      all_goals decide
    refine step_bCond_taken (dst := blkPl07.base + offSeg5SerLoop)
      hpc2 hrun2 (by wp_norm_lhs) htaken (by clear * -; dsimp [offSeg5SerLoop]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2, hsp1], spAligned_of_sp_eq hspA2' (hsp2.trans hsp1) (by simp [hsp2, hsp1]),
        by simp [hx8_2, hx8_1], by simp [hx9_2, hx9_1], by simp [hx10_2, hx10_1],
        by simp [hfp2, hfp1],
        by simp [hv0_2, hv0_1], by simp [hv1_2, hv1_1], by simp [hv2_2, hv2_1],
        by simp [hv3_2, hv3_1], by simp [hv4_2, hv4_1],
        Entails.trans hP2 (by dsimp [ser5Chunk]; sep_frame)⟩
  · simp only [hlt, ↓reduceIte]
    have hc15 : c = 15 := by omega
    subst hc15
    have hnot : ConditionHolds .NE s2.pstate = false := by
      rw [hpst2, hpst1, conditionHolds_ne_subsPState64]; decide
    refine step_bCond_not_taken (dst := blkPl07.base + offSeg5Tail)
      hpc2 hrun2 (by wp_norm_lhs) hnot (by clear * -; dsimp [offSeg5Tail]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2, hsp1], spAligned_of_sp_eq hspA2' (hsp2.trans hsp1) (by simp [hsp2, hsp1]),
        by simp [hx8_2, hx8_1], by simp [hx9_2, hx9_1], by simp [hx10_2, hx10_1],
        by simp [hfp2, hfp1],
        by simp [hv0_2, hv0_1], by simp [hv1_2, hv1_1], by simp [hv2_2, hv2_1],
        by simp [hv3_2, hv3_1], by simp [hv4_2, hv4_1],
        Entails.trans hP2 (by dsimp [ser5Chunk]; sep_frame)⟩

private theorem seg5_inner_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp : BitVec 64) (v : Poly16) :
    ∀ (rem c : Nat), c + rem = 15 → ∀ (s : State) (Rest : SepProp),
      s.pc = b + offSeg5SerLoop → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = sp + BitVec.ofNat 64 (30912 + 32 * c) →
      s.readReg64 .x9 = BitVec.ofNat 64 (1408 + 10 * c) →
      s.readReg64 .x10 = sp + 23104#64 →
      s.readVReg128 0#5 = c31Vec → s.readVReg128 1#5 = c3329Vec →
      s.readVReg128 2#5 = c2097120Vec → s.readVReg128 3#5 = c1664Vec →
      s.readVReg128 4#5 = c10321340Vec →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Tail) s
        (PolyMem (sp + 30896#64) (polyVecNat v) ∗
          ((sp + 24512#64) ↦ₛ ser5Prefix v c) ∗
          memRegion (sp + BitVec.ofNat 64 (24512 + 10 * c)) (10 * (16 - c)) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          (Pf ⊢ PolyMem (sp + 30896#64) (polyVecNat v) ∗
            ((sp + 24512#64) ↦ₛ neonCompressSerialize5Poly v) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro c hcrem s Rest hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hv0 hv1 hv2 hv3 hv4
    have hc15 : c = 15 := by omega
    subst hc15
    have hiter := seg5_inner_iter hb hbase s sp (by decide : 15 < 16) v
      (((sp + 24512#64) ↦ₛ ser5Prefix v 15) ∗ Rest)
      hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hv0 hv1 hv2 hv3 hv4
    simp only [show ¬ (15 + 1 < 16) by decide, ↓reduceIte] at hiter
    refine SepWP.weaken_pre (by show _ ⊢ _ ∗ memRegion _ 10 ∗ _; sep_frame)
      (SepWP.mono hiter ?_)
    rintro sf Pf _ _ ⟨hsp', hspA', _, _, _, hfp', _, _, _, _, _, hPf⟩
    refine ⟨hsp', hspA', hfp', Entails.trans hPf ?_⟩
    have hjoin := ser5_prefix_append_chunk (sp + 24512#64) v 15
    rw [show (sp + 24512#64) + BitVec.ofNat 64 (10 * 15) = sp + BitVec.ofNat 64 (24512 + 10 * 15) by
      clear * -; bv_omega, ser5Prefix_sixteen] at hjoin
    rw [← hjoin]; sep_frame
  | succ rem ih =>
    intro c hcrem s Rest hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hv0 hv1 hv2 hv3 hv4
    have hc16 : c < 16 := by omega
    have hlt : c + 1 < 16 := by omega
    have hmsplit : memRegion (sp + BitVec.ofNat 64 (24512 + 10 * c)) (10 * (16 - c)) =
        memRegion (sp + BitVec.ofNat 64 (24512 + 10 * c)) 10 ∗
          memRegion (sp + BitVec.ofNat 64 (24512 + 10 * (c + 1))) (10 * (16 - (c + 1))) := by
      rw [show 10 * (16 - c) = 10 + 10 * (16 - (c + 1)) by omega]
      exact memRegion_split'
        (b := sp + BitVec.ofNat 64 (24512 + 10 * c))
        (b' := sp + BitVec.ofNat 64 (24512 + 10 * (c + 1)))
        (n := 10) (k := (10 * (16 - (c + 1)) : Nat)) rfl
        (by clear * - hc16; bv_omega)
        (by change 10 + 10 * (16 - (c + 1)) ≤ 0x10000000000000000; omega)
    rw [hmsplit]
    have hiter := seg5_inner_iter hb hbase s sp hc16 v
      (((sp + 24512#64) ↦ₛ ser5Prefix v c) ∗
        memRegion (sp + BitVec.ofNat 64 (24512 + 10 * (c + 1))) (10 * (16 - (c + 1))) ∗ Rest)
      hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hv0 hv1 hv2 hv3 hv4
    simp only [hlt, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro (SepWP.weaken_pre (by sep_frame) hiter) ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hfp1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hP1⟩
    have hjoin := ser5_prefix_append_chunk (sp + 24512#64) v c
    rw [show (sp + 24512#64) + BitVec.ofNat 64 (10 * c) = sp + BitVec.ofNat 64 (24512 + 10 * c) by
      clear * - hc16; bv_omega] at hjoin
    refine SepWP.weaken_pre (Entails.trans hP1 (by rw [← hjoin]; sep_frame))
      (SepWP.mono (ih (c + 1) (by omega) s1 Rest
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hv0_1 hv1_1 hv2_1 hv3_1 hv4_1) ?_)
    rintro sf Pf _ _ ⟨hsp', hspA', hfp', hPf⟩
    exact ⟨hsp', hspA', hfp'.trans hfp1, hPf⟩

theorem seg5_compress_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp fpVal : BitVec 64) (v : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Compress) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Tail) s
      (PolyMem (sp + 30896#64) (polyVecNat v) ∗ memRegion (sp + 24512#64) 160 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        (Pf ⊢ PolyMem (sp + 30896#64) (polyVecNat v) ∗
          ((sp + 24512#64) ↦ₛ neonCompressSerialize5Poly v) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg5_ser_header hb hbase s sp _ hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx8_1, hx9_1, hx10_1, hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, rfl⟩
  have hspA1' : s1.spAligned = true := hspA1.trans hspA
  have hloop := seg5_inner_loop hb hbase sp v 15 0 rfl s1 Rest
    hpc1 hrun1 hsp1 hspA1' hcl1 hro1 hx8_1 hx9_1 hx10_1 hv0_1 hv1_1 hv2_1 hv3_1 hv4_1
  simp only [show ser5Prefix v 0 = [] from rfl, pointsToBytes_nil, emp_sepConj,
    show 10 * (16 - 0) = 160 by decide,
    show sp + BitVec.ofNat 64 (24512 + 10 * 0) = sp + 24512#64 by clear * -; bv_omega] at hloop
  refine SepWP.mono hloop ?_
  rintro sf Pf _ _ ⟨hsp', hspA', hfp', hPf⟩
  exact ⟨hsp', hspA', hfp'.trans (hfp1.trans hfp), hPf⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress
