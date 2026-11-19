/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 Row Epilogue

Proves `seg5_epi_ok` (`+0x710c → +0x4158`), compacting the four `544`-byte `SampleNTT` lanes
into `[sp + 4176 .. sp + 6224)` on `cfgD06` and copying all four `512`-byte polynomials into
`[sp + 14432 + 2048 * row .. + 2048)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 bytesToPoly16 sampleNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (packLane64 unpackLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  pointsTo64_eq_unpackLane64 readLE_8_eq_packLane64 unpack64_eq_unpackLane64 unpackLane64_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  packHalfwordsLE packHalfwordsLE_length sampleNttClassical)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyMem_bytesToPoly16 polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KState KZFlag evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem BTreeMemFrom BTreeMemFrom_eq_bytes BTreeMem_entails_memRegion BTreeMem_eq_bytes
  KSpatial KStateMatches SepWP.of_memRegion_btreeMem btreeBytesFrom btreeBytesFrom_congr
  btreeBytesFrom_length btreeBytesFrom_split bytesToBTree9 evalMemTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get vreg128_repack)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep eval_checked_gpr eval_checked_memA exprVarsOk rowSeed specEnvSteps)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  multiLaneSampled4_entails_memRegion32 multiLaneSlots4_eq_btreeMem272 slotBytes4
  slotBytes4_drop_take slotBytes4_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast (
  optKZFlagBeq optKZFlagBeq_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowCalleeGprs06 RowExitState06 blk28_memcpy_06 cfgD06 cfgD06_valid)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06 (
  runAndCheckKProg06 sepWP_of_runAndCheckKProg06)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x7528 → 0x76a8]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## 1. `BTreeMem` Slot-Compaction Byte Bridges -/

private theorem btreeMem_zero (ptr : BitVec 64) (t : BTree (BitVec 64) 9) :
    BTreeMem ptr 0 t = emp := rfl

private theorem unpackLane64_packLane64_zero {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpackLane64 (packLane64 bs 0) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try solve | cases h
  rw [← unpack64_eq_unpackLane64, ← readLE_8_eq_packLane64, ← ByteSlice.pack64_eq_readLE_8]
  exact unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7

private theorem packLane64_drop (bs : List (BitVec 8)) (d off : Nat) :
    packLane64 (bs.drop d) off = packLane64 bs (d + off) := by
  unfold packLane64
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

private theorem packLane64_take8 (bs : List (BitVec 8)) :
    packLane64 (bs.take 8) 0 = packLane64 bs 0 := by
  unfold packLane64
  simp [List.getD_eq_getElem?_getD]

private theorem btreeBytesFrom_bytesToBTree9_prefix :
    ∀ (cnt start : Nat) {bs : List (BitVec 8)},
      8 * (start + cnt) ≤ bs.length →
      start + cnt ≤ 512 →
      btreeBytesFrom start cnt (bytesToBTree9 bs) = (bs.drop (8 * start)).take (8 * cnt)
  | 0, start, bs, _, _ => by simp [btreeBytesFrom]
  | c + 1, start, bs, h, h512 => by
      have hhd : (bytesToBTree9 bs).get start = packLane64 bs (8 * start) :=
        BTree.get_ofFn 9 _ start (by omega)
      have h8 : ((bs.drop (8 * start)).take 8).length = 8 := by
        simp [List.length_take_of_le (by simp; omega : 8 ≤ (bs.drop (8 * start)).length)]
      have hu : unpackLane64 (packLane64 bs (8 * start)) = (bs.drop (8 * start)).take 8 := by
        have hp : packLane64 bs (8 * start) = packLane64 ((bs.drop (8 * start)).take 8) 0 := by
          rw [packLane64_take8, packLane64_drop, Nat.add_zero]
        rw [hp, unpackLane64_packLane64_zero h8]
      have hrec := btreeBytesFrom_bytesToBTree9_prefix c (start + 1) (bs := bs) (by omega) (by omega)
      simp only [btreeBytesFrom, hhd, hu, hrec]
      have hd : bs.drop (8 * (start + 1)) = (bs.drop (8 * start)).drop 8 := by
        rw [List.drop_drop]; exact congrArg (fun n => bs.drop n) (by omega)
      rw [hd, show 8 * (c + 1) = 8 + 8 * c by omega, List.take_add]

private theorem btreeBytesFrom_congr_shift :
    ∀ (cnt s1 s2 : Nat) {t1 t2 : BTree (BitVec 64) 9},
      (∀ k, k < cnt → t1.get (s1 + k) = t2.get (s2 + k)) →
      btreeBytesFrom s1 cnt t1 = btreeBytesFrom s2 cnt t2
  | 0, _, _, _, _, _ => rfl
  | c + 1, s1, s2, t1, t2, h => by
      simp only [btreeBytesFrom]
      have h0 : t1.get s1 = t2.get s2 := by simpa using h 0 (Nat.zero_lt_succ c)
      rw [h0, btreeBytesFrom_congr_shift c (s1 + 1) (s2 + 1) fun k hk => by
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) (Nat.succ_lt_succ hk)]

private theorem btreeMemFrom_split (ptr : BitVec 64) (start a b : Nat) (t : BTree (BitVec 64) 9) :
    BTreeMemFrom ptr start (a + b) t =
      BTreeMemFrom ptr start a t ∗
        BTreeMemFrom (ptr + BitVec.ofNat 64 (8 * a)) (start + a) b t := by
  rw [BTreeMemFrom_eq_bytes, BTreeMemFrom_eq_bytes, BTreeMemFrom_eq_bytes,
    btreeBytesFrom_split, pointsToBytes_append, btreeBytesFrom_length]

private theorem btreeMemFrom_entails_memRegion (ptr : BitVec 64) (start cnt : Nat)
    (t : BTree (BitVec 64) 9) :
    BTreeMemFrom ptr start cnt t ⊢ memRegion ptr (8 * cnt) := by
  rw [BTreeMemFrom_eq_bytes]
  have hp := pointsToBytes_entails_memRegion ptr (btreeBytesFrom start cnt t)
  rwa [btreeBytesFrom_length] at hp

private theorem btreeMem272_compacted_split06 (sp : BitVec 64) {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (h3 : (hws 3).length = 272)
    {tOut : BTree (BitVec 64) 9}
    (hcomp : ∀ c, c < 4 → ∀ k, k < 64 →
      tOut.get (2 + 64 * c + k) = (bytesToBTree9 (slotBytes4 hws)).get (68 * c + k)) :
    BTreeMem (sp + 4160#64) 272 tOut ⊢
      memRegion (sp + 4160#64) 16 ∗
      ((sp + 4176#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
      ((sp + 4688#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
      ((sp + 5200#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
      ((sp + 5712#64) ↦ₛ (packHalfwordsLE (hws 3)).take 512) ∗
      ((sp + 6224#64) ↦₆₄ tOut.get 258) ∗
      memRegion (sp + 6232#64) 104 := by
  have hslen := slotBytes4_length h0 h1 h2 h3
  have hcol : ∀ c, c < 4 →
      btreeBytesFrom (2 + 64 * c) 64 tOut = (packHalfwordsLE (hws c)).take 512 := fun c hc => by
    rw [btreeBytesFrom_congr_shift 64 (2 + 64 * c) (68 * c) (hcomp c hc),
      btreeBytesFrom_bytesToBTree9_prefix 64 (68 * c) (by omega) (by omega),
      show 8 * (68 * c) = 544 * c by omega, show 8 * 64 = 512 from rfl,
      slotBytes4_drop_take h0 h1 h2 h3 hc]
  unfold BTreeMem
  rw [show (272 : Nat) = 2 + (64 + (64 + (64 + (64 + 14)))) from rfl,
    btreeMemFrom_split (sp + 4160#64) 0 2 _,
    btreeMemFrom_split _ 2 64 _,
    btreeMemFrom_split _ 66 64 _,
    btreeMemFrom_split _ 130 64 _,
    btreeMemFrom_split _ 194 64 _,
    show (sp + 4160#64) + BitVec.ofNat 64 (8 * 2) = sp + 4176#64 by bv_omega,
    show (sp + 4176#64) + BitVec.ofNat 64 (8 * 64) = sp + 4688#64 by bv_omega,
    show (sp + 4688#64) + BitVec.ofNat 64 (8 * 64) = sp + 5200#64 by bv_omega,
    show (sp + 5200#64) + BitVec.ofNat 64 (8 * 64) = sp + 5712#64 by bv_omega,
    show (sp + 5712#64) + BitVec.ofNat 64 (8 * 64) = sp + 6224#64 by bv_omega,
    BTreeMemFrom_eq_bytes (sp + 4176#64) 2 64 tOut, hcol 0 (by decide),
    BTreeMemFrom_eq_bytes (sp + 4688#64) 66 64 tOut, hcol 1 (by decide),
    BTreeMemFrom_eq_bytes (sp + 5200#64) 130 64 tOut, hcol 2 (by decide),
    BTreeMemFrom_eq_bytes (sp + 5712#64) 194 64 tOut, hcol 3 (by decide)]
  change BTreeMemFrom (sp + 4160#64) 0 2 tOut ∗
    (((sp + 4176#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
     (((sp + 4688#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
      (((sp + 5200#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
       (((sp + 5712#64) ↦ₛ (packHalfwordsLE (hws 3)).take 512) ∗
        (((sp + 6224#64) ↦₆₄ tOut.get 258) ∗ BTreeMemFrom (sp + 6224#64 + 8#64) 259 13 tOut))))) ⊢ _
  rw [show sp + 6224#64 + 8#64 = sp + 6232#64 by bv_omega]
  have h16 := btreeMemFrom_entails_memRegion (sp + 4160#64) 0 2 tOut
  have h104 := btreeMemFrom_entails_memRegion (sp + 6232#64) 259 13 tOut
  exact Entails.trans (sepConj_mono h16
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right h104)))))) (by sep_frame)

/-! ## 2. Symbolic Compaction `+0x710c → +0x7528` on `cfgD06` (`seg5_sliceD_ok`) -/

private def stD06 : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs := BTree.ofFn 5 (fun g => .var (64 + g))
    memA := BTree.ofFn 9 (fun i => .var (200 + i))
    memB := BTree.ofFn 9 (fun _ => .const64 0#64)
    zFlag := none }

private def stepsD06 : List KProgStep := [.range 7235 263]

private def chkD06 (ok : Nat → Bool) (st : KState) : Bool :=
  optKZFlagBeq st.zFlag (some (.constBool false)) &&
  (st.gprs.get 8).beq (.const64 4#64) &&
  (st.gprs.get 25).beq (.const64 4#64) &&
  (st.gprs.get 24).beq (.const64 0#64) &&
  ([1, 19, 21, 22, 23, 26, 28, 29].all fun g =>
    (st.gprs.get g).beq (.var (64 + g)) && ok (64 + g)) &&
  ((List.range 4).all fun c =>
    (List.range 64).all fun k =>
      (st.memA.get (2 + 64 * c + k)).beq (.var (200 + 68 * c + k)) &&
      ok (200 + 68 * c + k))

set_option maxRecDepth 200000 in
private theorem cert_sliceD06 :
    runAndCheckKProg06 cfgD06 7235 7498 7235 7498 1000 stepsD06 stD06 chkD06 = true := by
  rfl_kernel

private def envD06 (sp rcBase : BitVec 64) (s : State) (tSlots : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp, rcBase := rcBase, rLoop := 0
    vars := fun id =>
      if id < 64 then
        let v := s.readVReg128 (BitVec.ofNat 5 (id / 2))
        if id % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id < 96 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 64)))
      else if id < 712 then tSlots.get (id - 200)
      else 0#64 }

private theorem stD06_matches {sp rcBase : BitVec 64} {s : State} {tSlots : BTree (BitVec 64) 9}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    KStateMatches (envD06 sp rcBase s tSlots) stD06 s ∧
      evalMemTree (envD06 sp rcBase s tSlots) stD06.memA = tSlots := by
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_⟩
  · intro r
    have hr : r.toNat < 32 := r.isLt
    have hget : stD06.vregs.get r.toNat = (.var (2 * r.toNat), .var (2 * r.toNat + 1)) := by
      dsimp only [stD06]; exact BTree.get_ofFn 5 _ r.toNat hr
    rw [hget]
    have hlo : evalKExpr (envD06 sp rcBase s tSlots) (.var (2 * r.toNat)) =
        (s.readVReg128 r).truncate 64 := by
      simp [evalKExpr, envD06, show 2 * r.toNat < 64 by omega,
        show (2 * r.toNat) / 2 = r.toNat by omega]
    have hhi : evalKExpr (envD06 sp rcBase s tSlots) (.var (2 * r.toNat + 1)) =
        ((s.readVReg128 r) >>> 64).truncate 64 := by
      simp [evalKExpr, envD06, show 2 * r.toNat + 1 < 64 by omega,
        show (2 * r.toNat + 1) / 2 = r.toNat by omega,
        show (2 * r.toNat + 1) % 2 = 1 by omega]
    rw [hlo, hhi, vreg128_repack]
  · intro r hr
    have hlt : r.toNat < 32 := r.isLt
    have hget : stD06.gprs.get r.toNat = .var (64 + r.toNat) := by
      dsimp only [stD06]; exact BTree.get_ofFn 5 _ r.toNat hlt
    rw [hget]
    simp [evalKExpr, envD06, show ¬(64 + r.toNat < 64) by omega, show 64 + r.toNat < 96 by omega]
  · apply btree_ext_get
    intro i hi
    have hi512 : i < 512 := by simpa using hi
    simp [evalMemTree, BTree.get_map, stD06, BTree.get_ofFn 9 _ i hi512, evalKExpr, envD06,
      show ¬(200 + i < 64) by omega, show ¬(200 + i < 96) by omega,
      show 200 + i < 712 by omega]

@[expose] def EpiPreservedGprs06 (sp rcBase fpVal : BitVec 64) (row : Nat) (s : State) : Prop :=
  s.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  s.readReg64 .x19 = 544#64 ∧
  s.readReg64 .x22 = sp + 4160#64 ∧
  s.readReg64 .x23 = sp + 26320#64 ∧
  s.readReg64 .x26 = sp + 28632#64 ∧
  s.readReg64 .x28 = rcBase ∧
  s.readReg64 .fp = fpVal

set_option maxRecDepth 20000 in
private theorem seg5_sliceD_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64} {row : Nat}
    {hws : Nat → List (BitVec 16)}
    (h0 : (hws 0).length = 272) (h1 : (hws 1).length = 272)
    (h2 : (hws 2).length = 272) (h3 : (hws 3).length = 272)
    {s0 : State} {F : SepProp}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * 7235)) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hgprs0 : RowCalleeGprs06 sp rcBase fpVal row s0)
    (hx1_0 : s0.readReg64 .x1 = BitVec.ofNat 64 (row + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 7498)) s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ MultiLaneSlots (sp + 4160#64) 544 4 hws ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        ConditionHolds .EQ sf.pstate = false ∧
        sf.readReg64 .x8 = 4#64 ∧ sf.readReg64 .x21 = BitVec.ofNat 64 row ∧
        sf.readReg64 .x24 = 0#64 ∧ sf.readReg64 .x25 = 4#64 ∧
        EpiPreservedGprs06 sp rcBase fpVal row sf ∧
        ∃ v6224 : BitVec 64,
          Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            memRegion (sp + 4160#64) 16 ∗
            ((sp + 4176#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
            ((sp + 4688#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
            ((sp + 5200#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
            ((sp + 5712#64) ↦ₛ (packHalfwordsLE (hws 3)).take 512) ∗
            ((sp + 6224#64) ↦₆₄ v6224) ∗
            memRegion (sp + 6232#64) 104 ∗ F) := by
  let tSlots := bytesToBTree9 (slotBytes4 hws)
  let env0 := envD06 sp rcBase s0 tSlots
  obtain ⟨hm0, hmemEq0⟩ := stD06_matches (rcBase := rcBase) (tSlots := tSlots) hsp0 hspA0
  have hspEq : ((rcBase ↦ᵣ mlkemData01Bytes) ∗ MultiLaneSlots (sp + 4160#64) 544 4 hws ∗ F) =
      KSpatial cfgD06 env0 stD06 F := by
    rw [multiLaneSlots4_eq_btreeMem272 (sp + 4160#64) h0 h1 h2 h3]
    simp only [KSpatial, cfgD06, btreeMem_zero, emp_sepConj]
    rw [hmemEq0]
    rfl
  rw [hspEq]
  refine sepWP_of_runAndCheckKProg06 cfgD06_valid (env0 := env0) (show 0 < 24 by decide)
    cert_sliceD06 hm0 hpc0 hrun0 ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _hrlF heval hmF hchk
  simp only [chkD06, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hz_chk, hx8_chk⟩, hx25_chk⟩, hx24_chk⟩, hgpr_chk⟩, hmem_chk⟩
  have hspecEq : specEnvSteps env0 stepsD06 = env0 := rfl
  have hzEq : stEnd.zFlag = some (.constBool false) := by
    rw [optKZFlagBeq_eq] at hz_chk; exact eq_of_beq hz_chk
  have hcond : ConditionHolds .EQ sf.pstate = false := by
    have hz := hmF.hzflag; rw [hzEq] at hz; exact hz.1
  have hx8 := eval_checked_gpr hmF heval 8#5 (by decide) (.const64 4#64) hx8_chk rfl
  have hx25 := eval_checked_gpr hmF heval 25#5 (by decide) (.const64 4#64) hx25_chk rfl
  have hx24 := eval_checked_gpr hmF heval 24#5 (by decide) (.const64 0#64) hx24_chk rfl
  have hgprPres : ∀ g ∈ ([1, 19, 21, 22, 23, 26, 28, 29] : List Nat),
      (h31 : BitVec.ofNat 5 g ≠ 31#5) →
      sf.readReg64 (.gpr (BitVec.ofNat 5 g)) = s0.readReg64 (.gpr (BitVec.ofNat 5 g)) := by
    intro g hg h31
    have h1 := List.all_eq_true.mp hgpr_chk g hg
    simp only [Bool.and_eq_true] at h1
    rcases h1 with ⟨heq, hok⟩
    have hlt : g < 32 := by
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      rcases List.mem_cons.mp hg with rfl | hg; · decide
      cases hg
    have hv := eval_checked_gpr hmF heval (BitVec.ofNat 5 g) h31 (.var (64 + g))
      (by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using heq) hok
    rw [hspecEq] at hv
    simpa [evalKExpr, env0, envD06, show ¬(64 + g < 64) by omega,
      show 64 + g < 96 by omega] using hv
  rcases hgprs0 with ⟨g19, _, g21, g22, g23, _, _, g26, g28, gfp⟩
  have hcomp : ∀ c, c < 4 → ∀ k, k < 64 →
      (evalMemTree envFinal stEnd.memA).get (2 + 64 * c + k) = tSlots.get (68 * c + k) := by
    intro c hc k hk
    have hc1 := List.all_eq_true.mp hmem_chk c (List.mem_range.mpr hc)
    have hc2 := List.all_eq_true.mp hc1 k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at hc2
    rcases hc2 with ⟨heq, hok⟩
    have hv := eval_checked_memA heval (2 + 64 * c + k) (.var (200 + 68 * c + k)) heq hok
    rw [hspecEq] at hv
    simpa [evalKExpr, env0, envD06, show 200 + 68 * c + k - 200 = 68 * c + k by omega,
      show ¬(200 + 68 * c + k < 64) by omega,
      show ¬(200 + 68 * c + k < 96) by omega, show 200 + 68 * c + k < 712 by omega] using hv
  refine SepWP.done hpcF hrunF ⟨hmF.hsp.trans hspF, hmF.hsp_al, hcond,
    by simpa [Reg.x8, evalKExpr] using hx8,
    (hgprPres 21 (by simp) (by decide)).trans g21,
    by simpa [Reg.x24, evalKExpr] using hx24,
    by simpa [Reg.x25, evalKExpr] using hx25,
    ⟨(hgprPres 1 (by simp) (by decide)).trans hx1_0,
     (hgprPres 19 (by simp) (by decide)).trans g19,
     (hgprPres 22 (by simp) (by decide)).trans g22,
     (hgprPres 23 (by simp) (by decide)).trans g23,
     (hgprPres 26 (by simp) (by decide)).trans g26,
     (hgprPres 28 (by simp) (by decide)).trans g28,
     (hgprPres 29 (by simp) (by decide)).trans gfp⟩,
    (evalMemTree envFinal stEnd.memA).get 258, ?_⟩
  simp only [KSpatial, cfgD06, hspF, hrcF, btreeMem_zero, emp_sepConj]
  change ((rcBase ↦ᵣ mlkemData01Bytes) ∗
    (BTreeMem (sp + 4160#64) 272 (evalMemTree envFinal stEnd.memA) ∗ F)) ⊢ _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left
    (btreeMem272_compacted_split06 sp h0 h1 h2 h3 hcomp))) (by sep_frame)

/-! ## 3. Row Polynomial Output & `3 × memcpy` Column Helper -/

@[expose] noncomputable def RowPolyOut06 (sp : BitVec 64) (rho : List (BitVec 8)) (row : Nat) : SepProp :=
  PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row))
    (polyVecNat ((sampleNtt (rowSeed rho row 0)).map (BitVec.ofNat 16))) ∗
  PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512))
    (polyVecNat ((sampleNtt (rowSeed rho row 1)).map (BitVec.ofNat 16))) ∗
  PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024))
    (polyVecNat ((sampleNtt (rowSeed rho row 2)).map (BitVec.ofNat 16))) ∗
  PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536))
    (polyVecNat ((sampleNtt (rowSeed rho row 3)).map (BitVec.ofNat 16)))

private def CopyGprs06 (sp rcBase fpVal x20Val x21Val : BitVec 64) (row : Nat) (s : State) : Prop :=
  s.sp = sp ∧
  s.spAligned = true ∧
  s.readReg64 .x19 = 544#64 ∧
  s.readReg64 .x20 = x20Val ∧
  s.readReg64 .x21 = x21Val ∧
  s.readReg64 .x22 = sp + 4160#64 ∧
  s.readReg64 .x23 = sp + 26320#64 ∧
  s.readReg64 .x24 = 0#64 ∧
  s.readReg64 .x25 = 4#64 ∧
  s.readReg64 .x26 = sp + 28632#64 ∧
  s.readReg64 .x27 = BitVec.ofNat 64 (row + 1) ∧
  s.readReg64 .x28 = rcBase ∧
  s.readReg64 .fp = fpVal

private theorem sampleNttClassical_eq_sampleNtt (seed : List (BitVec 8)) :
    sampleNttClassical seed = sampleNtt seed := rfl

attribute [local irreducible] blkPC06 sampleNtt sampleNttClassical bytesToPoly16 polyVecNat

@[simp, arm64_norm, wp_norm] private abbrev off7528 : BitVec 64 := 29992#64
@[simp, arm64_norm, wp_norm] private abbrev off7558 : BitVec 64 := 30040#64
@[simp, arm64_norm, wp_norm] private abbrev off755c : BitVec 64 := 30044#64
@[simp, arm64_norm, wp_norm] private abbrev off7574 : BitVec 64 := 30068#64
@[simp, arm64_norm, wp_norm] private abbrev off758c : BitVec 64 := 30092#64
@[simp, arm64_norm, wp_norm] private abbrev off75b4 : BitVec 64 := 30132#64
@[simp, arm64_norm, wp_norm] private abbrev off75b8 : BitVec 64 := 30136#64
@[simp, arm64_norm, wp_norm] private abbrev off75d0 : BitVec 64 := 30160#64
@[simp, arm64_norm, wp_norm] private abbrev off75e8 : BitVec 64 := 30184#64
@[simp, arm64_norm, wp_norm] private abbrev off7618 : BitVec 64 := 30232#64
@[simp, arm64_norm, wp_norm] private abbrev off761c : BitVec 64 := 30236#64
@[simp, arm64_norm, wp_norm] private abbrev off7634 : BitVec 64 := 30260#64
@[simp, arm64_norm, wp_norm] private abbrev off764c : BitVec 64 := 30284#64
@[simp, arm64_norm, wp_norm] private abbrev off766c : BitVec 64 := 30316#64
@[simp, arm64_norm, wp_norm] private abbrev off7670 : BitVec 64 := 30320#64
@[simp, arm64_norm, wp_norm] private abbrev off7688 : BitVec 64 := 30344#64
@[simp, arm64_norm, wp_norm] private abbrev off76a0 : BitVec 64 := 30368#64
@[simp, arm64_norm, wp_norm] abbrev off4158 : BitVec 64 := 16728#64

private theorem spAligned_of_chk06 {s' : State} {sp : BitVec 64}
    (hsp' : s'.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) :
    s'.spAligned = true := by
  simp only [State.spAligned, hsp']
  exact hchk

set_option linter.unreachableTactic false

local macro "sgpr06 " g:term:arg : tactic =>
  `(tactic| first | (simp; done) | (simp [$g:term]; done) | (simp [$g:term, *]; done))

local macro "prove_col_calls " mid1:term:arg mid2:term:arg x20Val:term:arg
    srcAddr:term:arg x0Call:term:arg dstAddr:term:arg
    sp:term:arg rcBase:term:arg fpVal:term:arg row:term:arg bs:term:arg pad8:term:arg
    hbs:term:arg hpad:term:arg hsp_chk:term:arg hcl1:term:arg hro1:term:arg
    hg1:term:arg s1:term:arg haDst:term:arg Rest:term:arg : tactic => `(tactic| (
  have hlen520 : ($pad8 ++ $bs).length = 520 := by simp [$hpad:term, $hbs:term]
  have hlt512 : ($bs).length < 2 ^ 64 := by rw [$hbs:term]; omega
  have hlt520 : ($pad8 ++ $bs).length < 2 ^ 64 := by rw [hlen520]; omega
  have h520Eq30 : (($sp + 30448#64) ↦ₛ $pad8) ∗ (($sp + 30456#64) ↦ₛ $bs) =
      (($sp + 30448#64) ↦ₛ ($pad8 ++ $bs)) := by
    rw [pointsToBytes_append, $hpad:term,
      show $sp + 30448#64 + BitVec.ofNat 64 8 = $sp + 30456#64 by bv_omega]
  have h520Eq28 : (($sp + 28368#64) ↦ₛ ($pad8 ++ $bs)) =
      (($sp + 28368#64) ↦ₛ $pad8) ∗ (($sp + 28376#64) ↦ₛ $bs) := by
    rw [pointsToBytes_append, $hpad:term,
      show $sp + 28368#64 + BitVec.ofNat 64 8 = $sp + 28376#64 by bv_omega]
  have hcall1 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + $mid1) $s1
      ((($srcAddr) ↦ₛ $bs) ∗ (($sp + 30448#64) ↦ₛ $pad8) ∗ memRegion ($sp + 30456#64) 512 ∗
        memRegion ($sp + 28368#64) 520 ∗ memRegion ($dstAddr) 512 ∗ $Rest)
      (fun s2 P2 =>
        CopyGprs06 $sp $rcBase $fpVal $x20Val ($sp + 14432#64 + BitVec.ofNat 64 (2048 * $row)) $row s2 ∧
        (P2 ⊢ memRegion ($sp + 28368#64) ($pad8 ++ $bs).length ∗
          (($sp + 30448#64) ↦ₛ ($pad8 ++ $bs)) ∗
          (memRegion $srcAddr 512 ∗ memRegion $dstAddr 512 ∗ $Rest))) := by
    rcases ($hg1 : CopyGprs06 _ _ _ _ _ _ _) with
      ⟨hsp, _, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
    refine SepWP.weaken_pre (P' := memRegion ($sp + 30456#64) ($bs).length ∗ ($srcAddr ↦ₛ $bs) ∗
        ((($sp + 30448#64) ↦ₛ $pad8) ∗ memRegion ($sp + 28368#64) 520 ∗
          memRegion $dstAddr 512 ∗ $Rest)) (by rw [$hbs:term]; sep_frame) ?_
    wp_step
    refine seq_codeLoaded_lr $hcl1 ?_
    wp_call (blk28_memcpy_06 blkPl06.base) ($sp + 30456#64, $srcAddr, $bs)
    apply SepWP.done (by assumption) (by assumption); intro _hcl_c1
    refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
      ⟨⟨by sgpr06 hsp, spAligned_of_chk06 (by sgpr06 hsp) $hsp_chk, by sgpr06 g19,
        by sgpr06 g20, by sgpr06 g21, by sgpr06 g22, by sgpr06 g23,
        by sgpr06 g24, by sgpr06 g25, by sgpr06 g26, by sgpr06 g27,
        by sgpr06 g28, by sgpr06 gfp⟩, ?_⟩
    have hsrcM : ($srcAddr ↦ₛ $bs) ⊢ memRegion $srcAddr 512 := by
      have hp := pointsToBytes_entails_memRegion $srcAddr $bs; rwa [$hbs:term] at hp
    rw [hlen520, ← h520Eq30]
    exact entails_sub hsrcM (by sep_frame) (by sep_frame)
  refine sepWP_seq_env $hcl1 $hro1 hcall1 fun s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hg2, hP2⟩ => ?_
  have hcall2 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + $mid2) s2 P2
      (fun s3 P3 =>
        CopyGprs06 $sp $rcBase $fpVal $x20Val ($sp + 14432#64 + BitVec.ofNat 64 (2048 * $row)) $row s3 ∧
        (P3 ⊢ memRegion $x0Call ($bs).length ∗ (($sp + 28376#64) ↦ₛ $bs) ∗
          ((($sp + 28368#64) ↦ₛ $pad8) ∗ (($sp + 30448#64) ↦ₛ $pad8) ∗
            memRegion ($sp + 30456#64) 512 ∗ memRegion $srcAddr 512 ∗ $Rest))) := by
    refine SepWP.weaken_pre hP2 ?_
    rcases hg2 with ⟨hsp2, _, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
    wp_steps 6
    refine seq_codeLoaded_lr hcl2 ?_
    wp_call (blk28_memcpy_06 blkPl06.base) ($sp + 28368#64, $sp + 30448#64, $pad8 ++ $bs)
    apply SepWP.done (by assumption) (by assumption); intro _hcl_c2
    refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
      ⟨⟨by sgpr06 hsp2, spAligned_of_chk06 (by sgpr06 hsp2) $hsp_chk, by sgpr06 g19,
        by sgpr06 g20, by sgpr06 g21, by sgpr06 g22, by sgpr06 g23,
        by sgpr06 g24, by sgpr06 g25, by sgpr06 g26, by sgpr06 g27,
        by sgpr06 g28, by sgpr06 gfp⟩, ?_⟩
    have hm30 : (($sp + 30456#64) ↦ₛ $bs) ⊢ memRegion ($sp + 30456#64) 512 := by
      have hp := pointsToBytes_entails_memRegion ($sp + 30456#64) $bs; rwa [$hbs:term] at hp
    rw [$hbs:term, h520Eq28, ← h520Eq30]; try rw [$haDst:term]
    exact entails_sub hm30 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl2 hro2 hcall2 fun s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hg3, hP3⟩ => ?_
  refine SepWP.weaken_pre hP3 ?_
  rcases hg3 with ⟨hsp3, _, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
  wp_steps 6
  refine seq_codeLoaded_lr hcl3 ?_
  wp_call (blk28_memcpy_06 blkPl06.base) ($x0Call, $sp + 28376#64, $bs)
  apply SepWP.done (by assumption) (by assumption); intro _hcl_c3
  refine SepWP.done (by first | assumption | wp_norm_lhs) ‹_›
    ⟨⟨by sgpr06 hsp3, spAligned_of_chk06 (by sgpr06 hsp3) $hsp_chk, by sgpr06 g19,
      by sgpr06 g20, by sgpr06 g21, by sgpr06 g22, by sgpr06 g23,
      by sgpr06 g24, by sgpr06 g25, by sgpr06 g26, by sgpr06 g27,
      by sgpr06 g28, by sgpr06 gfp⟩, $pad8, $hpad, ?_⟩
  have h520M : (($sp + 28368#64) ↦ₛ $pad8) ∗ (($sp + 28376#64) ↦ₛ $bs) ⊢
      memRegion ($sp + 28368#64) 520 := by
    rw [← h520Eq28]
    have hp := pointsToBytes_entails_memRegion ($sp + 28368#64) ($pad8 ++ $bs); rwa [hlen520] at hp
  try rw [$haDst:term]
  exact entails_sub h520M (by sep_frame) (by sep_frame)))

private theorem dst_row_shl06 {sp : BitVec 64} {row : Nat} (hrow : row < 4) :
    sp + 12288#64 + 2144#64 + (BitVec.ofNat 64 row <<< 11) =
      sp + 14432#64 + BitVec.ofNat 64 (2048 * row) := by
  rcases (by omega : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3) with rfl | rfl | rfl | rfl <;> bv_omega

private theorem step_pre_col0 [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    (hrow : row < 4) {s : State} {F : SepProp}
    (hpc : s.pc = blkPl06.base + off7528) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcond : ConditionHolds .EQ s.pstate = false)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 row)
    (hx24 : s.readReg64 .x24 = 0#64) (hx25 : s.readReg64 .x25 = 4#64)
    (hg : EpiPreservedGprs06 sp rcBase fpVal row s) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off7558) s F
      (fun s1 P1 =>
        CopyGprs06 sp rcBase fpVal 1#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row s1 ∧
        s1.readReg64 .x0 = sp + 30456#64 ∧
        s1.readReg64 .x1 = sp + 4176#64 ∧
        s1.readReg64 .x2 = 512#64 ∧ (P1 ⊢ F)) := by
  rcases hg with ⟨hx1, hx19, hx22, hx23, hx26, hx28, hfp⟩
  wp_steps 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [*], hspA, by simp [*], by simp [*],
      by simpa [BitVec.add_assoc, *] using dst_row_shl06 (sp := sp) hrow,
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*]⟩,
     by simp [BitVec.add_assoc, *], by simp [BitVec.add_assoc, *], by simp, Entails.refl _⟩

set_option maxRecDepth 32768 in
private theorem step_col0 [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl06.base + off7558) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hg1 : CopyGprs06 sp rcBase fpVal 1#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 30456#64) (hx1_1 : s1.readReg64 .x1 = sp + 4176#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off758c) s1
      (((sp + 4176#64) ↦ₛ bs) ∗ ((sp + 30448#64) ↦ₛ pad8) ∗ memRegion (sp + 30456#64) 512 ∗
        memRegion (sp + 28368#64) 520 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs06 sp rcBase fpVal 1#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) ↦ₛ bs) ∗
            memRegion (sp + 4176#64) 512 ∗ ((sp + 30448#64) ↦ₛ pad8') ∗
            memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗ Rest)) := by
  have ha_dst0 : sp + 14432#64 + BitVec.ofNat 64 (2048 * row) =
      sp + 14432#64 + BitVec.ofNat 64 (2048 * row) := rfl
  prove_col_calls off755c off7574 1#64 (sp + 4176#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row))
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row))
    sp rcBase fpVal row bs pad8 hbs hpad hsp_chk hcl1 hro1 hg1 s1 ha_dst0 Rest

private theorem step_inter_col1 [MlKemPlacement] {sp rcBase fpVal x21Val : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl06.base + off758c) (hrun : s.status = .Running)
    (hg : CopyGprs06 sp rcBase fpVal 1#64 x21Val row s) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off75b4) s F
      (fun s1 P1 =>
        CopyGprs06 sp rcBase fpVal 2#64 x21Val row s1 ∧
        s1.readReg64 .x0 = sp + 30456#64 ∧ s1.readReg64 .x1 = sp + 4688#64 ∧
        s1.readReg64 .x2 = 512#64 ∧ (P1 ⊢ F)) := by
  rcases hg with ⟨hsp, hspA, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
  wp_steps 10
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp], hspA, by simp [g19], by simp, by simp [g21], by simp [g22],
      by simp [g23], by simp [g24], by simp [g25], by simp [g26], by simp [g27], by simp [g28],
      by simp [gfp]⟩, by simp; try bv_omega,
     by simp; try bv_omega, by simp, Entails.refl _⟩

set_option maxRecDepth 32768 in
private theorem step_col1 [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl06.base + off75b4) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hg1 : CopyGprs06 sp rcBase fpVal 2#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 30456#64) (hx1_1 : s1.readReg64 .x1 = sp + 4688#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off75e8) s1
      (((sp + 4688#64) ↦ₛ bs) ∗ ((sp + 30448#64) ↦ₛ pad8) ∗ memRegion (sp + 30456#64) 512 ∗
        memRegion (sp + 28368#64) 520 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs06 sp rcBase fpVal 2#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) ↦ₛ bs) ∗
            memRegion (sp + 4688#64) 512 ∗ ((sp + 30448#64) ↦ₛ pad8') ∗
            memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗ Rest)) := by
  have ha_dst : sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 512#64 =
      sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512) := by rw [BitVec.ofNat_add]; bv_omega
  prove_col_calls off75b8 off75d0 2#64 (sp + 4688#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 512#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512))
    sp rcBase fpVal row bs pad8 hbs hpad hsp_chk hcl1 hro1 hg1 s1 ha_dst Rest

private theorem step_inter_col2 [MlKemPlacement] {sp rcBase fpVal x21Val v6224 : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl06.base + off75e8) (hrun : s.status = .Running)
    (hg : CopyGprs06 sp rcBase fpVal 2#64 x21Val row s) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off7618) s
      (((sp + 6224#64) ↦₆₄ v6224) ∗ F)
      (fun s1 P1 =>
        CopyGprs06 sp rcBase fpVal 3#64 x21Val row s1 ∧
        s1.readReg64 .x0 = sp + 30456#64 ∧ s1.readReg64 .x1 = sp + 5200#64 ∧
        s1.readReg64 .x2 = 512#64 ∧ (P1 ⊢ ((sp + 6224#64) ↦₆₄ 3#64) ∗ F)) := by
  rcases hg with ⟨hsp, hspA, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
  wp_steps 12
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp], hspA, by simp [g19], by simp, by simp [g21], by simp [g22],
      by simp [g23], by simp [g24], by simp [g25], by simp [g26], by simp [g27], by simp [g28],
      by simp [gfp]⟩, by simp; try bv_omega,
     by simp; try bv_omega, by simp, Entails.refl _⟩

set_option maxRecDepth 32768 in
private theorem step_col2 [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl06.base + off7618) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hg1 : CopyGprs06 sp rcBase fpVal 3#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 30456#64) (hx1_1 : s1.readReg64 .x1 = sp + 5200#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off764c) s1
      (((sp + 5200#64) ↦ₛ bs) ∗ ((sp + 30448#64) ↦ₛ pad8) ∗ memRegion (sp + 30456#64) 512 ∗
        memRegion (sp + 28368#64) 520 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs06 sp rcBase fpVal 3#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) ↦ₛ bs) ∗
            memRegion (sp + 5200#64) 512 ∗ ((sp + 30448#64) ↦ₛ pad8') ∗
            memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗ Rest)) := by
  have ha_dst : sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 1024#64 =
      sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024) := by rw [BitVec.ofNat_add]; bv_omega
  prove_col_calls off761c off7634 3#64 (sp + 5200#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 1024#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024))
    sp rcBase fpVal row bs pad8 hbs hpad hsp_chk hcl1 hro1 hg1 s1 ha_dst Rest

private theorem step_inter_col3 [MlKemPlacement] {sp rcBase fpVal x21Val : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl06.base + off764c) (hrun : s.status = .Running)
    (hg : CopyGprs06 sp rcBase fpVal 3#64 x21Val row s) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off766c) s F
      (fun s1 P1 =>
        CopyGprs06 sp rcBase fpVal 3#64 x21Val row s1 ∧
        s1.readReg64 .x0 = sp + 30456#64 ∧ s1.readReg64 .x1 = sp + 5712#64 ∧
        s1.readReg64 .x2 = 512#64 ∧ (P1 ⊢ F)) := by
  rcases hg with ⟨hsp, hspA, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gfp⟩
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨⟨by simp [hsp], hspA, by simp [g19], by simp [g20], by simp [g21], by simp [g22],
      by simp [g23], by simp [g24], by simp [g25], by simp [g26], by simp [g27], by simp [g28],
      by simp [gfp]⟩, by simp; try bv_omega,
     by simp; try bv_omega, by simp, Entails.refl _⟩

set_option maxRecDepth 32768 in
private theorem step_col3 [MlKemPlacement] {sp rcBase fpVal : BitVec 64} {row : Nat}
    {bs pad8 : List (BitVec 8)} {Rest : SepProp} {s1 : State}
    (hbs : bs.length = 512) (hpad : pad8.length = 8) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = blkPl06.base + off766c) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (hg1 : CopyGprs06 sp rcBase fpVal 3#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row s1)
    (hx0_1 : s1.readReg64 .x0 = sp + 30456#64) (hx1_1 : s1.readReg64 .x1 = sp + 5712#64)
    (hx2_1 : s1.readReg64 .x2 = 512#64) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off76a0) s1
      (((sp + 5712#64) ↦ₛ bs) ∗ ((sp + 30448#64) ↦ₛ pad8) ∗ memRegion (sp + 30456#64) 512 ∗
        memRegion (sp + 28368#64) 520 ∗
        memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) 512 ∗ Rest)
      (fun sf Pf =>
        CopyGprs06 sp rcBase fpVal 3#64 (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) row sf ∧
        ∃ pad8' : List (BitVec 8), pad8'.length = 8 ∧
          (Pf ⊢ ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) ↦ₛ bs) ∗
            memRegion (sp + 5712#64) 512 ∗ ((sp + 30448#64) ↦ₛ pad8') ∗
            memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗ Rest)) := by
  have ha_dst : sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 1536#64 =
      sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536) := by rw [BitVec.ofNat_add]; bv_omega
  prove_col_calls off7670 off7688 3#64 (sp + 5712#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row) + 1536#64)
    (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536))
    sp rcBase fpVal row bs pad8 hbs hpad hsp_chk hcl1 hro1 hg1 s1 ha_dst Rest

private theorem step_post_col3 [MlKemPlacement] {sp rcBase fpVal x21Val : BitVec 64} {row : Nat}
    {s : State} {F : SepProp}
    (hpc : s.pc = blkPl06.base + off76a0) (hrun : s.status = .Running)
    (hg : CopyGprs06 sp rcBase fpVal 3#64 x21Val row s) :
    SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off4158) s F
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ EpiPreservedGprs06 sp rcBase fpVal row sf ∧ (Pf ⊢ F)) := by
  rcases hg with ⟨hsp, hspA, g19, _, _, g22, g23, _, _, g26, g27, g28, gfp⟩
  wp_steps 2
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [*], hspA,
     ⟨by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*]⟩, Entails.refl _⟩

/-! ## 4. Composed Row Epilogue `seg5_epi_ok` (`+0x710c → +0x4158`) -/

private theorem slots_rejoin_2176_06 (sp : BitVec 64) :
    memRegion (sp + 4160#64) 16 ∗ memRegion (sp + 4176#64) 512 ∗
      memRegion (sp + 4688#64) 512 ∗ memRegion (sp + 5200#64) 512 ∗
      memRegion (sp + 5712#64) 512 ∗ ((sp + 6224#64) ↦₆₄ 3#64) ∗
      memRegion (sp + 6232#64) 104 ⊢ memRegion (sp + 4160#64) 2176 := by
  have h8 : ((sp + 6224#64) ↦₆₄ 3#64) ⊢ memRegion (sp + 6224#64) 8 := by
    rw [pointsTo64_eq_unpackLane64]
    have hp := pointsToBytes_entails_memRegion (sp + 6224#64) (unpackLane64 3#64)
    rwa [unpackLane64_length] at hp
  have hmr : memRegion (sp + 4160#64) 2176 =
      memRegion (sp + 4160#64) 16 ∗ memRegion (sp + 4176#64) 512 ∗
        memRegion (sp + 4688#64) 512 ∗ memRegion (sp + 5200#64) 512 ∗
        memRegion (sp + 5712#64) 512 ∗ memRegion (sp + 6224#64) 8 ∗
        memRegion (sp + 6232#64) 104 := by
    rw [memRegion_split' (b := sp + 4160#64) (b' := sp + 4176#64) (n := 16) (k := (2160 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4176#64) (b' := sp + 4688#64) (n := 512) (k := (1648 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4688#64) (b' := sp + 5200#64) (n := 512) (k := (1136 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5200#64) (b' := sp + 5712#64) (n := 512) (k := (624 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5712#64) (b' := sp + 6224#64) (n := 512) (k := (112 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 6224#64) (b' := sp + 6232#64) (n := 8) (k := (104 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hmr]
  exact entails_sub h8 (by sep_frame) (by sep_frame)

set_option maxRecDepth 4096 in
theorem seg5_epi_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hrow : row < 4)
    {s : State} {P : SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * 7235)) (hrun : s.status = .Running)
    (hexit : RowExitState06 sp rcBase fpVal rho row
      (memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 ∗ Rest) s P) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off4158) s P
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        EpiPreservedGprs06 sp rcBase fpVal row sf ∧
        ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
          (Pf ⊢ RowPolyOut06 sp rho row ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            BTreeMem (sp + 144#64) 286 tA ∗ memRegion (sp + 26320#64) 32 ∗
            memRegion (sp + 4160#64) 2176 ∗ memRegion (sp + 28368#64) 672 ∗
            memRegion (sp + 30448#64) 2016 ∗ Rest)) := by
  subst hbase
  rcases hexit with ⟨hsp0, hspA0, hsp_chk, hcl0, hro0, hgprs0, hx1_0,
    extra, tA, sampled, hws, hhdr, hinv, hd, hP0⟩
  have hl0 : (hws 0).length = 272 := (hinv 0 (by decide)).1.1
  have hl1 : (hws 1).length = 272 := (hinv 1 (by decide)).1.1
  have hl2 : (hws 2).length = 272 := (hinv 2 (by decide)).1.1
  have hl3 : (hws 3).length = 272 := (hinv 3 (by decide)).1.1
  have hb0 : ((packHalfwordsLE (hws 0)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl0]
  have hb1 : ((packHalfwordsLE (hws 1)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl1]
  have hb2 : ((packHalfwordsLE (hws 2)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl2]
  have hb3 : ((packHalfwordsLE (hws 3)).take 512).length = 512 := by simp [packHalfwordsLE_length, hl3]
  refine SepWP.weaken_pre (Entails.trans hP0 (entails_sub
    (multiLaneSampled4_entails_memRegion32 (sp + 26320#64) sampled) (by sep_frame)
    (show memRegion (sp + 26320#64) 32 ∗ _ ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      MultiLaneSlots (sp + 4160#64) 544 4 hws ∗ _ by sep_frame))) ?_
  refine sepWP_seq_env hcl0 hro0
    (seg5_sliceD_ok hl0 hl1 hl2 hl3 hpc hrun hsp0 hspA0 hgprs0 hx1_0) ?_
  rintro sD PD hpcD hrunD hclD hroD ⟨hspD, hspAD, hcondD, _, hx21D, hx24D, hx25D, hgD, v6224, hPD⟩
  have h28368 : memRegion (sp + 28368#64) 672 =
      memRegion (sp + 28368#64) 520 ∗ memRegion (sp + 28888#64) 152 :=
    memRegion_split' (b := sp + 28368#64) (b' := sp + 28888#64) (n := 520) (k := (152 : Nat)) rfl (by bv_omega) (by decide)
  have h30448 : memRegion (sp + 30448#64) 2016 =
      memRegion (sp + 30448#64) 8 ∗ memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 30968#64) 1496 := by
    rw [memRegion_split' (b := sp + 30448#64) (b' := sp + 30456#64) (n := 8) (k := (2008 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30456#64) (b' := sp + 30968#64) (n := 512) (k := (1496 : Nat)) rfl (by bv_omega) (by decide)]
  have hout2048 : memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 2048 =
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 512 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) 512 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) 512 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) 512 := by
    rw [memRegion_split' (b := sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) (n := 512) (k := (1536 : Nat)) rfl (by rw [BitVec.ofNat_add]; bv_omega) (by decide),
      memRegion_split' (b := sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) (n := 512) (k := (1024 : Nat)) rfl (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega) (by decide),
      memRegion_split' (b := sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) (b' := sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) (n := 512) (k := (512 : Nat)) rfl (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega) (by decide)]
  rw [h28368, h30448, hout2048] at hPD
  refine SepWP.weaken_pre (Entails.trans hPD (show _ ⊢ memRegion (sp + 30448#64) 8 ∗ _ by sep_frame)) ?_
  refine SepWP.of_memRegion_btreeMem 1 (sp + 30448#64) (by decide) (by decide) rfl fun tPad => ?_
  have hpadEq : BTreeMem (sp + 30448#64) 1 tPad = ((sp + 30448#64) ↦ₛ unpackLane64 (tPad.get 0)) := by
    simp only [BTreeMem, BTreeMemFrom, sepConj_emp, pointsTo64_eq_unpackLane64]
  rw [hpadEq]
  have hpcD' : sD.pc = blkPl06.base + off7528 := by simpa using hpcD
  refine sepWP_seq_env hclD hroD
    (step_pre_col0 hrow hpcD' hrunD hspD hspAD hcondD hx21D hx24D hx25D hgD) ?_
  rintro s0 P0 hpc0 hrun0 hcl0' hro0' ⟨hg0, hx0_0, hx1_0', hx2_0, hP0'⟩
  refine SepWP.weaken_pre (Entails.trans hP0' (show _ ⊢
    ((sp + 4176#64) ↦ₛ (packHalfwordsLE (hws 0)).take 512) ∗
    ((sp + 30448#64) ↦ₛ unpackLane64 (tPad.get 0)) ∗
    memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗
    memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl0' hro0'
    (step_col0 hb0 (unpackLane64_length _) hsp_chk hpc0 hrun0 hcl0' hro0' hg0 hx0_0 hx1_0' hx2_0) ?_
  rintro s0' P0' hpc0' hrun0' hcl0'' hro0'' ⟨hg0', pad1, hpad1, hP0''⟩
  refine sepWP_seq_env hcl0'' hro0'' (SepWP.weaken_pre hP0'' (step_inter_col1 hpc0' hrun0' hg0')) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hg1, hx0_1, hx1_1, hx2_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
    ((sp + 4688#64) ↦ₛ (packHalfwordsLE (hws 1)).take 512) ∗
    ((sp + 30448#64) ↦ₛ pad1) ∗
    memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗
    memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (step_col1 hb1 hpad1 hsp_chk hpc1 hrun1 hcl1 hro1 hg1 hx0_1 hx1_1 hx2_1) ?_
  rintro s1' P1' hpc1' hrun1' hcl1' hro1' ⟨hg1', pad2, hpad2, hP1'⟩
  refine sepWP_seq_env hcl1' hro1'
    (SepWP.weaken_pre (Entails.trans hP1' (show _ ⊢ ((sp + 6224#64) ↦₆₄ v6224) ∗ _ by sep_frame))
      (step_inter_col2 hpc1' hrun1' hg1')) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hg2, hx0_2, hx1_2, hx2_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
    ((sp + 5200#64) ↦ₛ (packHalfwordsLE (hws 2)).take 512) ∗
    ((sp + 30448#64) ↦ₛ pad2) ∗
    memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗
    memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (step_col2 hb2 hpad2 hsp_chk hpc2 hrun2 hcl2 hro2 hg2 hx0_2 hx1_2 hx2_2) ?_
  rintro s2' P2' hpc2' hrun2' hcl2' hro2' ⟨hg2', pad3, hpad3, hP2'⟩
  refine sepWP_seq_env hcl2' hro2' (SepWP.weaken_pre hP2' (step_inter_col3 hpc2' hrun2' hg2')) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hg3, hx0_3, hx1_3, hx2_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢
    ((sp + 5712#64) ↦ₛ (packHalfwordsLE (hws 3)).take 512) ∗
    ((sp + 30448#64) ↦ₛ pad3) ∗
    memRegion (sp + 30456#64) 512 ∗ memRegion (sp + 28368#64) 520 ∗
    memRegion (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) 512 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl3 hro3
    (step_col3 hb3 hpad3 hsp_chk hpc3 hrun3 hcl3 hro3 hg3 hx0_3 hx1_3 hx2_3) ?_
  rintro s3' P3' hpc3' hrun3' hcl3' hro3' ⟨hg3', pad4, hpad4, hP3'⟩
  refine sepWP_seq_env hcl3' hro3' (SepWP.weaken_pre hP3' (step_post_col3 hpc3' hrun3' hg3')) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hgf, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hsp_chk, hclf, hrof, hgf, tA, hhdr, ?_⟩
  have hp0 : ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row)) ↦ₛ (packHalfwordsLE (hws 0)).take 512) =
      PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row))
        (polyVecNat ((sampleNtt (rowSeed rho row 0)).map (BitVec.ofNat 16))) := by
    rw [polyMem_bytesToPoly16 _ hb0, (hinv.exit_poly hd (by decide)).2.2, sampleNttClassical_eq_sampleNtt]
  have hp1 : ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512)) ↦ₛ (packHalfwordsLE (hws 1)).take 512) =
      PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 512))
        (polyVecNat ((sampleNtt (rowSeed rho row 1)).map (BitVec.ofNat 16))) := by
    rw [polyMem_bytesToPoly16 _ hb1, (hinv.exit_poly hd (by decide)).2.2, sampleNttClassical_eq_sampleNtt]
  have hp2 : ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024)) ↦ₛ (packHalfwordsLE (hws 2)).take 512) =
      PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1024))
        (polyVecNat ((sampleNtt (rowSeed rho row 2)).map (BitVec.ofNat 16))) := by
    rw [polyMem_bytesToPoly16 _ hb2, (hinv.exit_poly hd (by decide)).2.2, sampleNttClassical_eq_sampleNtt]
  have hp3 : ((sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536)) ↦ₛ (packHalfwordsLE (hws 3)).take 512) =
      PolyMem (sp + 14432#64 + BitVec.ofNat 64 (2048 * row + 1536))
        (polyVecNat ((sampleNtt (rowSeed rho row 3)).map (BitVec.ofNat 16))) := by
    rw [polyMem_bytesToPoly16 _ hb3, (hinv.exit_poly hd (by decide)).2.2, sampleNttClassical_eq_sampleNtt]
  have hpad4M : ((sp + 30448#64) ↦ₛ pad4) ⊢ memRegion (sp + 30448#64) 8 := by
    have hp := pointsToBytes_entails_memRegion (sp + 30448#64) pad4; rwa [hpad4] at hp
  rw [hp0, hp1, hp2, hp3] at hPf
  refine Entails.trans hPf ?_
  rw [h28368, h30448]
  unfold RowPolyOut06
  exact entails_sub (slots_rejoin_2176_06 sp) (by sep_frame)
    (entails_sub hpad4M (by sep_frame) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi
