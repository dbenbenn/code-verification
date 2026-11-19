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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs

/-!
# `kyber::encapsulate` (`B07`) — Segment 4 `compress_11` + `serialize_11` & `r̂` Copy (`+0x760c .. +0x7954`)

Proves `seg4_compress_ok` (`+0x760c → +0x7954`):
1. Copies `uVec[0..3]` (`2,048` B) from `[sp + 28848, sp + 30896)` to `[sp + 12848, sp + 14896)`.
2. Runs the 4-polynomial `compress_11` + `serialize_11` outer/inner loops writing `c₁` (`1,408` B)
   at `[sp + 23104, sp + 24512)`.
3. Copies `r̂[0..3]` (`2,048` B) from `[sp + 24720, sp + 26768)` to `[sp + 12832, sp + 14880)`
   with `x20 = sp + 12832#64`, preserving `x19` and `fp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemMpl seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane16 lane32 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid (
  neonSerialize11Bytes neonSerialize11Half serialize11_byte4_bfxil serialize11_byte8_bfxil)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem VecRangeMem
  polyVecNat step_ldpQ128 step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length
  vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdOrr_16b svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDup_4s exec_simdSqdmulh_4s exec_simdUshr_4s_4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (blk28_memcpy_07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Add (offSeg4RowsEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Simd (
  cells11_eq_neonSerialize11Half cells22_eq_neonSerialize11Bytes
  exec_simdBic_4s_f8_24 exec_simdBic_8h_f8_8 exec_simdMovi_2d_0
  exec_simdShl_4s_11 exec_simdUshr_4s_5
  exec_umov_b1 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5
  exec_umov_h6 exec_umov_h7 lane16_neonCompress8h_11_mask
  neonCompressSerialize11Poly neonCompressSerialize11Poly_length
  seg4_compress11_eq ser11_b0 ser11_b1 ser11_lsr ser11_shl_lsr)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x760c → 0x7954]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg4Header   : BitVec 64 := BitVec.ofNat 64 30260
@[simp, arm64_norm, wp_norm] abbrev offSeg4Outer    : BitVec 64 := BitVec.ofNat 64 30348
@[simp, arm64_norm, wp_norm] abbrev offSeg4Zero     : BitVec 64 := BitVec.ofNat 64 30436
@[simp, arm64_norm, wp_norm] abbrev offSeg4Inner    : BitVec 64 := BitVec.ofNat 64 30552
@[simp, arm64_norm, wp_norm] abbrev offSeg4Store    : BitVec 64 := BitVec.ofNat 64 30692
@[simp, arm64_norm, wp_norm] abbrev offSeg4Bounce   : BitVec 64 := BitVec.ofNat 64 30976
@[simp, arm64_norm, wp_norm] abbrev offSeg4RhatCopy : BitVec 64 := BitVec.ofNat 64 31028
@[simp, arm64_norm, wp_norm] abbrev offSeg5Start    : BitVec 64 := BitVec.ofNat 64 31060

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

attribute [local irreducible]
  blkPC07 polyVecNat dup8x16 lane16 lane32 pack4x32
  simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h neonCompress8h

@[simp, arm64_norm, wp_norm]
private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
@[simp, arm64_norm, wp_norm]
private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r
@[simp, arm64_norm, wp_norm]
private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem mem_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).mem = s.mem := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_writeReg64_gpr' (s : State) (i : BitVec 5) (w : BitVec 64) :
    (s.writeReg64 (.gpr i) w).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_setPC' (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm]
private theorem spAligned_setPState' (s : State) (ps : PState) :
    (s.setPState ps).spAligned = s.spAligned := by cases s; rfl
attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdBic_4s_f8_24 exec_simdBic_8h_f8_8
  exec_simdShl_4s_11 exec_simdUshr_4s_5
  exec_umov_b1 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4
  exec_umov_h5 exec_umov_h6 exec_umov_h7
  exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdOrr_16b svc_simdTrn1_8h

/-! ## 1. `ByteRangeMem` & Helper Step Lemmas -/

@[expose] def ByteRangeMem : Nat → BitVec 64 → (Nat → BitVec 8) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, f => (ptr ↦₈ f 0) ∗ ByteRangeMem n (ptr + 1#64) (fun i => f (i + 1))

theorem byteRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 8}
    (h : ∀ i, i < n → f i = g i) : ByteRangeMem n ptr f = ByteRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [ByteRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

theorem SepStore8.byteRange {n k : Nat} {ea ptr : BitVec 64} {val : BitVec 8}
    {f : Nat → BitVec 8} (hk : k < n) (ha : ptr + BitVec.ofNat 64 k = ea) :
    SepStore8 ea val (ByteRangeMem n ptr f) (ByteRangeMem n ptr (Function.update f k val)) := by
  induction n generalizing k ptr ea f with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      have h0 : ptr = ea := by simpa using ha
      have hu : ByteRangeMem n (ptr + 1#64) (fun i => Function.update f 0 val (i + 1)) =
          ByteRangeMem n (ptr + 1#64) (fun i => f (i + 1)) :=
        byteRangeMem_congr (fun i _ => by simp [Function.update])
      simp only [ByteRangeMem, Function.update_self, hu]
      exact SepStore8.left (SepStore8.here h0)
    | succ j =>
      have ha' : (ptr + 1#64) + BitVec.ofNat 64 j = ea := by rw [← ha]; bv_omega
      have hu : ByteRangeMem n (ptr + 1#64) (fun i => Function.update f (j + 1) val (i + 1)) =
          ByteRangeMem n (ptr + 1#64) (Function.update (fun i => f (i + 1)) j val) :=
        byteRangeMem_congr (fun i _ => by simp [Function.update])
      simp only [ByteRangeMem, show Function.update f (j + 1) val 0 = f 0 by simp [Function.update], hu]
      exact SepStore8.right (ih (Nat.lt_of_succ_lt_succ hk) ha')

theorem sepWP_elim_cell1 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 8, SepWP prog target s ((a ↦₈ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

theorem sepWP_elim_byteRange :
    ∀ (n : Nat), n ≤ 32 → ∀ {prog : Program} {target : BitVec 64} {s : State}
      {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop},
      (∀ f : Nat → BitVec 8, SepWP prog target s (ByteRangeMem n a f ∗ R0) post) →
      SepWP prog target s (memRegion a n ∗ R0) post
  | 0, _, _, _, _, _, _, _, h => by
    simpa [ByteRangeMem, memRegion_zero] using h (fun _ => 0#8)
  | n + 1, _, _, _, _, a, R0, _, h => by
    rw [show n + 1 = 1 + n by omega,
      memRegion_split' (b := a) (b' := a + 1#64) (n := 1) (k := (n : Nat)) rfl (by bv_omega)
        (by change 1 + n ≤ 18446744073709551616; omega),
      sepConj_assoc]
    apply sepWP_elim_cell1; intro v0
    refine SepWP.weaken_pre
      (show (a ↦₈ v0) ∗ (memRegion (a + 1#64) n ∗ R0) ⊢
        memRegion (a + 1#64) n ∗ ((a ↦₈ v0) ∗ R0) by sep_frame) ?_
    apply sepWP_elim_byteRange n (by omega); intro f'
    let f : Nat → BitVec 8 := fun i => match i with | 0 => v0 | j + 1 => f' j
    have hf : ByteRangeMem (n + 1) a f = (a ↦₈ v0) ∗ ByteRangeMem n (a + 1#64) f' := rfl
    refine SepWP.weaken_pre ?_ (h f)
    rw [hf]; sep_frame

private theorem byteRangeMem_split11 (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 22 a f =
      ByteRangeMem 11 a f ∗ ByteRangeMem 11 (a + 11#64) (fun i => f (i + 11)) := by
  dsimp only [ByteRangeMem]
  simp only [sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd, Nat.add_assoc]

private theorem byteRangeMem11_eq_cells (a : BitVec 64) (f : Nat → BitVec 8) :
    ByteRangeMem 11 a f =
      (a ↦₈ f 0) ∗ ((a + 1#64) ↦₈ f 1) ∗ ((a + 2#64) ↦₈ f 2) ∗ ((a + 3#64) ↦₈ f 3) ∗
      ((a + 4#64) ↦₈ f 4) ∗ ((a + 5#64) ↦₈ f 5) ∗ ((a + 6#64) ↦₈ f 6) ∗ ((a + 7#64) ↦₈ f 7) ∗
      ((a + 8#64) ↦₈ f 8) ∗ ((a + 9#64) ↦₈ f 9) ∗ ((a + 10#64) ↦₈ f 10) := by
  dsimp only [ByteRangeMem]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

@[simp] private theorem sp_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).sp = s.sp := rfl
@[simp] private theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).pstate = s.pstate := rfl
@[simp] private theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) :
    (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) :
    (s.setMem m).readVReg128 v = s.readVReg128 v := rfl

theorem step_strSimd8_byteRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff n k : Nat) (vt : BitVec 5) (addr : AddrMode) (val : BitVec 8)
    (f : Nat → BitVec 8)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.strSimd .B8 vt addr))
    (hchk : checkAddrSPAligned s addr = true)
    (hea : evalAddrMode s addr = (ea + BitVec.ofNat 64 k, none))
    (hval : (s.readVReg128 vt).truncate 8 = val)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (ByteRangeMem n ea (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (ByteRangeMem n ea f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strSimd8 (wb := none) hpc hrun hfetch hchk hea hval
    (SepStore8.left (SepStore8.byteRange hk rfl))
    (by simp [applyWriteback, hpc']) hnext

theorem step_str8_byteRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff n k : Nat) (rn rt : Reg) (val : BitVec 8)
    (f : Nat → BitVec 8)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.str .B8 rt (.Offset rn (BitVec.ofNat 64 k))))
    (hchk : checkAddrSPAligned s (.Offset rn (BitVec.ofNat 64 k)) = true)
    (hea : s.readReg64 rn = ea) (hval : (s.readReg32 rt).truncate 8 = val)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (ByteRangeMem n ea (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (ByteRangeMem n ea f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_str8 (wb := none) hpc hrun hfetch hchk
    (by simp [evalAddrMode, hea]) hval
    (SepStore8.left (SepStore8.byteRange hk rfl))
    (by simp [applyWriteback, hpc']) hnext

private theorem step_strQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5) (val : BitVec 128)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off)
    (hval : s.readVReg128 vt = val) (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (VecRangeMem n base (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp]) hval
    (SepStore128.left (SepStore128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

private theorem step_ldrQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.ldrSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (f k)).setPC (b + BitVec.ofNat 64 nextOff))
      (VecRangeMem n base f ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

theorem polyMem4_eq_pointsToBytes (a : BitVec 64) (p0 p1 p2 p3 : Poly16) :
    PolyMem a (polyVecNat p0) ∗ PolyMem (a + 512#64) (polyVecNat p1) ∗
      PolyMem (a + 1024#64) (polyVecNat p2) ∗ PolyMem (a + 1536#64) (polyVecNat p3) =
      (a ↦ₛ (vecRangeBytes 32 (polyVecNat p0) ++ vecRangeBytes 32 (polyVecNat p1) ++
        vecRangeBytes 32 (polyVecNat p2) ++ vecRangeBytes 32 (polyVecNat p3))) := by
  dsimp only [PolyMem]
  rw [vecRangeMem_eq_pointsToBytes 32 a, vecRangeMem_eq_pointsToBytes 32 (a + 512#64),
    vecRangeMem_eq_pointsToBytes 32 (a + 1024#64), vecRangeMem_eq_pointsToBytes 32 (a + 1536#64)]
  simp only [List.append_assoc, pointsToBytes_append, vecRangeBytes_length,
    show BitVec.ofNat 64 (16 * 32) = 512#64 from rfl, BitVec.add_assoc, BitVec.reduceAdd]

private def ser11Chunk (u : Poly16) (c : Nat) : List (BitVec 8) :=
  neonSerialize11Bytes (neonCompress8h 11 (polyVecNat u (2 * c)))
    (neonCompress8h 11 (polyVecNat u (2 * c + 1)))

private def ser11Prefix (u : Poly16) (c : Nat) : List (BitVec 8) :=
  ((List.range c).map (ser11Chunk u)).flatten

private theorem ser11Chunk_length (u : Poly16) (c : Nat) : (ser11Chunk u c).length = 22 := rfl

private theorem ser11Prefix_length (u : Poly16) (c : Nat) : (ser11Prefix u c).length = 22 * c := by
  induction c with
  | zero => simp [ser11Prefix]
  | succ n ih =>
    rw [show ser11Prefix u (n + 1) = ser11Prefix u n ++ ser11Chunk u n by
      simp [ser11Prefix, List.range_succ, List.flatten_append]]
    rw [List.length_append, ih, ser11Chunk_length]; omega

private theorem ser11Prefix_succ (u : Poly16) (c : Nat) :
    ser11Prefix u (c + 1) = ser11Prefix u c ++ ser11Chunk u c := by
  simp [ser11Prefix, List.range_succ, List.flatten_append]

private theorem ser11Prefix_sixteen (u : Poly16) :
    ser11Prefix u 16 = neonCompressSerialize11Poly u := rfl

private abbrev c10321340Vec  : BitVec 128 := pack4x32 fun _ => 10321340#32
private abbrev c1664Vec      : BitVec 128 := pack4x32 fun _ => 1664#32
private abbrev c134215680Vec : BitVec 128 := pack4x32 fun _ => 134215680#32
private abbrev c3329Vec      : BitVec 128 := dup8x16 3329#16

private def ser11ConstFn : Nat → BitVec 128
  | 0 => c10321340Vec
  | 1 => c1664Vec
  | 2 => c134215680Vec
  | _ => c3329Vec

/-! ## 2. `uVec` Copy (`+0x760c → +0x7634`) & Header (`+0x7634 → +0x768c`) -/

private theorem seg4_uvec_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) (u0 u1 u2 u3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4RowsEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Header) s
      (PolyMem (sp + 28848#64) (polyVecNat u0) ∗ PolyMem (sp + 29360#64) (polyVecNat u1) ∗
        PolyMem (sp + 29872#64) (polyVecNat u2) ∗ PolyMem (sp + 30384#64) (polyVecNat u3) ∗
        memRegion (sp + 12848#64) 2048 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x20 = sp + 12848#64 ∧ sf.readReg64 .x22 = sp + 28848#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13360#64) (polyVecNat u1) ∗
          PolyMem (sp + 13872#64) (polyVecNat u2) ∗ PolyMem (sp + 14384#64) (polyVecNat u3) ∗
          memRegion (sp + 28848#64) 2048 ∗ Rest)) := by
  subst hbase
  generalize hbs4_def : vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
    vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3) = bs4
  have hbs4 : bs4.length = 2048 := by rw [← hbs4_def]; simp [List.length_append, vecRangeBytes_length]
  have hpSrc := polyMem4_eq_pointsToBytes (sp + 28848#64) u0 u1 u2 u3
  have hpDst := polyMem4_eq_pointsToBytes (sp + 12848#64) u0 u1 u2 u3
  rw [hbs4_def] at hpSrc hpDst
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpSrc hpDst
  refine SepWP.weaken_pre
    (show _ ⊢ ((sp + 28848#64) ↦ₛ bs4) ∗ memRegion (sp + 12848#64) 2048 ∗ Rest by
      rw [← hpSrc]; sep_frame) ?_
  wp_steps 9; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 12848#64, sp + 28848#64, bs4)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*],
      by simp [*], by simp [*], hcl1, ?_⟩
  have hmSrc : ((sp + 28848#64) ↦ₛ bs4) ⊢ memRegion (sp + 28848#64) 2048 := by
    rw [← hbs4]; exact pointsToBytes_entails_memRegion (sp + 28848#64) bs4
  have hpDst' : ((sp + 12848#64) ↦ₛ bs4) ⊢
      PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13360#64) (polyVecNat u1) ∗
        PolyMem (sp + 13872#64) (polyVecNat u2) ∗ PolyMem (sp + 14384#64) (polyVecNat u3) := by
    rw [← hpDst]; exact Entails.refl _
  exact entails_sub hpDst' (by sep_frame) (entails_sub hmSrc (by sep_frame) (by sep_frame))

private theorem seg4_header [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Header) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hx20 : s.readReg64 .x20 = sp + 12848#64) (hx22 : s.readReg64 .x22 = sp + 28848#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Outer) s
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 12840#64) 8 ∗
        memRegion (sp + 14896#64) 8 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = x19Val ∧ s1.readReg64 .fp = fpVal ∧
        s1.readReg64 .x20 = sp + 12848#64 ∧ s1.readReg64 .x22 = sp + 28848#64 ∧
        s1.readReg64 .x23 = 0#64 ∧ s1.readReg64 .x25 = 352#64 ∧
        s1.readReg64 .x26 = sp + 32288#64 ∧ s1.readReg64 .x27 = sp + 23104#64 ∧
        (P1 ⊢ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
          memRegion (sp + 12840#64) 8 ∗ memRegion (sp + 14896#64) 8 ∗ Rest)) := by
  subst hbase
  apply SepWP.of_memRegion_vecRangeMem 4 (sp + 2368#64) (by decide) (by sep_focus); intro fc
  refine SepWP.weaken_pre
    (show VecRangeMem 4 (sp + 2368#64) fc ∗ (memRegion (sp + 12840#64) 8 ∗ memRegion (sp + 14896#64) 8 ∗ Rest) ⊢
      memRegion (sp + 12840#64) 8 ∗ (memRegion (sp + 14896#64) 8 ∗ (VecRangeMem 4 (sp + 2368#64) fc ∗ Rest)) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w1
  refine SepWP.weaken_pre (show ((sp + 12840#64) ↦₆₄ w1) ∗ (memRegion (sp + 14896#64) 8 ∗
      (VecRangeMem 4 (sp + 2368#64) fc ∗ Rest)) ⊢
      memRegion (sp + 14896#64) 8 ∗ (((sp + 12840#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2368#64) fc ∗ Rest) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w2
  refine SepWP.weaken_pre
    (show ((sp + 14896#64) ↦₆₄ w2) ∗ (((sp + 12840#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2368#64) fc ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2368#64) fc ∗ (((sp + 12840#64) ↦₆₄ w1) ∗ ((sp + 14896#64) ↦₆₄ w2) ∗ Rest) by
      sep_frame) ?_
  wp_steps 12
  refine step_strQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30308 30312 2416 4 3 0#5 c3329Vec fc
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c3329Vec]) rfl ?_; intro m1
  wp_steps 4
  refine step_strQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30328 30332 2400 4 2 0#5 c134215680Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c134215680Vec]) rfl ?_; intro m2
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30336 30340 2384 4 1 0#5 c1664Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c1664Vec]) rfl ?_; intro m3
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30344 30348 2368 4 0 0#5 c10321340Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c10321340Vec]) rfl ?_; intro m4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp [hx19], by simp [hfp], by simp [hx20], by simp [hx22],
      by simp, by simp, by simp, by simp, ?_⟩
  have hvc : VecRangeMem 4 (sp + 2368#64)
      (Function.update (Function.update (Function.update (Function.update fc 3 c3329Vec) 2 c134215680Vec) 1 c1664Vec) 0 c10321340Vec) =
      VecRangeMem 4 (sp + 2368#64) ser11ConstFn := by
    apply vecRangeMem_congr; intro i hi
    rcases i with _ | _ | _ | _ | n <;> try omega
    all_goals simp [ser11ConstFn, Function.update]
  rw [hvc]
  exact entails_sub (cell_entails_memRegion8 (sp + 12840#64) 4#64) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (sp + 14896#64) 0#64) (by sep_frame) (by sep_frame))

/-! ## 3. Outer-Loop Stage Preparation (`+0x768c → +0x76e4`) & Zero/Load (`+0x76e4 → +0x7758`) -/

private theorem seg4_prep_poly [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) {idx : Nat} (hidx : idx < 4) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hx20 : s.readReg64 .x20 = sp + 12848#64) (hx22 : s.readReg64 .x22 = sp + 28848#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 idx) (hx25 : s.readReg64 .x25 = 352#64)
    (hx26 : s.readReg64 .x26 = sp + 32288#64) (hx27 : s.readReg64 .x27 = sp + 23104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (12848 + 512 * idx)
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Zero) s
      (PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 28848#64) 520 ∗ memRegion (sp + 31408#64) 520 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x20 = sp + 12848#64 ∧ sf.readReg64 .x21 = BitVec.ofNat 64 (352 * idx) ∧
        sf.readReg64 .x22 = sp + 28848#64 ∧ sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x25 = 352#64 ∧ sf.readReg64 .x26 = sp + 32288#64 ∧
        sf.readReg64 .x27 = sp + 23104#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem uPtr (polyVecNat u) ∗ PolyMem (sp + 28848#64) (polyVecNat u) ∗
          memRegion (sp + 29360#64) 8 ∗ memRegion (sp + 31408#64) 520 ∗ Rest)) := by
  subst hbase; intro uPtr
  generalize hbsU_def : vecRangeBytes 32 (polyVecNat u) = bsU
  have hbsU : bsU.length = 512 := by rw [← hbsU_def]; exact vecRangeBytes_length 32 (polyVecNat u)
  have hpU_src : PolyMem uPtr (polyVecNat u) = (uPtr ↦ₛ bsU) := by
    dsimp only [PolyMem]; rw [vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u), hbsU_def]
  have hpU_dst : PolyMem (sp + 28848#64) (polyVecNat u) = ((sp + 28848#64) ↦ₛ bsU) := by
    dsimp only [PolyMem]; rw [vecRangeMem_eq_pointsToBytes 32 (sp + 28848#64) (polyVecNat u), hbsU_def]
  have hm520a : memRegion (sp + 28848#64) 520 = memRegion (sp + 28848#64) 8 ∗ memRegion (sp + 28856#64) 512 :=
    memRegion_split' (b := sp + 28848#64) (b' := sp + 28856#64) (n := 8) (k := (512 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm520b : memRegion (sp + 28848#64) 520 = memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 8 :=
    memRegion_split' (b := sp + 28848#64) (b' := sp + 29360#64) (n := 512) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  rw [hm520a]
  refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 28848#64) 8 ∗
      ((uPtr ↦ₛ bsU) ∗ memRegion (sp + 28856#64) 512 ∗ memRegion (sp + 31408#64) 520 ∗ Rest) by
    rw [hpU_src]; sep_frame) ?_
  apply sepWP_elim_cell8; intro w0
  have huPtr : (sp + 12848#64) + (BitVec.ofNat 64 idx <<< 9) = uPtr := by
    dsimp only [uPtr]; rcases idx with _ | _ | _ | _ | n <;> try omega
    all_goals (clear * -; bv_omega)
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 28856#64, uPtr, bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  generalize hbs520_def : unpack64 w0 ++ bsU = bs520
  have h520len : bs520.length = 520 := by
    rw [← hbs520_def]; simp [List.length_append, unpack64_length, hbsU]
  have hjoin1 : ((sp + 28848#64) ↦₆₄ w0) ∗ ((sp + 28856#64) ↦ₛ bsU) = ((sp + 28848#64) ↦ₛ bs520) := by
    have ha : (sp + 28848#64) + BitVec.ofNat 64 (unpack64 w0).length = sp + 28856#64 := by
      rw [unpack64_length]; clear * -; bv_omega
    rw [← hbs520_def, pointsTo64_eq_pointsToBytes, pointsToBytes_append, ha]
  refine SepWP.weaken_pre
    (P' := ((sp + 28848#64) ↦ₛ bs520) ∗ memRegion (sp + 31408#64) 520 ∗ ((uPtr ↦ₛ bsU) ∗ Rest))
    (Entails.trans (show _ ⊢ (((sp + 28848#64) ↦₆₄ w0) ∗ ((sp + 28856#64) ↦ₛ bsU)) ∗
        memRegion (sp + 31408#64) 520 ∗ ((uPtr ↦ₛ bsU) ∗ Rest) by sep_frame)
      (by rw [hjoin1]; exact Entails.refl _)) ?_
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl1)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 31408#64, sp + 28848#64, bs520)
  apply SepWP.done (by assumption) (by assumption); intro hcl2
  have hsp2 : sf_1.sp = sp := by simp [*]
  have hsplit31408 : ((sp + 31408#64) ↦ₛ bs520) =
      ((sp + 31408#64) ↦ₛ unpack64 w0) ∗ ((sp + 31416#64) ↦ₛ bsU) := by
    have ha : (sp + 31408#64) + BitVec.ofNat 64 (unpack64 w0).length = sp + 31416#64 := by
      rw [unpack64_length]; clear * -; bv_omega
    rw [← hbs520_def, pointsToBytes_append, ha]
  have hm28848 : ((sp + 28848#64) ↦ₛ bs520) ⊢
      memRegion (sp + 28848#64) 512 ∗ memRegion (sp + 29360#64) 8 := by
    rw [← hm520b, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 28848#64) bs520
  refine SepWP.weaken_pre
    (P' := ((sp + 31416#64) ↦ₛ bsU) ∗ memRegion (sp + 28848#64) 512 ∗
      (((sp + 31408#64) ↦ₛ unpack64 w0) ∗ memRegion (sp + 29360#64) 8 ∗ (uPtr ↦ₛ bsU) ∗ Rest))
    (by rw [hsplit31408]; exact entails_sub hm28848 (by sep_frame) (by sep_frame)) ?_
  wp_steps 6; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl2)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 28848#64, sp + 31416#64, bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl3
  have hsp3 : sf_2.sp = sp := by simp [*]
  have hspA3 : sf_2.spAligned = true := spAligned_of_sp_eq hspA hsp hsp3
  have hcond : ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 idx) 4#64) = false := by
    rw [conditionHolds_eq_subsPState64]
    rcases idx with _ | _ | _ | _ | n <;> try omega
    all_goals decide
  wp_steps 2
  refine step_bCond_not_taken (dst := blkPl07.base + offSeg4Zero)
    (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by clear * -; dsimp [offSeg4Zero]; bv_omega) ?_
  refine SepWP.done rfl (by simp [*])
    ⟨by simp [hsp3], spAligned_of_sp_eq hspA3 hsp3 (by simp [hsp3]),
      by simp [*], by simp [*], by simp [*],
      by rcases idx with _ | _ | _ | _ | n <;> try omega
         all_goals simp [*],
      by simp [*],
      by rcases idx with _ | _ | _ | _ | n <;> try omega
         all_goals simp [*],
      by simp [*], by simp [*], by simp [*], hcl3, ?_⟩
  have hm31408 : ((sp + 31408#64) ↦ₛ unpack64 w0) ∗ ((sp + 31416#64) ↦ₛ bsU) ⊢
      memRegion (sp + 31408#64) 520 := by
    rw [← hsplit31408, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 31408#64) bs520
  rw [hpU_src, hpU_dst]
  exact entails_sub hm31408 (by sep_frame) (by sep_frame)

local macro "step_zero_q22 " sp:term:arg hrun:term:arg hsp:term:arg hspA:term:arg
    pcOff:num nextOff:num spOff:num k:num : tactic => `(tactic|
  (refine step_strQ128_sp_vecRange blkPl07.base $sp ($sp + 32288#64) $pcOff $nextOff $spOff 22 $k 0#5 0#128 _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp [$hsp:term])
      (spAligned_of_sp_eq $hspA $hsp (by simp [$hsp:term]))
      (by simp) (by clear * -; bv_omega) (by simp) rfl ?_;
   intro _))

private theorem seg4_zero_load [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Zero) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hx22 : s.readReg64 .x22 = sp + 28848#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Inner) s
      (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion (sp + 32288#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 28864#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = sp + 28848#64 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readVReg128 5#5 = c3329Vec ∧ sf.readVReg128 6#5 = c134215680Vec ∧
        sf.readVReg128 7#5 = c1664Vec ∧ sf.readVReg128 16#5 = c10321340Vec ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion (sp + 32288#64) 352 ∗ Rest)) := by
  subst hbase
  refine SepWP.weaken_pre
    (show VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ (memRegion (sp + 32288#64) 352 ∗ Rest) ⊢
      memRegion (sp + 32288#64) 352 ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest) by sep_frame) ?_
  apply SepWP.of_memRegion_vecRangeMem 22 (sp + 32288#64) (by decide) (by sep_focus); intro fz
  refine SepWP.weaken_pre
    (show VecRangeMem 22 (sp + 32288#64) fz ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ (VecRangeMem 22 (sp + 32288#64) fz ∗ Rest) by sep_frame) ?_
  wp_steps 1
  refine step_ldrQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30440 30444 2416 4 3 5#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30444 30448 2400 4 2 6#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30448 30452 2384 4 1 7#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl07.base sp (sp + 2368#64) 30452 30456 2368 4 0 16#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  wp_steps 2
  refine SepWP.weaken_pre
    (P' := VecRangeMem 22 (sp + 32288#64) fz ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest))
    (by sep_frame) ?_
  step_zero_q22 sp hrun hsp hspA 30464 30468 32624 21; step_zero_q22 sp hrun hsp hspA 30468 30472 32608 20
  step_zero_q22 sp hrun hsp hspA 30472 30476 32592 19; step_zero_q22 sp hrun hsp hspA 30476 30480 32576 18
  step_zero_q22 sp hrun hsp hspA 30480 30484 32560 17; step_zero_q22 sp hrun hsp hspA 30484 30488 32544 16
  step_zero_q22 sp hrun hsp hspA 30488 30492 32528 15; step_zero_q22 sp hrun hsp hspA 30492 30496 32512 14
  step_zero_q22 sp hrun hsp hspA 30496 30500 32496 13; step_zero_q22 sp hrun hsp hspA 30500 30504 32480 12
  step_zero_q22 sp hrun hsp hspA 30504 30508 32464 11; step_zero_q22 sp hrun hsp hspA 30508 30512 32448 10
  step_zero_q22 sp hrun hsp hspA 30512 30516 32432 9;  step_zero_q22 sp hrun hsp hspA 30516 30520 32416 8
  step_zero_q22 sp hrun hsp hspA 30520 30524 32400 7;  step_zero_q22 sp hrun hsp hspA 30524 30528 32384 6
  step_zero_q22 sp hrun hsp hspA 30528 30532 32368 5;  step_zero_q22 sp hrun hsp hspA 30532 30536 32352 4
  step_zero_q22 sp hrun hsp hspA 30536 30540 32336 3;  step_zero_q22 sp hrun hsp hspA 30540 30544 32320 2
  step_zero_q22 sp hrun hsp hspA 30544 30548 32304 1;  step_zero_q22 sp hrun hsp hspA 30548 30552 32288 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp [hx19], by simp [hfp], by simp, by simp,
      by simp, by simp, by simp [hx22], by simp, by simp, by simp, by simp,
      by simp [ser11ConstFn], by simp [ser11ConstFn], by simp [ser11ConstFn], by simp [ser11ConstFn], ?_⟩
  exact entails_sub (vecRangeMem_entails_memRegion 22 (sp + 32288#64) _) (by sep_frame) (by sep_frame)

/-! ## 4. 16-Iteration `compress_11` + `serialize_11` Inner Loop (`+0x7758 → +0x7900`) -/

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

set_option maxRecDepth 8000 in
private theorem seg4_inner_simd_ushr [MlKemPlacement] (sn : State) (P : SepProp)
    (q0 q1 q2 q3 : BitVec 128)
    (hpc : sn.pc = blkPl07.base + BitVec.ofNat 64 30660) (hrun : sn.status = .Running)
    (hv2 : sn.readVReg128 2#5 = q0) (hv0 : sn.readVReg128 0#5 = q1)
    (hv3 : sn.readVReg128 3#5 = q2) (hv1 : sn.readVReg128 1#5 = q3)
    (hv5 : sn.readVReg128 5#5 = c3329Vec) (hv6 : sn.readVReg128 6#5 = c134215680Vec)
    (hv7 : sn.readVReg128 7#5 = c1664Vec) (hv16 : sn.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg4Store) sn P
      (fun s1 P1 =>
        s1.sp = sn.sp ∧ s1.spAligned = sn.spAligned ∧ s1.pstate = sn.pstate ∧
        (∀ r : Reg, s1.readReg64 r = sn.readReg64 r) ∧
        s1.readVReg128 1#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 q0 k >>> 4)
          (pack4x32 fun k => lane32 q1 k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 0#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 q2 k >>> 4)
          (pack4x32 fun k => lane32 q3 k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c134215680Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, fun _ => by simp,
      by simp, by simp,
      by simp [hv5], by simp [hv6], by simp [hv7], by simp [hv16], rfl⟩

set_option maxRecDepth 8000 in
private theorem seg4_inner_simd_mul [MlKemPlacement] (sm : State) (P : SepProp)
    (ev0 od0 ev1 od1 : BitVec 128)
    (hpc : sm.pc = blkPl07.base + BitVec.ofNat 64 30644) (hrun : sm.status = .Running)
    (hv2 : sm.readVReg128 2#5 = ev0) (hv0 : sm.readVReg128 0#5 = od0)
    (hv3 : sm.readVReg128 3#5 = ev1) (hv1 : sm.readVReg128 1#5 = od1)
    (hv5 : sm.readVReg128 5#5 = c3329Vec) (hv6 : sm.readVReg128 6#5 = c134215680Vec)
    (hv7 : sm.readVReg128 7#5 = c1664Vec) (hv16 : sm.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg4Store) sm P
      (fun s1 P1 =>
        s1.sp = sm.sp ∧ s1.spAligned = sm.spAligned ∧ s1.pstate = sm.pstate ∧
        (∀ r : Reg, s1.readReg64 r = sm.readReg64 r) ∧
        s1.readVReg128 1#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s ev0 c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s od0 c10321340Vec) k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 0#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s ev1 c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s od1 c10321340Vec) k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c134215680Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 4
  refine SepWP.mono (seg4_inner_simd_ushr _ P
    (simdSqdmulh4s ev0 c10321340Vec) (simdSqdmulh4s od0 c10321340Vec)
    (simdSqdmulh4s ev1 c10321340Vec) (simdSqdmulh4s od1 c10321340Vec)
    (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp) (by simp) (by simp)
    (by simp [hv5]) (by simp [hv6]) (by simp [hv7]) (by simp [hv16])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  exact ⟨hsp1.trans (by simp), hspA1.trans (by simp), hpst1.trans (by simp),
    fun r => (hregs1 r).trans (by simp),
    hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩

set_option maxRecDepth 8000 in
private theorem seg4_inner_simd_mid [MlKemPlacement] (sb : State) (P : SepProp)
    (a0 a1 : BitVec 128)
    (hpc : sb.pc = blkPl07.base + BitVec.ofNat 64 30596) (hrun : sb.status = .Running)
    (hv0 : sb.readVReg128 0#5 = a0) (hv1 : sb.readVReg128 1#5 = a1)
    (hv5 : sb.readVReg128 5#5 = c3329Vec) (hv6 : sb.readVReg128 6#5 = c134215680Vec)
    (hv7 : sb.readVReg128 7#5 = c1664Vec) (hv16 : sb.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg4Store) sb P
      (fun s1 P1 =>
        s1.sp = sb.sp ∧ s1.spAligned = sb.spAligned ∧ s1.pstate = sb.pstate ∧
        (∀ r : Reg, s1.readReg64 r = sb.readReg64 r) ∧
        s1.readVReg128 1#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s (((pack4x32 fun j => lane32 a0 j <<< 11) &&&
            0x07ffffff07ffffff07ffffff07ffffff#128) ||| c1664Vec) c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s (((pack4x32 fun j => lane32 a0 j >>> 5) &&&
            c134215680Vec) ||| c1664Vec) c10321340Vec) k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 0#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s (((pack4x32 fun j => lane32 a1 j <<< 11) &&&
            0x07ffffff07ffffff07ffffff07ffffff#128) ||| c1664Vec) c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s (((pack4x32 fun j => lane32 a1 j >>> 5) &&&
            c134215680Vec) ||| c1664Vec) c10321340Vec) k >>> 4) &&& dup8x16 0x07ff#16) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c134215680Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 4
  refine sepWP_cut (fun sc => sc.pc = blkPl07.base + BitVec.ofNat 64 30612 ∧ sc.status = .Running ∧
    sc.sp = sb.sp ∧ sc.spAligned = sb.spAligned ∧ sc.pstate = sb.pstate ∧
    (∀ r : Reg, sc.readReg64 r = sb.readReg64 r) ∧
    sc.readVReg128 2#5 = (pack4x32 fun j => lane32 a0 j <<< 11) ∧
    sc.readVReg128 0#5 = (pack4x32 fun j => lane32 a0 j >>> 5) ∧
    sc.readVReg128 3#5 = (pack4x32 fun j => lane32 a1 j <<< 11) ∧
    sc.readVReg128 1#5 = (pack4x32 fun j => lane32 a1 j >>> 5) ∧
    sc.readVReg128 5#5 = c3329Vec ∧ sc.readVReg128 6#5 = c134215680Vec ∧
    sc.readVReg128 7#5 = c1664Vec ∧ sc.readVReg128 16#5 = c10321340Vec)
    ⟨by wp_norm_lhs, by simp [hrun], by simp, by simp, by simp, fun _ => by simp,
      by simp, by simp, by simp, by simp,
      by simp [hv5], by simp [hv6], by simp [hv7], by simp [hv16]⟩ ?_
  rintro sc ⟨hpc_c, hrun_c, hsp_c, hspA_c, hpst_c, hregs_c,
    hv2_c, hv0_c, hv3_c, hv1_c, hv5_c, hv6_c, hv7_c, hv16_c⟩
  wp_steps 8
  refine SepWP.mono (seg4_inner_simd_mul _ P _ _ _ _
    (by wp_norm_lhs) (by simp [hrun_c])
    rfl rfl rfl rfl
    (by simp [hv5_c]) (by simp [hv6_c]) (by simp [hv7_c]) (by simp [hv16_c])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  exact ⟨hsp1.trans (by simp [hsp_c]), hspA1.trans (by simp [hspA_c]),
    hpst1.trans (by simp [hpst_c]), fun r => (hregs1 r).trans (by simp [hregs_c r]),
    hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩

private theorem seg4_inner_simd_prep [MlKemPlacement] (sa : State) (P : SepProp)
    (v0_in v1_in : BitVec 128)
    (hpc : sa.pc = blkPl07.base + BitVec.ofNat 64 30572) (hrun : sa.status = .Running)
    (hv0 : sa.readVReg128 0#5 = v0_in) (hv1 : sa.readVReg128 1#5 = v1_in)
    (hv5 : sa.readVReg128 5#5 = c3329Vec) (hv6 : sa.readVReg128 6#5 = c134215680Vec)
    (hv7 : sa.readVReg128 7#5 = c1664Vec) (hv16 : sa.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + offSeg4Store) sa P
      (fun s1 P1 =>
        s1.sp = sa.sp ∧ s1.spAligned = sa.spAligned ∧ s1.pstate = sa.pstate ∧
        (∀ r : Reg, s1.readReg64 r = sa.readReg64 r) ∧
        s1.readVReg128 1#5 = neonCompress8h 11 v0_in ∧
        s1.readVReg128 0#5 = neonCompress8h 11 v1_in ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c134215680Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧ P1 = P) := by
  wp_steps 6
  refine SepWP.mono (seg4_inner_simd_mid _ P
    (simdAdd8h (simdCmltZero8h v0_in &&& c3329Vec) v0_in)
    (simdAdd8h (simdCmltZero8h v1_in &&& c3329Vec) v1_in)
    (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp)
    (by simp [hv5]) (by simp [hv6]) (by simp [hv7]) (by simp [hv16])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  exact ⟨hsp1.trans (by simp), hspA1.trans (by simp), hpst1.trans (by simp),
    fun r => (hregs1 r).trans (by simp),
    hv1_1.trans (seg4_compress11_eq v0_in), hv0_1.trans (seg4_compress11_eq v1_in),
    hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩

private theorem seg4_inner_simd [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (22 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (28864 + 32 * c))
    (hx26 : s.readReg64 .x26 = sp + 32288#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c134215680Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Store) s
      (PolyMem (sp + 28848#64) (polyVecNat u) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = subsPState64 (BitVec.ofNat 64 (22 * (c + 1))) 352#64 ∧
        s1.readReg64 .x8 = BitVec.ofNat 64 (22 * (c + 1)) ∧
        s1.readReg64 .x9 = sp + BitVec.ofNat 64 (28864 + 32 * (c + 1)) ∧
        s1.readReg64 .x10 = sp + BitVec.ofNat 64 (32288 + 22 * c) ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s1.readReg64 r = s.readReg64 r) ∧
        s1.readVReg128 1#5 = neonCompress8h 11 (polyVecNat u (2 * c)) ∧
        s1.readVReg128 0#5 = neonCompress8h 11 (polyVecNat u (2 * c + 1)) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c134215680Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 28848#64) (polyVecNat u) ∗ Rest)) := by
  subst hbase
  have ha_ldp : (sp + 28848#64) + BitVec.ofNat 64 (16 * (2 * c)) =
      (sp + BitVec.ofNat 64 (28864 + 32 * c)) + 0xfffffffffffffff0#64 := by
    clear * - hc; bv_omega
  refine step_ldpQ128
    (s' := ((s.writeVReg128 0#5 (polyVecNat u (2 * c))).writeVReg128 1#5
      (polyVecNat u (2 * c + 1))).setPC (blkPl07.base + BitVec.ofNat 64 30556))
    (vt1 := 0#5) (vt2 := 1#5) (addr := .Offset .x9 0xfffffffffffffff0#64) (wb := none)
    hpc hrun (by simp only [arm64_norm]; rfl) rfl (by simp [evalAddrMode, hx9]) rfl
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c < 32) ha_ldp))
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c + 1 < 32)
      (by rw [← ha_ldp]; clear * -; bv_omega)))
    (by simp [applyWriteback, offSeg4Inner]) ?_
  wp_steps 4
  refine SepWP.mono
    (seg4_inner_simd_prep _ _ (polyVecNat u (2 * c)) (polyVecNat u (2 * c + 1))
      (by wp_norm_lhs) (by simp [hrun]) (by simp) (by simp)
      (by simp [hv5]) (by simp [hv6]) (by simp [hv7]) (by simp [hv16])) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  have h22 : BitVec.ofNat 64 (22 * c) + 22#64 = BitVec.ofNat 64 (22 * (c + 1)) := by
    clear * - hc; bv_omega
  have h32 : sp + BitVec.ofNat 64 (28864 + 32 * c) + 32#64 =
      sp + BitVec.ofNat 64 (28864 + 32 * (c + 1)) := by
    clear * - hc; bv_omega
  have h10 : sp + 32288#64 + BitVec.ofNat 64 (22 * c) =
      sp + BitVec.ofNat 64 (32288 + 22 * c) := by
    clear * - hc; bv_omega
  refine ⟨by simpa [hsp] using hsp1, by simpa using hspA1,
    by rw [hpst1]; simp only [arm64_norm]; exact congrArg (subsPState64 · 352#64) h22,
    by rw [hregs1]; simp only [arm64_norm]; exact h22,
    by rw [hregs1]; simp only [arm64_norm]; exact h32,
    by rw [hregs1]; simp only [arm64_norm]; exact h10,
    fun r h8 h9 h10 => ?_,
    hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  rw [hregs1]
  have hne8 : r ≠ .gpr 8#5 := h8; have hne9 : r ≠ .gpr 9#5 := h9; have hne10 : r ≠ .gpr 10#5 := h10
  simp only [arm64_norm, hne8, hne9, hne10, ite_self]

local macro "s4_strb " ea:term:arg hx10:term:arg hrun:term:arg
    pcOff:num nextOff:num k:num rt:term:arg : tactic => `(tactic|
  (refine step_str8_byteRange blkPl07.base $ea $pcOff $nextOff 22 $k .x10 $rt _ _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp) rfl
      (by simp [$hx10:term]) rfl rfl ?_;
   intro _))

local macro "s4_strb_simd " ea:term:arg hx10:term:arg hrun:term:arg
    pcOff:num nextOff:num k:num vt:term:arg addr:term:arg : tactic => `(tactic|
  (refine step_strSimd8_byteRange blkPl07.base $ea $pcOff $nextOff 22 $k $vt $addr _ _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp) rfl
      (by simp [evalAddrMode, $hx10:term]) rfl rfl ?_;
   intro _))

private theorem trunc32_zext64_shl (x : BitVec 16) (n : Nat) :
    ((x.zeroExtend 64) <<< n).truncate 32 = (x.zeroExtend 32) <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, hi, show i < 64 by omega, decide_true, Bool.true_and]
  by_cases hn : i < n
  · simp [hn]
  · simp [hn, show i - n < 32 by omega, show i - n < 64 by omega]

private theorem trunc32_zext64_shr (x : BitVec 16) (n : Nat) :
    ((x.zeroExtend 64) >>> n).truncate 32 = (x.zeroExtend 32) >>> n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h16 : n + i < 16
  · simp [h16, show n + i < 32 by omega, show n + i < 64 by omega]
  · simp [BitVec.getLsbD_of_ge, show 16 ≤ n + i by omega]

set_option maxRecDepth 8000 in
private theorem seg4_inner_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (ea : BitVec 64) (vFirst vSecond : BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Store) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 = ea)
    (hv1 : s.readVReg128 1#5 = vFirst) (hv0 : s.readVReg128 0#5 = vSecond)
    (hm1 : ∀ j : Fin 8, lane16 vFirst j &&& 0x07ff#16 = lane16 vFirst j)
    (hm0 : ∀ j : Fin 8, lane16 vSecond j &&& 0x07ff#16 = lane16 vSecond j) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 30972) s
      (memRegion ea 22 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        (∀ r : Reg, r = .x8 ∨ r = .x9 ∨ r = .x10 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
          r = .x22 ∨ r = .x23 ∨ r = .x25 ∨ r = .x26 ∨ r = .x27 ∨ r = .fp →
          s2.readReg64 r = s.readReg64 r) ∧
        s2.readVReg128 5#5 = s.readVReg128 5#5 ∧ s2.readVReg128 6#5 = s.readVReg128 6#5 ∧
        s2.readVReg128 7#5 = s.readVReg128 7#5 ∧ s2.readVReg128 16#5 = s.readVReg128 16#5 ∧
        (P2 ⊢ (ea ↦ₛ neonSerialize11Bytes vFirst vSecond) ∗ Rest)) := by
  subst hbase
  apply sepWP_elim_byteRange 22 (by decide); intro f0
  wp_steps 17
  s4_strb_simd ea hx10 hrun 30760 30764 0 1#5 (.Offset .x10 0#64)
  s4_strb ea hx10 hrun 30764 30768 7 .x7
  wp_steps 2; s4_strb ea hx10 hrun 30776 30780 10 .x28
  wp_steps 2; s4_strb ea hx10 hrun 30788 30792 12 .x3
  wp_steps 5; s4_strb ea hx10 hrun 30812 30816 1 .x4
  wp_steps 2; s4_strb ea hx10 hrun 30824 30828 3 .x5
  wp_steps 2; s4_strb ea hx10 hrun 30836 30840 2 .x14
  wp_steps 2; s4_strb ea hx10 hrun 30848 30852 5 .x16
  wp_steps 3; s4_strb ea hx10 hrun 30864 30868 6 .x17
  wp_steps 1; s4_strb ea hx10 hrun 30872 30876 8 .x15
  wp_steps 3; s4_strb ea hx10 hrun 30888 30892 9 .x14
  wp_steps 7; s4_strb ea hx10 hrun 30920 30924 16 .x11
  wp_steps 1; s4_strb ea hx10 hrun 30928 30932 17 .x13
  wp_steps 1; s4_strb_simd ea hx10 hrun 30936 30940 11 0#5 (.UnscaledOffset .x10 11#64)
  s4_strb ea hx10 hrun 30940 30944 14 .lr
  s4_strb ea hx10 hrun 30944 30948 18 .x24
  s4_strb ea hx10 hrun 30948 30952 4 .x28
  s4_strb ea hx10 hrun 30952 30956 13 .x18
  s4_strb ea hx10 hrun 30956 30960 15 .x16
  s4_strb ea hx10 hrun 30960 30964 19 .x12
  s4_strb ea hx10 hrun 30964 30968 20 .x11
  s4_strb ea hx10 hrun 30968 30972 21 .x13
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp [State.spAligned], by simp,
      by rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp,
      by simp, by simp, by simp, by simp, ?_⟩
  rw [byteRangeMem_split11, byteRangeMem11_eq_cells, byteRangeMem11_eq_cells]
  simp only [arm64_norm, Function.update, Nat.reduceEqDiff, hv1, hv0,
    trunc32_zext64_shl, trunc32_zext64_shr]
  simp only [ser11_b0 vFirst (hm1 0), ser11_b0 vSecond (hm0 0),
    ser11_lsr _ 1 (hm1 5) (Or.inl rfl), ser11_lsr _ 2 (hm1 2) (Or.inr (Or.inl rfl)),
    ser11_lsr _ 3 (hm1 7) (Or.inr (Or.inr rfl)),
    ser11_lsr _ 1 (hm0 5) (Or.inl rfl), ser11_lsr _ 2 (hm0 2) (Or.inr (Or.inl rfl)),
    ser11_lsr _ 3 (hm0 7) (Or.inr (Or.inr rfl)),
    ser11_shl_lsr _ _ 6 5 (hm1 1) (hm1 2) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 4 7 (hm1 3) (hm1 4) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 7 4 (hm1 4) (hm1 5) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 5 6 (hm1 6) (hm1 7) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 6 5 (hm0 1) (hm0 2) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 4 7 (hm0 3) (hm0 4) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 7 4 (hm0 4) (hm0 5) rfl (by decide) (by decide),
    ser11_shl_lsr _ _ 5 6 (hm0 6) (hm0 7) rfl (by decide) (by decide)]
  rw [← cells22_eq_neonSerialize11Bytes, ← cells11_eq_neonSerialize11Half ea vFirst,
      ← cells11_eq_neonSerialize11Half (ea + 11#64) vSecond]
  sep_frame


private theorem seg4_inner_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Inner) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (22 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (28864 + 32 * c))
    (hx26 : s.readReg64 .x26 = sp + 32288#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c134215680Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if c + 1 < 16 then b + offSeg4Inner else b + offSeg4Bounce) s
      (PolyMem (sp + 28848#64) (polyVecNat u) ∗
        memRegion (sp + BitVec.ofNat 64 (32288 + 22 * c)) 22 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (22 * (c + 1)) ∧
        sf.readReg64 .x9 = sp + BitVec.ofNat 64 (28864 + 32 * (c + 1)) ∧
        (∀ r : Reg, r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨
          r = .x25 ∨ r = .x26 ∨ r = .x27 ∨ r = .fp → sf.readReg64 r = s.readReg64 r) ∧
        sf.readVReg128 5#5 = c3329Vec ∧ sf.readVReg128 6#5 = c134215680Vec ∧
        sf.readVReg128 7#5 = c1664Vec ∧ sf.readVReg128 16#5 = c10321340Vec ∧
        (Pf ⊢ PolyMem (sp + 28848#64) (polyVecNat u) ∗
          ((sp + BitVec.ofNat 64 (32288 + 22 * c)) ↦ₛ
            neonSerialize11Bytes (neonCompress8h 11 (polyVecNat u (2 * c)))
              (neonCompress8h 11 (polyVecNat u (2 * c + 1)))) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro
    (seg4_inner_simd hb hbase s sp hc u _ hpc hrun hsp hx8 hx9 hx26 hv5 hv6 hv7 hv16) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hregs1, hv1_1, hv0_1, hv5_1, hv6_1, hv7_1, hv16_1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (SepWP.weaken_pre
      (show PolyMem (sp + 28848#64) (polyVecNat u) ∗ (memRegion _ 22 ∗ Rest) ⊢
          memRegion _ 22 ∗ (PolyMem (sp + 28848#64) (polyVecNat u) ∗ Rest) by sep_frame)
      (seg4_inner_store hb hbase s1 _ _ _ _ hpc1 hrun1 hx10_1 hv1_1 hv0_1
        (fun j => lane16_neonCompress8h_11_mask _ j)
        (fun j => lane16_neonCompress8h_11_mask _ j))) ?_
  rintro s2 P2 hpc2 hrun2 _ _ ⟨hsp2, hspA2, hpst2, hregs2, hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  subst hbase
  have hspA2' : s2.spAligned = true := hspA2.trans (hspA1.trans hspA)
  by_cases hlt : c + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have htaken : ConditionHolds .NE s2.pstate = true := by
      rw [hpst2, hpst1, conditionHolds_ne_subsPState64]
      rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
      all_goals decide
    refine step_bCond_taken (dst := blkPl07.base + offSeg4Inner)
      hpc2 hrun2 (by wp_norm_lhs) htaken (by clear * -; dsimp [offSeg4Inner]; bv_omega) ?_
    refine SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2, hsp1], spAligned_of_sp_eq hspA2' (hsp2.trans hsp1) (by simp [hsp2, hsp1]),
        by simp [hregs2 .x8 (Or.inl rfl), hx8_1],
        by simp [hregs2 .x9 (Or.inr (Or.inl rfl)), hx9_1],
        by rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
             (simp; rw [hregs2 _ (by simp), hregs1 _ (by decide) (by decide) (by decide)]),
        by simp [hv5_2, hv5_1], by simp [hv6_2, hv6_1],
        by simp [hv7_2, hv7_1], by simp [hv16_2, hv16_1],
        Entails.trans hP2 (by sep_frame)⟩
  · simp only [hlt, ↓reduceIte]
    have hc15 : c = 15 := by omega
    subst hc15
    have hnot : ConditionHolds .NE s2.pstate = false := by
      rw [hpst2, hpst1, conditionHolds_ne_subsPState64]; decide
    refine step_bCond_not_taken (dst := blkPl07.base + offSeg4Bounce)
      hpc2 hrun2 (by wp_norm_lhs) hnot (by clear * -; dsimp [offSeg4Bounce]; bv_omega) ?_
    refine SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2, hsp1], spAligned_of_sp_eq hspA2' (hsp2.trans hsp1) (by simp [hsp2, hsp1]),
        by simp [hregs2 .x8 (Or.inl rfl), hx8_1],
        by simp [hregs2 .x9 (Or.inr (Or.inl rfl)), hx9_1],
        by rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
             (simp; rw [hregs2 _ (by simp), hregs1 _ (by decide) (by decide) (by decide)]),
        by simp [hv5_2, hv5_1], by simp [hv6_2, hv6_1],
        by simp [hv7_2, hv7_1], by simp [hv16_2, hv16_1],
        Entails.trans hP2 (by sep_frame)⟩

private theorem seg4_inner_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp : BitVec 64) (u : Poly16) :
    ∀ (rem c : Nat), c + rem = 15 → ∀ (s : State) (Rest : SepProp),
      s.pc = b + offSeg4Inner → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 (22 * c) →
      s.readReg64 .x9 = sp + BitVec.ofNat 64 (28864 + 32 * c) →
      s.readReg64 .x26 = sp + 32288#64 →
      s.readVReg128 5#5 = c3329Vec → s.readVReg128 6#5 = c134215680Vec →
      s.readVReg128 7#5 = c1664Vec → s.readVReg128 16#5 = c10321340Vec →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Bounce) s
        (PolyMem (sp + 28848#64) (polyVecNat u) ∗
          ((sp + 32288#64) ↦ₛ ser11Prefix u c) ∗
          memRegion (sp + BitVec.ofNat 64 (32288 + 22 * c)) (22 * (16 - c)) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          (∀ r : Reg, r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨
            r = .x25 ∨ r = .x26 ∨ r = .x27 ∨ r = .fp → sf.readReg64 r = s.readReg64 r) ∧
          (Pf ⊢ PolyMem (sp + 28848#64) (polyVecNat u) ∗
            ((sp + 32288#64) ↦ₛ neonCompressSerialize11Poly u) ∗ Rest))
  | 0, c, _hrem, s, Rest, hpc, hrun, hsp, hspA, hcl, hro, hx8, hx9, hx26, hv5, hv6, hv7, hv16 => by
    have hc15 : c = 15 := by omega
    subst hc15
    have hstep := seg4_inner_iter hb hbase s sp (by decide : 15 < 16) u
      (((sp + 32288#64) ↦ₛ ser11Prefix u 15) ∗ Rest)
      hpc hrun hsp hspA hcl hro hx8 hx9 hx26 hv5 hv6 hv7 hv16
    simp only [show ¬ (15 + 1 < 16) by decide, ↓reduceIte,
      show 22 * (16 - 15) = 22 by decide] at hstep ⊢
    refine SepWP.weaken_pre (by sep_frame) (SepWP.mono hstep ?_)
    rintro sf Pf _ _ ⟨hsp', hspA', _, _, hregs', _, _, _, _, hPf⟩
    refine ⟨hsp', hspA', hregs', Entails.trans hPf ?_⟩
    rw [← ser11Prefix_sixteen u, ser11Prefix_succ u 15, pointsToBytes_append, ser11Prefix_length u 15,
      ser11Chunk,
      show (sp + 32288#64) + BitVec.ofNat 64 (22 * 15) = sp + BitVec.ofNat 64 (32288 + 22 * 15) by
        clear * -; bv_omega]
    sep_frame
  | rem + 1, c, _hrem, s, Rest, hpc, hrun, hsp, hspA, hcl, hro, hx8, hx9, hx26, hv5, hv6, hv7, hv16 => by
    have hc15 : c + 1 < 16 := by omega
    have hsplit : memRegion (sp + BitVec.ofNat 64 (32288 + 22 * c)) (22 * (16 - c)) =
        memRegion (sp + BitVec.ofNat 64 (32288 + 22 * c)) 22 ∗
          memRegion (sp + BitVec.ofNat 64 (32288 + 22 * (c + 1))) (22 * (16 - (c + 1))) :=
      memRegion_split' (b := sp + BitVec.ofNat 64 (32288 + 22 * c))
        (b' := sp + BitVec.ofNat 64 (32288 + 22 * (c + 1))) (n := 22)
        (k := (22 * (16 - (c + 1)) : Nat)) (by omega)
        (by rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
            all_goals (clear * -; bv_omega))
        (by omega)
    rw [hsplit]
    have hstep := seg4_inner_iter hb hbase s sp (by omega : c < 16) u
      (((sp + 32288#64) ↦ₛ ser11Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (32288 + 22 * (c + 1))) (22 * (16 - (c + 1))) ∗ Rest)
      hpc hrun hsp hspA hcl hro hx8 hx9 hx26 hv5 hv6 hv7 hv16
    simp only [hc15, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro (SepWP.weaken_pre (by sep_frame) hstep) ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx8_1, hx9_1, hregs1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
    have hjoin : ((sp + 32288#64) ↦ₛ ser11Prefix u (c + 1)) =
        ((sp + 32288#64) ↦ₛ ser11Prefix u c) ∗
          ((sp + BitVec.ofNat 64 (32288 + 22 * c)) ↦ₛ
            neonSerialize11Bytes (neonCompress8h 11 (polyVecNat u (2 * c)))
              (neonCompress8h 11 (polyVecNat u (2 * c + 1)))) := by
      have ha : (sp + 32288#64) + BitVec.ofNat 64 (22 * c) = sp + BitVec.ofNat 64 (32288 + 22 * c) := by
        rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
        all_goals (clear * -; bv_omega)
      rw [ser11Prefix_succ u c, pointsToBytes_append, ser11Prefix_length u c, ser11Chunk, ha]
    refine SepWP.weaken_pre (Entails.trans hP1 (by rw [hjoin]; sep_frame))
      (SepWP.mono (seg4_inner_loop hb hbase sp u rem (c + 1) (by omega) s1 Rest
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1
        ((hregs1 .x26 (by simp)).trans hx26) hv5_1 hv6_1 hv7_1 hv16_1) ?_)
    rintro sf Pf _ _ ⟨hsp', hspA', hregs', hPf⟩
    exact ⟨hsp', hspA', fun r hr => (hregs' r hr).trans (hregs1 r hr), hPf⟩

/-! ## 5. Outer-Loop Bounce (`+0x7900 → +0x768c / +0x7934`), `r̂` Copy, & `seg4_compress_ok` -/

private theorem seg4_bounce [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) {idx : Nat} (hidx : idx < 4) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Bounce) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hx20 : s.readReg64 .x20 = sp + 12848#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (352 * idx))
    (hx22 : s.readReg64 .x22 = sp + 28848#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (idx + 1))
    (hx25 : s.readReg64 .x25 = 352#64) (hx26 : s.readReg64 .x26 = sp + 32288#64)
    (hx27 : s.readReg64 .x27 = sp + 23104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let dst := sp + BitVec.ofNat 64 (23104 + 352 * idx)
    SepWP (blkPC07.rebase b (fun _ => none))
      (if idx + 1 < 4 then b + offSeg4Outer else b + offSeg4RhatCopy) s
      (((sp + 32288#64) ↦ₛ neonCompressSerialize11Poly u) ∗
        memRegion (sp + 31936#64) 352 ∗ memRegion dst 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x20 = sp + 12848#64 ∧ sf.readReg64 .x22 = sp + 28848#64 ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x25 = 352#64 ∧
        sf.readReg64 .x26 = sp + 32288#64 ∧ sf.readReg64 .x27 = sp + 23104#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ (dst ↦ₛ neonCompressSerialize11Poly u) ∗
          memRegion (sp + 31936#64) 352 ∗ memRegion (sp + 32288#64) 352 ∗ Rest)) := by
  subst hbase; intro dst
  generalize hc1_def : neonCompressSerialize11Poly u = c1
  have hc1 : c1.length = 352 := by rw [← hc1_def]; exact neonCompressSerialize11Poly_length u
  have hdst_eq : (sp + 23104#64) + BitVec.ofNat 64 (352 * idx) = dst := by
    dsimp only [dst]; rcases idx with _ | _ | _ | _ | n <;> try omega
    all_goals (clear * -; bv_omega)
  refine SepWP.weaken_pre
    (show _ ⊢ ((sp + 32288#64) ↦ₛ c1) ∗ memRegion (sp + 31936#64) 352 ∗ (memRegion dst 352 ∗ Rest) by
      sep_frame) ?_
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 31936#64, sp + 32288#64, c1)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hm32288 : ((sp + 32288#64) ↦ₛ c1) ⊢ memRegion (sp + 32288#64) 352 := by
    rw [← hc1]; exact pointsToBytes_entails_memRegion (sp + 32288#64) c1
  refine SepWP.weaken_pre
    (P' := ((sp + 31936#64) ↦ₛ c1) ∗ memRegion dst 352 ∗ (memRegion (sp + 32288#64) 352 ∗ Rest))
    (entails_sub hm32288 (by sep_frame) (by sep_frame)) ?_
  wp_steps 4; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl1)
  wp_call (blk28_memcpy_07 blkPl07.base) (dst, sp + 31936#64, c1)
  apply SepWP.done (by assumption) (by assumption); intro hcl2
  have hsp2 : sf_1.sp = sp := by simp [*]
  have hspA2 : sf_1.spAligned = true := spAligned_of_sp_eq hspA hsp hsp2
  have hfp2 : sf_1.readReg64 .fp = fpVal := hcs_sf_1.trans (hcs_sf.trans hfp)
  have hm31936 : ((sp + 31936#64) ↦ₛ c1) ⊢ memRegion (sp + 31936#64) 352 := by
    rw [← hc1]; exact pointsToBytes_entails_memRegion (sp + 31936#64) c1
  wp_steps 1
  by_cases hlt : idx + 1 < 4
  · simp only [hlt, ↓reduceIte]
    have htaken : ConditionHolds .NE (subsPState64 (BitVec.ofNat 64 (idx + 1)) 4#64) = true := by
      rw [conditionHolds_ne_subsPState64]
      rcases idx with _ | _ | _ | n <;> try omega
      all_goals decide
    refine step_bCond_taken (dst := blkPl07.base + offSeg4Outer)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by wp_norm_lhs)
      (by simp [htaken]) (by clear * -; dsimp [offSeg4Outer]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun_sf_1])
      ⟨by simp [hsp2], spAligned_of_sp_eq hspA2 hsp2 (by simp [hsp2]),
        by simp [h_11, h, hx19], by simp [hfp2],
        by simp [h_12, h_1, hx20], by simp [h_14, h_3, hx22],
        by simp [h_15, h_4, hx23], by simp [h_17, h_6, hx25],
        by simp [h_18, h_7, hx26], by simp [h_19, h_8, hx27], by simpa using hcl2,
        entails_sub hm31936 (by sep_frame) (by sep_frame)⟩
  · simp only [hlt, ↓reduceIte]
    have hidx3 : idx = 3 := by omega
    subst hidx3
    have hnot : ConditionHolds .NE (subsPState64 (BitVec.ofNat 64 (3 + 1)) 4#64) = false := by
      rw [conditionHolds_ne_subsPState64]; decide
    refine step_bCond_not_taken (dst := blkPl07.base + offSeg4RhatCopy)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by wp_norm_lhs)
      (by simp [hnot]) (by clear * -; dsimp [offSeg4RhatCopy]; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun_sf_1])
      ⟨by simp [hsp2], spAligned_of_sp_eq hspA2 hsp2 (by simp [hsp2]),
        by simp [h_11, h, hx19], by simp [hfp2],
        by simp [h_12, h_1, hx20], by simp [h_14, h_3, hx22],
        by simp [h_15, h_4, hx23], by simp [h_17, h_6, hx25],
        by simp [h_18, h_7, hx26], by simp [h_19, h_8, hx27], by simpa using hcl2,
        entails_sub hm31936 (by sep_frame) (by sep_frame)⟩

private theorem seg4_outer_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) {idx : Nat} (hidx : idx < 4) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hx20 : s.readReg64 .x20 = sp + 12848#64) (hx22 : s.readReg64 .x22 = sp + 28848#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 idx) (hx25 : s.readReg64 .x25 = 352#64)
    (hx26 : s.readReg64 .x26 = sp + 32288#64) (hx27 : s.readReg64 .x27 = sp + 23104#64) :
    let uPtr := sp + BitVec.ofNat 64 (12848 + 512 * idx)
    let dst := sp + BitVec.ofNat 64 (23104 + 352 * idx)
    SepWP (blkPC07.rebase b (fun _ => none))
      (if idx + 1 < 4 then b + offSeg4Outer else b + offSeg4RhatCopy) s
      (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
        PolyMem uPtr (polyVecNat u) ∗ memRegion dst 352 ∗
        memRegion (sp + 28848#64) 520 ∗ memRegion (sp + 31408#64) 520 ∗
        memRegion (sp + 31936#64) 352 ∗ memRegion (sp + 32288#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x20 = sp + 12848#64 ∧ sf.readReg64 .x22 = sp + 28848#64 ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x25 = 352#64 ∧
        sf.readReg64 .x26 = sp + 32288#64 ∧ sf.readReg64 .x27 = sp + 23104#64 ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
          PolyMem uPtr (polyVecNat u) ∗ (dst ↦ₛ neonCompressSerialize11Poly u) ∗
          memRegion (sp + 28848#64) 520 ∗ memRegion (sp + 31408#64) 520 ∗
          memRegion (sp + 31936#64) 352 ∗ memRegion (sp + 32288#64) 352 ∗ Rest)) := by
  intro uPtr dst
  refine sepWP_seq_env hcl hro
    (SepWP.weaken_pre (by sep_frame)
      (seg4_prep_poly hb hbase s sp x19Val fpVal hidx u
        (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion dst 352 ∗
          memRegion (sp + 31936#64) 352 ∗ memRegion (sp + 32288#64) 352 ∗ Rest)
        hpc hrun hsp hspA hx19 hfp hx20 hx22 hx23 hx25 hx26 hx27 hcl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx19_1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, _, hP1⟩
  refine sepWP_seq_env hcl1 hro1
    (SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
      (seg4_zero_load hb hbase s1 sp x19Val fpVal _ hpc1 hrun1 hsp1 hspA1 hx19_1 hfp1 hx22_1)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx19_2, hfp2, hx8_2, hx9_2, hx20_2, hx21_2, hx22_2, hx23_2,
      hx25_2, hx26_2, hx27_2, hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  have hx26_2' : s2.readReg64 .x26 = sp + 32288#64 := hx26_2.trans hx26_1
  have hloop := seg4_inner_loop hb hbase sp u 15 0 rfl s2
    (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
      memRegion dst 352 ∗ memRegion (sp + 29360#64) 8 ∗ memRegion (sp + 31408#64) 520 ∗
      memRegion (sp + 31936#64) 352 ∗ Rest)
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx9_2 hx26_2' hv5_2 hv6_2 hv7_2 hv16_2
  simp only [show ser11Prefix u 0 = [] from rfl, pointsToBytes_nil, emp_sepConj,
    show 22 * (16 - 0) = 352 by decide,
    show sp + BitVec.ofNat 64 (32288 + 22 * 0) = sp + 32288#64 by clear * -; bv_omega] at hloop
  refine sepWP_seq_env hcl2 hro2
    (SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) hloop) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 _hro3 ⟨hsp3, hspA3, hregs3, hP3⟩
  have h520 : PolyMem (sp + 28848#64) (polyVecNat u) ∗ memRegion (sp + 29360#64) 8 ⊢
      memRegion (sp + 28848#64) 520 := by
    rw [memRegion_split' (b := sp + 28848#64) (b' := sp + 29360#64) (n := 512) (k := (8 : Nat))
      rfl (by clear * -; bv_omega) (by decide)]
    have hpm : PolyMem (sp + 28848#64) (polyVecNat u) ⊢ memRegion (sp + 28848#64) 512 :=
      vecRangeMem_entails_memRegion 32 (sp + 28848#64) (polyVecNat u)
    exact entails_sub hpm (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre (Entails.trans hP3 (entails_sub h520 (by sep_frame) (by sep_frame)))
    (SepWP.mono (seg4_bounce hb hbase s3 sp x19Val fpVal hidx u _ hpc3 hrun3 hsp3 hspA3
      ((hregs3 .x19 (by simp)).trans hx19_2) ((hregs3 .fp (by simp)).trans hfp2)
      ((hregs3 .x20 (by simp)).trans (hx20_2.trans hx20_1))
      ((hregs3 .x21 (by simp)).trans (hx21_2.trans hx21_1))
      ((hregs3 .x22 (by simp)).trans hx22_2)
      ((hregs3 .x23 (by simp)).trans (hx23_2.trans hx23_1))
      ((hregs3 .x25 (by simp)).trans (hx25_2.trans hx25_1))
      ((hregs3 .x26 (by simp)).trans hx26_2')
      ((hregs3 .x27 (by simp)).trans (hx27_2.trans hx27_1)) hcl3) ?_)
  rintro sf Pf _ _ ⟨hsp', hspA', hx19', hfp', hx20', hx22', hx23', hx25', hx26', hx27', _, hPf⟩
  exact ⟨hsp', hspA', hx19', hfp', hx20', hx22', hx23', hx25', hx26', hx27',
    Entails.trans hPf (by sep_frame)⟩

private theorem seg4_rhat_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64) (r0 r1 r2 r3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4RhatCopy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Start) s
      (PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        memRegion (sp + 12832#64) 2048 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .x20 = sp + 12832#64 ∧
        sf.readReg64 .fp = fpVal ∧
        (Pf ⊢ PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
          PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
          memRegion (sp + 24720#64) 2048 ∗ Rest)) := by
  subst hbase
  generalize hbsR_def : vecRangeBytes 32 (polyVecNat r0) ++ vecRangeBytes 32 (polyVecNat r1) ++
    vecRangeBytes 32 (polyVecNat r2) ++ vecRangeBytes 32 (polyVecNat r3) = bsR
  have hbsR : bsR.length = 2048 := by rw [← hbsR_def]; simp [List.length_append, vecRangeBytes_length]
  have hpSrc := polyMem4_eq_pointsToBytes (sp + 24720#64) r0 r1 r2 r3
  have hpDst := polyMem4_eq_pointsToBytes (sp + 12832#64) r0 r1 r2 r3
  rw [hbsR_def] at hpSrc hpDst
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpSrc hpDst
  refine SepWP.weaken_pre
    (show _ ⊢ ((sp + 24720#64) ↦ₛ bsR) ∗ memRegion (sp + 12832#64) 2048 ∗ Rest by
      rw [← hpSrc]; sep_frame) ?_
  wp_steps 7; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl)
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 12832#64, sp + 24720#64, bsR)
  apply SepWP.done (by assumption) (by assumption); intro _hcl1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*], by simp [*], ?_⟩
  have hmSrc : ((sp + 24720#64) ↦ₛ bsR) ⊢ memRegion (sp + 24720#64) 2048 := by
    rw [← hbsR]; exact pointsToBytes_entails_memRegion (sp + 24720#64) bsR
  have hpDst' : ((sp + 12832#64) ↦ₛ bsR) ⊢
      PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
        PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) := by
    rw [← hpDst]; exact Entails.refl _
  exact entails_sub hpDst' (by sep_frame) (entails_sub hmSrc (by sep_frame) (by sep_frame))

private theorem polyMem4_12848_entails_memRegion (sp : BitVec 64) (u0 u1 u2 u3 : Poly16) :
    PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13360#64) (polyVecNat u1) ∗
      PolyMem (sp + 13872#64) (polyVecNat u2) ∗ PolyMem (sp + 14384#64) (polyVecNat u3) ⊢
      memRegion (sp + 12848#64) 2048 := by
  have hp := polyMem4_eq_pointsToBytes (sp + 12848#64) u0 u1 u2 u3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp
  rw [hp]
  have hlen : (vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
      vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3)).length = 2048 := by
    simp [List.length_append, vecRangeBytes_length]
  rw [← hlen]
  exact pointsToBytes_entails_memRegion (sp + 12848#64) _

theorem seg4_compress_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp x19Val fpVal : BitVec 64)
    (u0 u1 u2 u3 r0 r1 r2 r3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4RowsEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Start) s
      (memRegion (sp + 2368#64) 64 ∗
        memRegion (sp + 12832#64) 2072 ∗
        memRegion (sp + 23104#64) 1408 ∗
        PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
        PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
        PolyMem (sp + 28848#64) (polyVecNat u0) ∗ PolyMem (sp + 29360#64) (polyVecNat u1) ∗
        PolyMem (sp + 29872#64) (polyVecNat u2) ∗ PolyMem (sp + 30384#64) (polyVecNat u3) ∗
        memRegion (sp + 31408#64) 1232 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .x20 = sp + 12832#64 ∧
        sf.readReg64 .fp = fpVal ∧
        (Pf ⊢ memRegion (sp + 2368#64) 64 ∗
          PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
          PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
          memRegion (sp + 14880#64) 24 ∗
          ((sp + 23104#64) ↦ₛ (neonCompressSerialize11Poly u0 ++ neonCompressSerialize11Poly u1 ++
            neonCompressSerialize11Poly u2 ++ neonCompressSerialize11Poly u3)) ∗
          memRegion (sp + 24720#64) 2048 ∗
          memRegion (sp + 28848#64) 2048 ∗
          memRegion (sp + 31408#64) 1232 ∗ Rest)) := by
  have hm12832_in : memRegion (sp + 12832#64) 2072 =
      memRegion (sp + 12832#64) 8 ∗ memRegion (sp + 12840#64) 8 ∗
        memRegion (sp + 12848#64) 2048 ∗ memRegion (sp + 14896#64) 8 := by
    rw [memRegion_split' (b := sp + 12832#64) (b' := sp + 12840#64) (n := 8) (k := (2064 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 12840#64) (b' := sp + 12848#64) (n := 8) (k := (2056 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 12848#64) (b' := sp + 14896#64) (n := 2048) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm23104 : memRegion (sp + 23104#64) 1408 =
      memRegion (sp + 23104#64) 352 ∗ memRegion (sp + 23456#64) 352 ∗
        memRegion (sp + 23808#64) 352 ∗ memRegion (sp + 24160#64) 352 := by
    rw [memRegion_split' (b := sp + 23104#64) (b' := sp + 23456#64) (n := 352) (k := (1056 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 23456#64) (b' := sp + 23808#64) (n := 352) (k := (704 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 23808#64) (b' := sp + 24160#64) (n := 352) (k := (352 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm31408 : memRegion (sp + 31408#64) 1232 =
      memRegion (sp + 31408#64) 520 ∗ memRegion (sp + 31928#64) 8 ∗
        memRegion (sp + 31936#64) 352 ∗ memRegion (sp + 32288#64) 352 := by
    rw [memRegion_split' (b := sp + 31408#64) (b' := sp + 31928#64) (n := 520) (k := (712 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 31928#64) (b' := sp + 31936#64) (n := 8) (k := (704 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 31936#64) (b' := sp + 32288#64) (n := 352) (k := (352 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm28848_split : memRegion (sp + 28848#64) 2048 =
      memRegion (sp + 28848#64) 520 ∗ memRegion (sp + 29368#64) 1528 :=
    memRegion_split' (b := sp + 28848#64) (b' := sp + 29368#64) (n := 520) (k := (1528 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  rw [hm12832_in, hm23104, hm31408]
  refine sepWP_seq_env hcl hro
    (SepWP.weaken_pre (by sep_frame)
      (seg4_uvec_copy hb hbase s sp x19Val fpVal u0 u1 u2 u3 _ hpc hrun hsp hspA hx19 hfp hcl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hfp1, hx20_1, hx22_1, _, hP1⟩
  refine sepWP_seq_env hcl1 hro1
    (SepWP.weaken_pre (Entails.trans hP1 (by rw [hm28848_split]; sep_frame))
      (seg4_header hb hbase s1 sp x19Val fpVal _ hpc1 hrun1 hsp1 hspA1 hx19_1 hfp1 hx20_1 hx22_1)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx19_2, hfp2, hx20_2, hx22_2, hx23_2, hx25_2, hx26_2, hx27_2, hP2⟩
  let F : SepProp := memRegion (sp + 12840#64) 8 ∗ memRegion (sp + 14896#64) 8 ∗
    memRegion (sp + 29368#64) 1528 ∗ memRegion (sp + 12832#64) 8 ∗
    PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
    PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
    memRegion (sp + 31928#64) 8 ∗ Rest
  have hit0 := seg4_outer_iter hb hbase s2 sp x19Val fpVal (by decide : 0 < 4) u0
    (PolyMem (sp + 13360#64) (polyVecNat u1) ∗ PolyMem (sp + 13872#64) (polyVecNat u2) ∗
      PolyMem (sp + 14384#64) (polyVecNat u3) ∗ memRegion (sp + 23456#64) 352 ∗
      memRegion (sp + 23808#64) 352 ∗ memRegion (sp + 24160#64) 352 ∗ F)
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx19_2 hfp2 hx20_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2
  dsimp only at hit0
  simp only [show 0 + 1 < 4 by decide, ↓reduceIte,
    show sp + BitVec.ofNat 64 (12848 + 512 * 0) = sp + 12848#64 by rfl,
    show sp + BitVec.ofNat 64 (23104 + 352 * 0) = sp + 23104#64 by rfl] at hit0
  refine sepWP_seq_env hcl2 hro2 (SepWP.weaken_pre (Entails.trans hP2 (by dsimp only [F]; sep_frame)) hit0) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx19_3, hfp3, hx20_3, hx22_3, hx23_3, hx25_3, hx26_3, hx27_3, hP3⟩
  have hit1 := seg4_outer_iter hb hbase s3 sp x19Val fpVal (by decide : 1 < 4) u1
    (PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13872#64) (polyVecNat u2) ∗
      PolyMem (sp + 14384#64) (polyVecNat u3) ∗ ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      memRegion (sp + 23808#64) 352 ∗ memRegion (sp + 24160#64) 352 ∗ F)
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx19_3 hfp3 hx20_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3
  dsimp only at hit1
  simp only [show 1 + 1 < 4 by decide, ↓reduceIte,
    show sp + BitVec.ofNat 64 (12848 + 512 * 1) = sp + 13360#64 by rfl,
    show sp + BitVec.ofNat 64 (23104 + 352 * 1) = sp + 23456#64 by rfl] at hit1
  refine sepWP_seq_env hcl3 hro3 (SepWP.weaken_pre (Entails.trans hP3 (by sep_frame)) hit1) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx19_4, hfp4, hx20_4, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4, hP4⟩
  have hit2 := seg4_outer_iter hb hbase s4 sp x19Val fpVal (by decide : 2 < 4) u2
    (PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13360#64) (polyVecNat u1) ∗
      PolyMem (sp + 14384#64) (polyVecNat u3) ∗ ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      ((sp + 23456#64) ↦ₛ neonCompressSerialize11Poly u1) ∗ memRegion (sp + 24160#64) 352 ∗ F)
    hpc4 hrun4 hsp4 hspA4 hcl4 hro4 hx19_4 hfp4 hx20_4 hx22_4 hx23_4 hx25_4 hx26_4 hx27_4
  dsimp only at hit2
  simp only [show 2 + 1 < 4 by decide, ↓reduceIte,
    show sp + BitVec.ofNat 64 (12848 + 512 * 2) = sp + 13872#64 by rfl,
    show sp + BitVec.ofNat 64 (23104 + 352 * 2) = sp + 23808#64 by rfl] at hit2
  refine sepWP_seq_env hcl4 hro4 (SepWP.weaken_pre (Entails.trans hP4 (by sep_frame)) hit2) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspA5, hx19_5, hfp5, hx20_5, hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hP5⟩
  have hit3 := seg4_outer_iter hb hbase s5 sp x19Val fpVal (by decide : 3 < 4) u3
    (PolyMem (sp + 12848#64) (polyVecNat u0) ∗ PolyMem (sp + 13360#64) (polyVecNat u1) ∗
      PolyMem (sp + 13872#64) (polyVecNat u2) ∗ ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      ((sp + 23456#64) ↦ₛ neonCompressSerialize11Poly u1) ∗
      ((sp + 23808#64) ↦ₛ neonCompressSerialize11Poly u2) ∗ F)
    hpc5 hrun5 hsp5 hspA5 hcl5 hro5 hx19_5 hfp5 hx20_5 hx22_5 hx23_5 hx25_5 hx26_5 hx27_5
  dsimp only at hit3
  simp only [show ¬ (3 + 1 < 4) by decide, ↓reduceIte,
    show sp + BitVec.ofNat 64 (12848 + 512 * 3) = sp + 14384#64 by rfl,
    show sp + BitVec.ofNat 64 (23104 + 352 * 3) = sp + 24160#64 by rfl] at hit3
  refine sepWP_seq_env hcl5 hro5 (SepWP.weaken_pre (Entails.trans hP5 (by sep_frame)) hit3) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 _ ⟨hsp6, hspA6, hx19_6, hfp6, _, _, _, _, _, _, hP6⟩
  dsimp only [F] at hP6
  have hm12832_mid : memRegion (sp + 12832#64) 8 ∗ memRegion (sp + 12840#64) 8 ∗
      memRegion (sp + 12848#64) 2048 ∗ memRegion (sp + 14896#64) 8 =
      memRegion (sp + 12832#64) 2048 ∗ memRegion (sp + 14880#64) 24 := by
    rw [← hm12832_in]
    exact memRegion_split' (b := sp + 12832#64) (b' := sp + 14880#64) (n := 2048) (k := (24 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hP6' : P6 ⊢ PolyMem (sp + 24720#64) (polyVecNat r0) ∗ PolyMem (sp + 25232#64) (polyVecNat r1) ∗
      PolyMem (sp + 25744#64) (polyVecNat r2) ∗ PolyMem (sp + 26256#64) (polyVecNat r3) ∗
      memRegion (sp + 12832#64) 2048 ∗
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 14880#64) 24 ∗
        ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
        ((sp + 23456#64) ↦ₛ neonCompressSerialize11Poly u1) ∗
        ((sp + 23808#64) ↦ₛ neonCompressSerialize11Poly u2) ∗
        ((sp + 24160#64) ↦ₛ neonCompressSerialize11Poly u3) ∗
        memRegion (sp + 28848#64) 2048 ∗ memRegion (sp + 31408#64) 1232 ∗ Rest) := by
    refine Entails.trans hP6 ?_
    refine entails_sub (vecRangeMem_entails_memRegion 4 (sp + 2368#64) ser11ConstFn) (by sep_frame) ?_
    refine entails_sub (polyMem4_12848_entails_memRegion sp u0 u1 u2 u3) (by sep_frame) ?_
    rw [hm28848_split, hm31408, show 16 * 4 = 64 by rfl]
    have hm12832_ent : memRegion (sp + 12832#64) 8 ∗ memRegion (sp + 12840#64) 8 ∗
        memRegion (sp + 12848#64) 2048 ∗ memRegion (sp + 14896#64) 8 ⊢
        memRegion (sp + 12832#64) 2048 ∗ memRegion (sp + 14880#64) 24 := by
      rw [hm12832_mid]; exact Entails.refl _
    exact entails_sub hm12832_ent (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP6'
    (SepWP.mono (seg4_rhat_copy hb hbase s6 sp x19Val fpVal r0 r1 r2 r3
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 14880#64) 24 ∗
        ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
        ((sp + 23456#64) ↦ₛ neonCompressSerialize11Poly u1) ∗
        ((sp + 23808#64) ↦ₛ neonCompressSerialize11Poly u2) ∗
        ((sp + 24160#64) ↦ₛ neonCompressSerialize11Poly u3) ∗
        memRegion (sp + 28848#64) 2048 ∗ memRegion (sp + 31408#64) 1232 ∗ Rest)
      hpc6 hrun6 hsp6 hspA6 hx19_6 hfp6 hcl6) ?_)
  rintro sf Pf _ _ ⟨hsp', hspA', hx19', hx20', hfp', hPf⟩
  refine ⟨hsp', hspA', hx19', hx20', hfp', Entails.trans hPf ?_⟩
  have hc1_join :
      ((sp + 23104#64) ↦ₛ (neonCompressSerialize11Poly u0 ++ neonCompressSerialize11Poly u1 ++
        neonCompressSerialize11Poly u2 ++ neonCompressSerialize11Poly u3)) =
      ((sp + 23104#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
        ((sp + 23456#64) ↦ₛ neonCompressSerialize11Poly u1) ∗
        ((sp + 23808#64) ↦ₛ neonCompressSerialize11Poly u2) ∗
        ((sp + 24160#64) ↦ₛ neonCompressSerialize11Poly u3) := by
    simp only [List.append_assoc, pointsToBytes_append, neonCompressSerialize11Poly_length,
      show (sp + 23104#64) + BitVec.ofNat 64 352 = sp + 23456#64 by clear * -; bv_omega,
      show (sp + 23456#64) + BitVec.ofNat 64 352 = sp + 23808#64 by clear * -; bv_omega,
      show (sp + 23808#64) + BitVec.ofNat 64 352 = sp + 24160#64 by clear * -; bv_omega]
  rw [hc1_join]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg4Compress
