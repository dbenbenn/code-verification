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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Row -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7SerSimd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b

/-!
# `kyber_decapsulate` (`B06`) — Segment 7 Full `uVec` + `c₁'` + `r̂` Copy (`+0x9380 .. +0xb308`)

Composes `Seg7Row.seg7_uvec_ok` (`+0x9380 .. +0xafc0`) with the 4-polynomial
`compress_and_serialize_11` loops (`+0xafc0 .. +0xb2e8`, writing `1,408` bytes of `c₁'` at
`[sp + 24704, sp + 26112)`) and the `2,048`-byte `r̂[0..3]` copy to `[sp + 14432, sp + 16480)`
(`+0xb2e8 .. +0xb308`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 compressAndEncode polyAdd polyInvNtt polyNtt
  sampleMatrixWith sampleNtt sampleVecCbd2 shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 lane16 lane32 lane32_pack4x32 pack4x32)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd (exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (ATransAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt (rHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat (offSeg7Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7Row (
  offSeg7Mid seg7_uvec_ok uVecPoly06 uVecPoly06_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7SerSimd (
  cells11_eq_neonSerialize11Half cells22_eq_neonSerialize11Bytes
  exec_simdBic_4s_f8_24 exec_simdBic_8h_f8_8 exec_simdShl_4s_11 exec_simdUshr_4s_5
  exec_umov_b1 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4 exec_umov_h5
  exec_umov_h6 exec_umov_h7 lane16_neonCompress8h_11_mask
  neonCompressSerialize11Poly neonCompressSerialize11Poly_eq neonCompressSerialize11Poly_length
  seg7_compress11_eq ser11_b0 ser11_b1 ser11_lsr ser11_shl_lsr)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xafc0 → 0xb304]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg7Header   : BitVec 64 := BitVec.ofNat 64 45032
@[simp, arm64_norm, wp_norm] abbrev offSeg7Outer    : BitVec 64 := BitVec.ofNat 64 45120
@[simp, arm64_norm, wp_norm] abbrev offSeg7Zero     : BitVec 64 := BitVec.ofNat 64 45208
@[simp, arm64_norm, wp_norm] abbrev offSeg7Inner    : BitVec 64 := BitVec.ofNat 64 45324
@[simp, arm64_norm, wp_norm] abbrev offSeg7Store    : BitVec 64 := BitVec.ofNat 64 45464
@[simp, arm64_norm, wp_norm] abbrev offSeg7Bounce   : BitVec 64 := BitVec.ofNat 64 45748
@[simp, arm64_norm, wp_norm] abbrev offSeg7RhatCopy : BitVec 64 := BitVec.ofNat 64 45800
@[simp, arm64_norm, wp_norm] abbrev offSeg8Start    : BitVec 64 := BitVec.ofNat 64 45832

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC06
attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdBic_4s_f8_24 exec_simdBic_8h_f8_8
  exec_simdShl_4s_11 exec_simdUshr_4s_5
  exec_umov_b1 exec_umov_h1 exec_umov_h2 exec_umov_h3 exec_umov_h4
  exec_umov_h5 exec_umov_h6 exec_umov_h7
  exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdOrr_16b svc_simdTrn1_8h

/-! ## 1. `ByteRangeMem` & Helper Step Lemmas -/

private def ByteRangeMem : Nat → BitVec 64 → (Nat → BitVec 8) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, f => (ptr ↦₈ f 0) ∗ ByteRangeMem n (ptr + 1#64) (fun i => f (i + 1))

private theorem byteRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 8}
    (h : ∀ i, i < n → f i = g i) : ByteRangeMem n ptr f = ByteRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [ByteRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

private theorem SepStore8.byteRange {n k : Nat} {ea ptr : BitVec 64} {val : BitVec 8}
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

private theorem sepWP_elim_cell1 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 8, SepWP prog target s ((a ↦₈ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_byteRange :
    ∀ (n : Nat), n ≤ 32 → ∀ {prog : Program} {target : BitVec 64} {s : State}
      {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop},
      (∀ f : Nat → BitVec 8, SepWP prog target s (ByteRangeMem n a f ∗ R0) post) →
      SepWP prog target s (memRegion a n ∗ R0) post
  | 0, _, _, _, _, a, _, _, h => by
    simpa [ByteRangeMem, memRegion_zero] using h (fun _ => 0#8)
  | n + 1, hn, _, _, _, a, R0, _, h => by
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
@[simp] private theorem spA_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).pstate = s.pstate := rfl
@[simp] private theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) :
    (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem sp_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := rfl
@[simp] private theorem spA_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := rfl
@[simp] private theorem status_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := rfl
@[simp] private theorem mem_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := rfl
@[simp] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem spA_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := rfl
@[simp] private theorem spA_setMem' (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := rfl
@[simp] private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) :
    (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem readReg32_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[simp] private theorem readReg32_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[simp] private theorem spA_writeReg64_gpr (s : State) (i : BitVec 5) (w : BitVec 64) :
    (s.writeReg64 (.gpr i) w).spAligned = s.spAligned := rfl
@[simp] private theorem spA_writeReg32_gpr (s : State) (i : BitVec 5) (w : BitVec 32) :
    (s.writeReg32 (.gpr i) w).spAligned = s.spAligned := rfl
@[simp] private theorem spA_setPState (s : State) (p : PState) :
    (s.setPState p).spAligned = s.spAligned := rfl
@[simp] private theorem pstate_setMem' (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := rfl
@[simp] private theorem sp_setMem' (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := rfl
@[simp] private theorem zext64_zext32_16 (x : BitVec 16) :
    (x.zeroExtend 32).zeroExtend 64 = x.zeroExtend 64 := by bv_bits
@[simp] private theorem zext64_shl1_zext32_16 (x : BitVec 16) :
    (x.zeroExtend 32 <<< 1).zeroExtend 64 = x.zeroExtend 64 <<< 1 := by bv_bits
@[simp] private theorem zext64_shl2_zext32_16 (x : BitVec 16) :
    (x.zeroExtend 32 <<< 2).zeroExtend 64 = x.zeroExtend 64 <<< 2 := by bv_bits
@[simp] private theorem trunc8_trunc32_64 (v : BitVec 64) :
    (v.truncate 32).truncate 8 = v.truncate 8 := by bv_bits

private theorem step_strSimd8_byteRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {addr : AddrMode} {Rest : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff k : Nat) (vt : BitVec 5) (val : BitVec 8)
    (f : Nat → BitVec 8)
    (hk : k < 22) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.strSimd .B8 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea + BitVec.ofNat 64 k, none))
    (hval : (s.readVReg128 vt).truncate 8 = val)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (ByteRangeMem 22 ea (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (ByteRangeMem 22 ea f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strSimd8 (wb := none) hpc hrun hfetch hsp haddr hval
    (SepStore8.left (SepStore8.byteRange hk rfl))
    (by simp [applyWriteback, hpc']) hnext

private theorem step_str8_byteRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff k : Nat) (rt : Reg) (val : BitVec 8)
    (f : Nat → BitVec 8)
    (hk : k < 22) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.str .B8 rt (.Offset .x10 (BitVec.ofNat 64 k))))
    (hea : s.readReg64 .x10 = ea) (hval : (s.readReg32 rt).truncate 8 = val)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (ByteRangeMem 22 ea (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (ByteRangeMem 22 ea f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_str8 (wb := none) hpc hrun hfetch rfl
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

private theorem polyMem4_eq_pointsToBytes (a : BitVec 64) (p0 p1 p2 p3 : Poly16) :
    PolyMem a (polyVecNat p0) ∗ PolyMem (a + 512#64) (polyVecNat p1) ∗
      PolyMem (a + 1024#64) (polyVecNat p2) ∗ PolyMem (a + 1536#64) (polyVecNat p3) =
      (a ↦ₛ (vecRangeBytes 32 (polyVecNat p0) ++ vecRangeBytes 32 (polyVecNat p1) ++
        vecRangeBytes 32 (polyVecNat p2) ++ vecRangeBytes 32 (polyVecNat p3))) := by
  dsimp only [PolyMem]
  rw [vecRangeMem_eq_pointsToBytes 32 a, vecRangeMem_eq_pointsToBytes 32 (a + 512#64),
    vecRangeMem_eq_pointsToBytes 32 (a + 1024#64), vecRangeMem_eq_pointsToBytes 32 (a + 1536#64)]
  simp only [List.append_assoc, pointsToBytes_append, vecRangeBytes_length,
    show BitVec.ofNat 64 (16 * 32) = 512#64 from rfl, BitVec.add_assoc]
  rfl

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
    rw [ser11Prefix, List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ← ser11Prefix, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, ser11Chunk_length]
    omega

private theorem ser11Prefix_succ (u : Poly16) (c : Nat) :
    ser11Prefix u (c + 1) = ser11Prefix u c ++ ser11Chunk u c := by
  simp [ser11Prefix, List.range_succ, List.flatten_append]

private theorem ser11Prefix_sixteen (u : Poly16) :
    ser11Prefix u 16 = neonCompressSerialize11Poly u := rfl

private def c10321340Vec  : BitVec 128 := pack4x32 fun _ => 10321340#32
private def c1664Vec      : BitVec 128 := pack4x32 fun _ => 1664#32
private def c134215680Vec : BitVec 128 := pack4x32 fun _ => 134215680#32
private def c3329Vec      : BitVec 128 := dup8x16 3329#16

private def ser11ConstFn : Nat → BitVec 128
  | 0 => c10321340Vec
  | 1 => c1664Vec
  | 2 => c134215680Vec
  | _ => c3329Vec

/-! ## 2. `uVec` Copy (`+0xafc0 → +0xafe8`) & Header (`+0xafe8 → +0xb040`) -/

private theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

@[simp] private abbrev PresFp19 (s : State) (fpVal x19Val : BitVec 64) : Prop :=
  s.readReg64 .fp = fpVal ∧ s.readReg64 .x19 = x19Val

private theorem PresFp19.rfl_of (s : State) : PresFp19 s (s.readReg64 .fp) (s.readReg64 .x19) :=
  ⟨rfl, rfl⟩

private theorem PresFp19.trans {s : State} {fp1 x19_1 fp0 x19_0 : BitVec 64}
    (h2 : PresFp19 s fp1 x19_1) (h1 : fp1 = fp0 ∧ x19_1 = x19_0) : PresFp19 s fp0 x19_0 :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem seg7_uvec_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) (u0 u1 u2 u3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Mid) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Header) s
      (PolyMem (sp + 30448#64) (polyVecNat u0) ∗ PolyMem (sp + 30960#64) (polyVecNat u1) ∗
        PolyMem (sp + 31472#64) (polyVecNat u2) ∗ PolyMem (sp + 31984#64) (polyVecNat u3) ∗
        memRegion (sp + 14448#64) 2048 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14448#64 ∧
        (Pf ⊢ PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 14960#64) (polyVecNat u1) ∗
          PolyMem (sp + 15472#64) (polyVecNat u2) ∗ PolyMem (sp + 15984#64) (polyVecNat u3) ∗
          memRegion (sp + 30448#64) 2048 ∗ Rest)) := by
  subst hbase
  generalize hbs_def : vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
    vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3) = bs
  have hbs : bs.length = 2048 := by rw [← hbs_def]; simp [List.length_append, vecRangeBytes_length]
  have hpSrc := polyMem4_eq_pointsToBytes (sp + 30448#64) u0 u1 u2 u3
  have hpDst := polyMem4_eq_pointsToBytes (sp + 14448#64) u0 u1 u2 u3
  rw [hbs_def] at hpSrc hpDst
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpSrc hpDst
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp + 14448#64) 2048 ∗ ((sp + 30448#64) ↦ₛ bs) ∗ Rest by
      exact entails_sub (Entails.of_eq hpSrc) (by sep_frame) (by sep_frame)) ?_
  wp_cut_codeLoaded
  wp_steps 10
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl1
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 14448#64, sp + 30448#64, bs)
  rw [← hpDst]
  have hsp1 : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*], by simp [*], ?_⟩
  have hm30 : ((sp + 30448#64) ↦ₛ bs) ⊢ memRegion (sp + 30448#64) 2048 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp + 30448#64) bs
  exact entails_sub hm30 (by sep_frame) (by sep_frame)

private theorem seg7_header [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Header) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hx21 : s.readReg64 .x21 = sp + 14448#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Outer) s
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 14440#64) 8 ∗
        memRegion (sp + 16496#64) 8 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧ PresFp19 s1 fpVal x19Val ∧
        s1.readReg64 .x20 = sp + 30448#64 ∧ s1.readReg64 .x21 = sp + 14448#64 ∧
        s1.readReg64 .x23 = 0#64 ∧ s1.readReg64 .x25 = 352#64 ∧
        s1.readReg64 .x26 = sp + 33888#64 ∧ s1.readReg64 .x27 = sp + 24704#64 ∧
        (P1 ⊢ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
          memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗ Rest)) := by
  subst hbase
  apply SepWP.of_memRegion_vecRangeMem 4 (sp + 2368#64) (by decide) (by sep_focus); intro fc
  refine SepWP.weaken_pre
    (show VecRangeMem 4 (sp + 2368#64) fc ∗ (memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗ Rest) ⊢
      memRegion (sp + 14440#64) 8 ∗ (memRegion (sp + 16496#64) 8 ∗ (VecRangeMem 4 (sp + 2368#64) fc ∗ Rest)) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w1
  refine SepWP.weaken_pre (show ((sp + 14440#64) ↦₆₄ w1) ∗ (memRegion (sp + 16496#64) 8 ∗
      (VecRangeMem 4 (sp + 2368#64) fc ∗ Rest)) ⊢
      memRegion (sp + 16496#64) 8 ∗ (((sp + 14440#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2368#64) fc ∗ Rest) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w2
  refine SepWP.weaken_pre
    (show ((sp + 16496#64) ↦₆₄ w2) ∗ (((sp + 14440#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2368#64) fc ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2368#64) fc ∗ (((sp + 14440#64) ↦₆₄ w1) ∗ ((sp + 16496#64) ↦₆₄ w2) ∗ Rest) by
      sep_frame) ?_
  wp_steps 12
  refine step_strQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45080 45084 2416 4 3 0#5 c3329Vec fc
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c3329Vec]) rfl ?_; intro m1
  wp_steps 4
  refine step_strQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45100 45104 2400 4 2 0#5 c134215680Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c134215680Vec]) rfl ?_; intro m2
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45108 45112 2384 4 1 0#5 c1664Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c1664Vec]) rfl ?_; intro m3
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45116 45120 2368 4 0 0#5 c10321340Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c10321340Vec]) rfl ?_; intro m4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp], by simp [hx20], by simp [hx21],
      by simp, by simp, by simp, by simp, ?_⟩
  have hvc : VecRangeMem 4 (sp + 2368#64)
      (Function.update (Function.update (Function.update (Function.update fc 3 c3329Vec) 2 c134215680Vec) 1 c1664Vec) 0 c10321340Vec) =
      VecRangeMem 4 (sp + 2368#64) ser11ConstFn := by
    apply vecRangeMem_congr; intro i hi
    rcases i with _ | _ | _ | _ | n <;> try omega
    all_goals simp [ser11ConstFn, Function.update]
  rw [hvc]
  exact entails_sub (cell_entails_memRegion8 (sp + 14440#64) 4#64) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (sp + 16496#64) 0#64) (by sep_frame) (by sep_frame))

/-! ## 3. Outer-Loop Stage Preparation (`+0xb040 → +0xb098`) & Zero/Load (`+0xb098 → +0xb10c`) -/

private theorem seg7_prep_poly [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) {idx : Nat} (hidx : idx < 4) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hx21 : s.readReg64 .x21 = sp + 14448#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 idx) (hx25 : s.readReg64 .x25 = 352#64)
    (hx26 : s.readReg64 .x26 = sp + 33888#64) (hx27 : s.readReg64 .x27 = sp + 24704#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (14448 + 512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Zero) s
      (PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 30448#64) 520 ∗ memRegion (sp + 33008#64) 520 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14448#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (352 * idx) ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x25 = 352#64 ∧
        sf.readReg64 .x26 = sp + 33888#64 ∧ sf.readReg64 .x27 = sp + 24704#64 ∧
        (Pf ⊢ PolyMem uPtr (polyVecNat u) ∗ PolyMem (sp + 30448#64) (polyVecNat u) ∗
          memRegion (sp + 30960#64) 8 ∗ memRegion (sp + 33008#64) 520 ∗ Rest)) := by
  subst hbase; intro uPtr
  generalize hbsU_def : vecRangeBytes 32 (polyVecNat u) = bsU
  have hbsU : bsU.length = 512 := by rw [← hbsU_def]; exact vecRangeBytes_length 32 (polyVecNat u)
  have hm520a : memRegion (sp + 30448#64) 520 = memRegion (sp + 30448#64) 8 ∗ memRegion (sp + 30456#64) 512 :=
    memRegion_split' (b := sp + 30448#64) (b' := sp + 30456#64) (n := 8) (k := (512 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm520b : memRegion (sp + 30448#64) 520 = memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 8 :=
    memRegion_split' (b := sp + 30448#64) (b' := sp + 30960#64) (n := 512) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hpU : PolyMem uPtr (polyVecNat u) = (uPtr ↦ₛ bsU) := by
    rw [← hbsU_def]; exact vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u)
  have hp30 : ((sp + 30448#64) ↦ₛ bsU) = PolyMem (sp + 30448#64) (polyVecNat u) := by
    rw [← hbsU_def]; exact (vecRangeMem_eq_pointsToBytes 32 (sp + 30448#64) (polyVecNat u)).symm
  rw [hm520a, hpU]
  refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 30448#64) 8 ∗
      (memRegion (sp + 30456#64) 512 ∗ (uPtr ↦ₛ bsU) ∗ memRegion (sp + 33008#64) 520 ∗ Rest) by
    sep_frame) ?_
  apply sepWP_elim_cell8; intro w0
  have huPtr : (sp + 14448#64) + (BitVec.ofNat 64 idx <<< 9) = uPtr := by
    dsimp only [uPtr]; rcases idx with _ | _ | _ | _ | n <;> try omega
    all_goals (clear * -; bv_omega)
  have ha30448 : (sp + 30448#64) + 8#64 = sp + 30456#64 := by clear * -; bv_omega
  have hjoin1 : ((sp + 30448#64) ↦₆₄ w0) ∗ ((sp + 30456#64) ↦ₛ bsU) =
      ((sp + 30448#64) ↦ₛ (unpack64 w0 ++ bsU)) := by
    rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, unpack64_length, ha30448]
  have h520len : (unpack64 w0 ++ bsU).length = 520 := by
    simp [List.length_append, unpack64_length, hbsU]
  have ha33008 : (sp + 33008#64) + 8#64 = sp + 33016#64 := by clear * -; bv_omega
  have hsplit33008 : ((sp + 33008#64) ↦ₛ (unpack64 w0 ++ bsU)) =
      ((sp + 33008#64) ↦ₛ unpack64 w0) ∗ ((sp + 33016#64) ↦ₛ bsU) := by
    rw [pointsToBytes_append, unpack64_length, ha33008]
  have hm30448 : ((sp + 30448#64) ↦ₛ (unpack64 w0 ++ bsU)) ⊢
      memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 8 := by
    rw [← hm520b, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 30448#64) (unpack64 w0 ++ bsU)
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 30456#64) 512 ∗ (uPtr ↦ₛ bsU) ∗
      (((sp + 30448#64) ↦₆₄ w0) ∗ memRegion (sp + 33008#64) 520 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_cl hcl (mid := blkPl06.base + BitVec.ofNat 64 45144)
    (post1 := fun s1 P1 =>
      s1.sp = sp ∧ s1.spAligned = true ∧ PresFp19 s1 fpVal x19Val ∧
      s1.readReg64 .x20 = sp + 30448#64 ∧ s1.readReg64 .x21 = sp + 14448#64 ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 idx + 1#64 ∧ s1.readReg64 .x25 = 352#64 ∧
      s1.readReg64 .x26 = sp + 33888#64 ∧ s1.readReg64 .x27 = sp + 24704#64 ∧
      s1.readReg64 .x28 = BitVec.ofNat 64 idx ∧
      (P1 ⊢ memRegion (sp + 33008#64) 520 ∗ ((sp + 30448#64) ↦ₛ (unpack64 w0 ++ bsU)) ∗
        ((uPtr ↦ₛ bsU) ∗ Rest)))
    (by
      wp_cut_codeLoaded; wp_steps 6
      apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl1
      wp_call (blk28_memcpy_06 blkPl06.base) (sp + 30456#64, uPtr, bsU)
      have hsp1 : sf.sp = sp := by simp [*]
      refine SepWP.done (by wp_norm_lhs) (by simp [*])
        ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*], by simp [*],
          by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
      rw [← hjoin1]; sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hfp1, hx20_1, hx21_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine sepWP_seq_cl hcl1 (mid := blkPl06.base + BitVec.ofNat 64 45168)
    (post1 := fun s2 P2 =>
      s2.sp = sp ∧ s2.spAligned = true ∧ PresFp19 s2 fpVal x19Val ∧
      s2.readReg64 .x20 = sp + 30448#64 ∧ s2.readReg64 .x21 = sp + 14448#64 ∧
      s2.readReg64 .x23 = BitVec.ofNat 64 idx + 1#64 ∧ s2.readReg64 .x25 = 352#64 ∧
      s2.readReg64 .x26 = sp + 33888#64 ∧ s2.readReg64 .x27 = sp + 24704#64 ∧
      s2.readReg64 .x28 = BitVec.ofNat 64 idx ∧
      (P2 ⊢ memRegion (sp + 30448#64) 512 ∗ ((sp + 33016#64) ↦ₛ bsU) ∗
        (((sp + 33008#64) ↦ₛ unpack64 w0) ∗ memRegion (sp + 30960#64) 8 ∗ (uPtr ↦ₛ bsU) ∗ Rest)))
    (by
      wp_cut_codeLoaded; wp_steps 6
      apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl2
      wp_call (blk28_memcpy_06 blkPl06.base) (sp + 33008#64, sp + 30448#64, unpack64 w0 ++ bsU)
      have hsp2 : sf.sp = sp := by simp [*]
      refine SepWP.done (by wp_norm_lhs) (by simp [*])
        ⟨hsp2, spAligned_of_sp_eq hspA1 hsp1 hsp2, by simp [*], by simp [*], by simp [*],
          by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
      rw [hsplit33008]; exact entails_sub hm30448 (by sep_frame) (by sep_frame)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 ⟨hsp2, hspA2, hfp2, hx20_2, hx21_2, hx23_2, hx25_2, hx26_2, hx27_2, hx28_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  wp_cut_codeLoaded; wp_steps 7
  apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl3
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 30448#64, sp + 33016#64, bsU)
  have hsp3 : sf.sp = sp := by simp [*]
  have hspA3 : sf.spAligned = true := spAligned_of_sp_eq hspA2 hsp2 hsp3
  wp_steps 2
  refine step_bCond_not_taken (dst := blkPl06.base + offSeg7Zero)
    (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]; clear * - hidx; rcases idx with _ | _ | _ | _ | n <;> first | simp | omega)
    (by clear * -; dsimp [offSeg7Zero]; bv_omega) ?_
  refine SepWP.done (by simp [State.setPC]) (by simp [*])
    ⟨by simp [hsp3], spAligned_of_sp_eq hspA3 hsp3 (by simp [hsp3]),
      by simp [*], by simp [*], by simp [*],
      by simp [*]; clear * - hidx; rcases idx with _ | _ | _ | _ | n <;> first | decide | omega,
      by simp [*]; clear * - hidx; rcases idx with _ | _ | _ | _ | n <;> first | decide | omega,
      by simp [*], by simp [*], by simp [*], ?_⟩
  have hm33008 : ((sp + 33008#64) ↦ₛ unpack64 w0) ∗ ((sp + 33016#64) ↦ₛ bsU) ⊢
      memRegion (sp + 33008#64) 520 := by
    rw [← hsplit33008, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 33008#64) (unpack64 w0 ++ bsU)
  rw [← hpU, hp30]
  exact entails_sub hm33008 (by sep_frame) (by sep_frame)

local macro "step_zero_q22 " sp:term:arg hrun:term:arg hsp:term:arg hspA:term:arg
    pcOff:num nextOff:num spOff:num k:num : tactic => `(tactic|
  (refine step_strQ128_sp_vecRange blkPl06.base $sp ($sp + 33888#64) $pcOff $nextOff $spOff 22 $k 0#5 0#128 _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp [$hsp:term])
      (spAligned_of_sp_eq $hspA $hsp (by simp [$hsp:term]))
      (by simp) (by clear * -; bv_omega) (by simp) rfl ?_;
   intro _))

private theorem seg7_zero_load [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Zero) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Inner) s
      (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion (sp + 33888#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 30464#64 ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readVReg128 5#5 = c3329Vec ∧ sf.readVReg128 6#5 = c134215680Vec ∧
        sf.readVReg128 7#5 = c1664Vec ∧ sf.readVReg128 16#5 = c10321340Vec ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion (sp + 33888#64) 352 ∗ Rest)) := by
  subst hbase
  refine SepWP.weaken_pre
    (show VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ (memRegion (sp + 33888#64) 352 ∗ Rest) ⊢
      memRegion (sp + 33888#64) 352 ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest) by sep_frame) ?_
  apply SepWP.of_memRegion_vecRangeMem 22 (sp + 33888#64) (by decide) (by sep_focus); intro fz
  refine SepWP.weaken_pre
    (show VecRangeMem 22 (sp + 33888#64) fz ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ (VecRangeMem 22 (sp + 33888#64) fz ∗ Rest) by sep_frame) ?_
  wp_steps 1
  refine step_ldrQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45212 45216 2416 4 3 5#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45216 45220 2400 4 2 6#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45220 45224 2384 4 1 7#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl06.base sp (sp + 2368#64) 45224 45228 2368 4 0 16#5 ser11ConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  wp_steps 2
  refine SepWP.weaken_pre
    (P' := VecRangeMem 22 (sp + 33888#64) fz ∗ (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ Rest))
    (by sep_frame) ?_
  step_zero_q22 sp hrun hsp hspA 45236 45240 34224 21; step_zero_q22 sp hrun hsp hspA 45240 45244 34208 20
  step_zero_q22 sp hrun hsp hspA 45244 45248 34192 19; step_zero_q22 sp hrun hsp hspA 45248 45252 34176 18
  step_zero_q22 sp hrun hsp hspA 45252 45256 34160 17; step_zero_q22 sp hrun hsp hspA 45256 45260 34144 16
  step_zero_q22 sp hrun hsp hspA 45260 45264 34128 15; step_zero_q22 sp hrun hsp hspA 45264 45268 34112 14
  step_zero_q22 sp hrun hsp hspA 45268 45272 34096 13; step_zero_q22 sp hrun hsp hspA 45272 45276 34080 12
  step_zero_q22 sp hrun hsp hspA 45276 45280 34064 11; step_zero_q22 sp hrun hsp hspA 45280 45284 34048 10
  step_zero_q22 sp hrun hsp hspA 45284 45288 34032 9;  step_zero_q22 sp hrun hsp hspA 45288 45292 34016 8
  step_zero_q22 sp hrun hsp hspA 45292 45296 34000 7;  step_zero_q22 sp hrun hsp hspA 45296 45300 33984 6
  step_zero_q22 sp hrun hsp hspA 45300 45304 33968 5;  step_zero_q22 sp hrun hsp hspA 45304 45308 33952 4
  step_zero_q22 sp hrun hsp hspA 45308 45312 33936 3;  step_zero_q22 sp hrun hsp hspA 45312 45316 33920 2
  step_zero_q22 sp hrun hsp hspA 45316 45320 33904 1;  step_zero_q22 sp hrun hsp hspA 45320 45324 33888 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp],
      by simp, by simp, by simp [hx20],
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [ser11ConstFn], by simp [ser11ConstFn], by simp [ser11ConstFn], by simp [ser11ConstFn], ?_⟩
  exact entails_sub (vecRangeMem_entails_memRegion 22 (sp + 33888#64) _) (by sep_frame) (by sep_frame)

/-! ## 4. 16-Iteration `compress_11` + `serialize_11` Inner Loop (`+0xb10c → +0xb2b4`) -/

private theorem seg7_compress11_vec_eq (vn : BitVec 128) :
    let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
    let evIn := (pack4x32 fun j => lane32 u0 j <<< 11) &&& 0x07ffffff07ffffff07ffffff07ffffff#128 ||| c1664Vec
    let odIn := ((pack4x32 fun j => lane32 u0 j >>> 5) &&& c134215680Vec) ||| c1664Vec
    let evOut := pack4x32 fun k => lane32 (simdSqdmulh4s evIn c10321340Vec) k >>> 4
    let odOut := pack4x32 fun k => lane32 (simdSqdmulh4s odIn c10321340Vec) k >>> 4
    simdTrn1_8h evOut odOut &&& dup8x16 0x07ff#16 = neonCompress8h 11 vn := by
  simpa [c3329Vec, c134215680Vec, c1664Vec, c10321340Vec, simdSqdmulh4s, lane32_pack4x32] using
    seg7_compress11_eq vn

section InnerSimd
attribute [local irreducible] c10321340Vec c1664Vec c134215680Vec c3329Vec
  dup8x16 pack4x32 lane16 lane32 polyVecNat
  simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h neonCompress8h

private structure Seg7SimdPres (s0 s : State) : Prop where
  fp  : PresFp19 s (s0.readReg64 .fp) (s0.readReg64 .x19)
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  v5  : s.readVReg128 5#5  = c3329Vec
  v6  : s.readVReg128 6#5  = c134215680Vec
  v7  : s.readVReg128 7#5  = c1664Vec
  v16 : s.readVReg128 16#5 = c10321340Vec

private theorem seg7_inner_simd_s1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (22 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (30464 + 32 * c))
    (hx26 : s.readReg64 .x26 = sp + 33888#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c134215680Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    let u0 := simdAdd8h (simdCmltZero8h (polyVecNat u (2 * c)) &&& c3329Vec) (polyVecNat u (2 * c))
    let u1 := simdAdd8h (simdCmltZero8h (polyVecNat u (2 * c + 1)) &&& c3329Vec) (polyVecNat u (2 * c + 1))
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 45368) s
      (PolyMem (sp + 30448#64) (polyVecNat u) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = s.spAligned ∧
        sm.pstate = subsPState64 (BitVec.ofNat 64 (22 * (c + 1))) 352#64 ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (22 * (c + 1)) ∧
        sm.readReg64 .x9 = sp + BitVec.ofNat 64 (30464 + 32 * (c + 1)) ∧
        sm.readReg64 .x10 = sp + BitVec.ofNat 64 (33888 + 22 * c) ∧
        Seg7SimdPres s sm ∧
        sm.readVReg128 0#5 = u0 ∧ sm.readVReg128 1#5 = u1 ∧
        Pm = (PolyMem (sp + 30448#64) (polyVecNat u) ∗ Rest)) := by
  subst hbase; intro u0 u1
  have hea1 : (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * c)) + 16#64 =
      (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * c + 1)) := by clear * - hc; bv_omega
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * c)))
    (ea16 := (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * c + 1)))
    (by wp_norm_lhs) hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hc; bv_omega) hea1
    (SepLoad128.vecRange (n := 32) (k := 2 * c) (by omega) rfl).left
    (SepLoad128.vecRange (n := 32) (k := 2 * c + 1) (by omega) rfl).left
    (by wp_norm_lhs) ?_
  wp_steps 10
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp,
      by simp; congr 1; clear * - hc; bv_omega,
      by simp; clear * - hc; bv_omega,
      by simp; clear * - hc; bv_omega,
      by simp; clear * - hc; bv_omega,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp [hx26], by simp,
        by simp [hv5], by simp [hv6], by simp [hv7], by simp [hv16]⟩,
      by simp [u0], by simp [u1], rfl⟩

private theorem seg7_inner_simd_s2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (u0 u1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 45368) (hrun : s.status = .Running)
    (hp : Seg7SimdPres s0 s) (hv0 : s.readVReg128 0#5 = u0) (hv1 : s.readVReg128 1#5 = u1) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 45400) s P
      (fun sm Pm =>
        sm.sp = s.sp ∧ sm.spAligned = s.spAligned ∧ sm.pstate = s.pstate ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧ sm.readReg64 .x9 = s.readReg64 .x9 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ Seg7SimdPres s0 sm ∧
        sm.readVReg128 2#5 = ((pack4x32 fun j => lane32 u0 j <<< 11) &&& 0x07ffffff07ffffff07ffffff07ffffff#128) ∧
        sm.readVReg128 0#5 = ((pack4x32 fun j => lane32 u0 j >>> 5) &&& c134215680Vec) ∧
        sm.readVReg128 3#5 = ((pack4x32 fun j => lane32 u1 j <<< 11) &&& 0x07ffffff07ffffff07ffffff07ffffff#128) ∧
        sm.readVReg128 1#5 = ((pack4x32 fun j => lane32 u1 j >>> 5) &&& c134215680Vec) ∧ Pm = P) := by
  subst hbase; rcases hp with ⟨pfp, p20, p21, p22, p23, p25, p26, p27, pv5, pv6, pv7, pv16⟩
  wp_steps 8
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [pfp], by simp [p20], by simp [p21], by simp [p22], by simp [p23],
        by simp [p25], by simp [p26], by simp [p27],
        by simp [pv5], by simp [pv6], by simp [pv7], by simp [pv16]⟩,
      by simp, by simp, by simp, by simp, rfl⟩

private theorem seg7_inner_simd_s3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (ev0 od0 ev1 od1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 45400) (hrun : s.status = .Running) (hp : Seg7SimdPres s0 s)
    (hv2 : s.readVReg128 2#5 = ev0) (hv0 : s.readVReg128 0#5 = od0)
    (hv3 : s.readVReg128 3#5 = ev1) (hv1 : s.readVReg128 1#5 = od1) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 45432) s P
      (fun sm Pm =>
        sm.sp = s.sp ∧ sm.spAligned = s.spAligned ∧ sm.pstate = s.pstate ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧ sm.readReg64 .x9 = s.readReg64 .x9 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ Seg7SimdPres s0 sm ∧
        sm.readVReg128 2#5 = simdSqdmulh4s (ev0 ||| c1664Vec) c10321340Vec ∧
        sm.readVReg128 0#5 = simdSqdmulh4s (od0 ||| c1664Vec) c10321340Vec ∧
        sm.readVReg128 3#5 = simdSqdmulh4s (ev1 ||| c1664Vec) c10321340Vec ∧
        sm.readVReg128 1#5 = simdSqdmulh4s (od1 ||| c1664Vec) c10321340Vec ∧ Pm = P) := by
  subst hbase; rcases hp with ⟨pfp, p20, p21, p22, p23, p25, p26, p27, pv5, pv6, pv7, pv16⟩
  wp_steps 8
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [pfp], by simp [p20], by simp [p21], by simp [p22], by simp [p23],
        by simp [p25], by simp [p26], by simp [p27],
        by simp [pv5], by simp [pv6], by simp [pv7], by simp [pv16]⟩,
      by simp, by simp,
      by simp, by simp, rfl⟩

private theorem seg7_inner_simd_s4 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (q0 r0 q1 r1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 45432) (hrun : s.status = .Running) (hp : Seg7SimdPres s0 s)
    (hv2 : s.readVReg128 2#5 = q0) (hv0 : s.readVReg128 0#5 = r0)
    (hv3 : s.readVReg128 3#5 = q1) (hv1 : s.readVReg128 1#5 = r1) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Store) s P
      (fun sm Pm =>
        sm.sp = s.sp ∧ sm.spAligned = s.spAligned ∧ sm.pstate = s.pstate ∧
        sm.readReg64 .x8 = s.readReg64 .x8 ∧ sm.readReg64 .x9 = s.readReg64 .x9 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ Seg7SimdPres s0 sm ∧
        sm.readVReg128 1#5 = (simdTrn1_8h (pack4x32 fun k => lane32 q0 k >>> 4)
          (pack4x32 fun k => lane32 r0 k >>> 4) &&& dup8x16 0x07ff#16) ∧
        sm.readVReg128 0#5 = (simdTrn1_8h (pack4x32 fun k => lane32 q1 k >>> 4)
          (pack4x32 fun k => lane32 r1 k >>> 4) &&& dup8x16 0x07ff#16) ∧ Pm = P) := by
  subst hbase; rcases hp with ⟨pfp, p20, p21, p22, p23, p25, p26, p27, pv5, pv6, pv7, pv16⟩
  wp_steps 8
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [pfp], by simp [p20], by simp [p21], by simp [p22], by simp [p23],
        by simp [p25], by simp [p26], by simp [p27],
        by simp [pv5], by simp [pv6], by simp [pv7], by simp [pv16]⟩,
      by simp, by simp, rfl⟩

private theorem seg7_inner_simd [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (22 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (30464 + 32 * c))
    (hx26 : s.readReg64 .x26 = sp + 33888#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c134215680Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Store) s
      (PolyMem (sp + 30448#64) (polyVecNat u) ∗ Rest)
      (fun s4 P4 =>
        s4.sp = sp ∧ s4.spAligned = s.spAligned ∧
        s4.pstate = subsPState64 (BitVec.ofNat 64 (22 * (c + 1))) 352#64 ∧
        s4.readReg64 .x8 = BitVec.ofNat 64 (22 * (c + 1)) ∧
        s4.readReg64 .x9 = sp + BitVec.ofNat 64 (30464 + 32 * (c + 1)) ∧
        s4.readReg64 .x10 = sp + BitVec.ofNat 64 (33888 + 22 * c) ∧
        Seg7SimdPres s s4 ∧
        s4.readVReg128 1#5 = neonCompress8h 11 (polyVecNat u (2 * c)) ∧
        s4.readVReg128 0#5 = neonCompress8h 11 (polyVecNat u (2 * c + 1)) ∧
        P4 = (PolyMem (sp + 30448#64) (polyVecNat u) ∗ Rest)) := by
  refine SepWP.seq (seg7_inner_simd_s1 hb hbase s sp hc u Rest hpc hrun hsp hx8 hx9 hx26 hv5 hv6 hv7 hv16) ?_
  rintro s1 _ hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hp1, hv0_1, hv1_1, rfl⟩
  refine SepWP.seq (seg7_inner_simd_s2 hb hbase s s1 _ _ _ hpc1 hrun1 hp1 hv0_1 hv1_1) ?_
  rintro s2 _ hpc2 hrun2 ⟨hsp2, hspA2, hpst2, hx8_2, hx9_2, hx10_2, hp2, hv2_2, hv0_2, hv3_2, hv1_2, rfl⟩
  refine SepWP.seq (seg7_inner_simd_s3 hb hbase s s2 _ _ _ _ _ hpc2 hrun2 hp2 hv2_2 hv0_2 hv3_2 hv1_2) ?_
  rintro s3 _ hpc3 hrun3 ⟨hsp3, hspA3, hpst3, hx8_3, hx9_3, hx10_3, hp3, hv2_3, hv0_3, hv3_3, hv1_3, rfl⟩
  refine SepWP.mono (seg7_inner_simd_s4 hb hbase s s3 _ _ _ _ _ hpc3 hrun3 hp3 hv2_3 hv0_3 hv3_3 hv1_3) ?_
  rintro s4 _ _ _ ⟨hsp4, hspA4, hpst4, hx8_4, hx9_4, hx10_4, hp4, hv1_4, hv0_4, rfl⟩
  exact ⟨hsp4.trans (hsp3.trans (hsp2.trans hsp1)), hspA4.trans (hspA3.trans (hspA2.trans hspA1)),
    hpst4.trans (hpst3.trans (hpst2.trans hpst1)), hx8_4.trans (hx8_3.trans (hx8_2.trans hx8_1)),
    hx9_4.trans (hx9_3.trans (hx9_2.trans hx9_1)), hx10_4.trans (hx10_3.trans (hx10_2.trans hx10_1)),
    hp4, hv1_4.trans (seg7_compress11_vec_eq (polyVecNat u (2 * c))),
    hv0_4.trans (seg7_compress11_vec_eq (polyVecNat u (2 * c + 1))), rfl⟩

end InnerSimd

private theorem ser11_prefix_append_chunk (dst : BitVec 64) (u : Poly16) (c : Nat) :
    (dst ↦ₛ ser11Prefix u c) ∗ ((dst + BitVec.ofNat 64 (22 * c)) ↦ₛ ser11Chunk u c) =
      (dst ↦ₛ ser11Prefix u (c + 1)) := by
  rw [ser11Prefix_succ, pointsToBytes_append, ser11Prefix_length]

section InnerStore
attribute [local irreducible] c10321340Vec c1664Vec c134215680Vec c3329Vec
  polyVecNat neonCompress8h lane16 neonSerialize11Bytes neonSerialize11Half

private theorem trunc32_zext64_shl (x : BitVec 16) (n : Nat) :
    setWidth 32 (setWidth 64 x <<< n) = setWidth 32 x <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, show i < 64 by omega,
    decide_true, Bool.true_and]
  by_cases hn : i < n
  · simp [hn]
  · simp [hn, show i - n < 32 by omega, show i - n < 64 by omega]

private theorem trunc32_zext64_shr (x : BitVec 16) (n : Nat) :
    setWidth 32 (setWidth 64 x >>> n) = setWidth 32 x >>> n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi,
    decide_true, Bool.true_and]
  by_cases h64 : n + i < 64
  · by_cases h32 : n + i < 32
    · simp [h64, h32]
    · simp [h64, h32, BitVec.getLsbD_of_ge x (n + i) (by omega)]
  · simp [h64, show ¬(n + i < 32) by omega]

private theorem ser11_b1_sw {c0 c1 : BitVec 16}
    (h0 : c0 &&& 0x07ff#16 = c0) (h1 : c1 &&& 0x07ff#16 = c1) :
    setWidth 8 (setWidth 64 (setWidth 8 (c0 >>> 8)) ||| setWidth 64 (setWidth 32 c1 <<< 3)) =
    setWidth 8 (((c0 &&& 0x07ff#16) >>> 8) ||| ((c1 &&& 0x07ff#16) <<< 3)) := by
  rw [h0, h1]; bv_bits

private theorem ser11_bfxil_4 {c2 c3 : BitVec 16}
    (h2 : c2 &&& 0x07ff#16 = c2) (h3 : c3 &&& 0x07ff#16 = c3) :
    setWidth 8 ((setWidth 64 (setWidth 32 c3 <<< 1) &&& 0xfffffffffffffffe#64) |||
      ((setWidth 64 c2 >>> 10) &&& 1#64)) =
    setWidth 8 (((c2 &&& 0x07ff#16) >>> 10) ||| ((c3 &&& 0x07ff#16) <<< 1)) := by
  rw [h2, h3]; bv_bits

private theorem ser11_bfxil_8 {c5 c6 : BitVec 16}
    (h5 : c5 &&& 0x07ff#16 = c5) (h6 : c6 &&& 0x07ff#16 = c6) :
    setWidth 8 ((setWidth 64 (setWidth 32 c6 <<< 2) &&& 0xfffffffffffffffc#64) |||
      ((setWidth 64 c5 >>> 9) &&& 3#64)) =
    setWidth 8 (((c5 &&& 0x07ff#16) >>> 9) ||| ((c6 &&& 0x07ff#16) <<< 2)) := by
  rw [h5, h6]; bv_bits

local macro "step_sb8 " ea:term:arg hrun:term:arg hx10:term:arg _hv1:term:arg _hv0:term:arg
    pcOff:num nextOff:num k:num rt:term:arg : tactic => `(tactic|
  (refine step_str8_byteRange blkPl06.base $ea $pcOff $nextOff $k $rt _ _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs)
      (by simp [$hx10:term, $ea:term]) rfl rfl ?_;
   intro _))

private theorem seg7_inner_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Store) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hpst : s.pstate = subsPState64 (BitVec.ofNat 64 (22 * (c + 1))) 352#64)
    (hx10 : s.readReg64 .x10 = sp + BitVec.ofNat 64 (33888 + 22 * c))
    (hv1 : s.readVReg128 1#5 = neonCompress8h 11 (polyVecNat u (2 * c)))
    (hv0 : s.readVReg128 0#5 = neonCompress8h 11 (polyVecNat u (2 * c + 1))) :
    let nextPc := if c < 15 then b + offSeg7Inner else b + offSeg7Bounce
    SepWP (blkPC06.rebase b (fun _ => none)) nextPc s
      (((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (33888 + 22 * c)) (352 - 22 * c) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = s.spAligned ∧
        PresFp19 sf (s.readReg64 .fp) (s.readReg64 .x19) ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readVReg128 5#5 = s.readVReg128 5#5 ∧ sf.readVReg128 6#5 = s.readVReg128 6#5 ∧
        sf.readVReg128 7#5 = s.readVReg128 7#5 ∧ sf.readVReg128 16#5 = s.readVReg128 16#5 ∧
        (Pf ⊢ ((sp + 33888#64) ↦ₛ ser11Prefix u (c + 1)) ∗
          memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest)) := by
  subst hbase; intro nextPc
  set ea := sp + BitVec.ofNat 64 (33888 + 22 * c)
  have hsplit : memRegion ea (352 - 22 * c) =
      memRegion ea 22 ∗ memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) := by
    have hm := memRegion_split ea 22 (352 - 22 * (c + 1)) (by omega)
    have ha : ea + BitVec.ofNat 64 22 = sp + BitVec.ofNat 64 (33888 + 22 * (c + 1)) := by
      dsimp only [ea]; clear * - hc; bv_omega
    rw [show 22 + (352 - 22 * (c + 1)) = 352 - 22 * c by omega, ha] at hm; exact hm
  refine SepWP.weaken_pre
    (show ((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗ memRegion ea (352 - 22 * c) ∗ Rest ⊢
      memRegion ea 22 ∗ (((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_byteRange 22 (by decide); intro f0
  wp_steps 17
  refine step_strSimd8_byteRange blkPl06.base ea 45532 45536 0 1#5 _ _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10, ea]) (by simp [hv1]; rfl) rfl ?_; intro _
  step_sb8 ea hrun hx10 hv1 hv0 45536 45540 7 .x7
  wp_steps 2; step_sb8 ea hrun hx10 hv1 hv0 45548 45552 10 .x28
  wp_steps 2; step_sb8 ea hrun hx10 hv1 hv0 45560 45564 12 .x3
  wp_steps 5; step_sb8 ea hrun hx10 hv1 hv0 45584 45588 1 .x4
  wp_steps 2; step_sb8 ea hrun hx10 hv1 hv0 45596 45600 3 .x5
  wp_steps 2; step_sb8 ea hrun hx10 hv1 hv0 45608 45612 2 .x14
  wp_steps 2; step_sb8 ea hrun hx10 hv1 hv0 45620 45624 5 .x16
  wp_steps 3; step_sb8 ea hrun hx10 hv1 hv0 45636 45640 6 .x17
  wp_steps 1; step_sb8 ea hrun hx10 hv1 hv0 45644 45648 8 .x15
  wp_steps 3; step_sb8 ea hrun hx10 hv1 hv0 45660 45664 9 .x14
  wp_steps 7; step_sb8 ea hrun hx10 hv1 hv0 45692 45696 16 .x11
  wp_steps 1; step_sb8 ea hrun hx10 hv1 hv0 45700 45704 17 .x13
  wp_steps 1
  refine step_strSimd8_byteRange blkPl06.base ea 45708 45712 11 0#5 _ _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10, ea]) (by simp [hv0]; rfl) rfl ?_; intro _
  step_sb8 ea hrun hx10 hv1 hv0 45712 45716 14 .lr
  step_sb8 ea hrun hx10 hv1 hv0 45716 45720 18 .x24
  step_sb8 ea hrun hx10 hv1 hv0 45720 45724 4 .x28
  step_sb8 ea hrun hx10 hv1 hv0 45724 45728 13 .x18
  step_sb8 ea hrun hx10 hv1 hv0 45728 45732 15 .x16
  step_sb8 ea hrun hx10 hv1 hv0 45732 45736 19 .x12
  step_sb8 ea hrun hx10 hv1 hv0 45736 45740 20 .x11
  step_sb8 ea hrun hx10 hv1 hv0 45740 45744 21 .x13
  refine SepWP.weaken_pre
    (P' := (ea ↦ₛ ser11Chunk u c) ∗ (((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
      memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest))
    (sepConj_mono_left (Entails.of_eq ?_)) ?_
  · set vA := neonCompress8h 11 (polyVecNat u (2 * c))
    set vB := neonCompress8h 11 (polyVecNat u (2 * c + 1))
    have hmA : ∀ j : Fin 8, lane16 vA j &&& 0x07ff#16 = lane16 vA j := lane16_neonCompress8h_11_mask _
    have hmB : ∀ j : Fin 8, lane16 vB j &&& 0x07ff#16 = lane16 vB j := lane16_neonCompress8h_11_mask _
    have hcA := cells11_eq_neonSerialize11Half ea vA
    have hcB := cells11_eq_neonSerialize11Half (ea + 11#64) vB
    simp only [BitVec.truncate_eq_setWidth] at hcA
    simp only [BitVec.truncate_eq_setWidth, BitVec.add_assoc, BitVec.reduceAdd] at hcB
    change ByteRangeMem 22 ea _ = (ea ↦ₛ neonSerialize11Bytes vA vB)
    rw [byteRangeMem_split11, ← cells22_eq_neonSerialize11Bytes ea vA vB]
    refine congrArg₂ sepConj ?_ ?_
    · rw [byteRangeMem11_eq_cells]
      simp only [arm64_norm, Function.update, Nat.reduceEqDiff, dite_false, dite_true,
        BitVec.truncate_eq_setWidth, trunc32_zext64_shl, trunc32_zext64_shr, trunc8_trunc32_64]
      simp only [← BitVec.truncate_eq_setWidth,
        ser11_b0 vA (hmA 0),
        ser11_lsr _ 1 (hmA 5) (Or.inl rfl), ser11_lsr _ 2 (hmA 2) (Or.inr (Or.inl rfl)),
        ser11_lsr _ 3 (hmA 7) (Or.inr (Or.inr rfl)),
        ser11_shl_lsr _ _ 6 5 (hmA 1) (hmA 2) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 4 7 (hmA 3) (hmA 4) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 7 4 (hmA 4) (hmA 5) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 5 6 (hmA 6) (hmA 7) rfl (by decide) (by decide)]
      simp only [BitVec.truncate_eq_setWidth,
        ser11_b1_sw (hmA 0) (hmA 1), ser11_bfxil_4 (hmA 2) (hmA 3), ser11_bfxil_8 (hmA 5) (hmA 6)]
      exact hcA
    · rw [byteRangeMem11_eq_cells]
      simp only [arm64_norm, Function.update, Nat.reduceAdd, Nat.reduceEqDiff, dite_false, dite_true,
        BitVec.truncate_eq_setWidth, trunc32_zext64_shl, trunc32_zext64_shr, trunc8_trunc32_64]
      simp only [← BitVec.truncate_eq_setWidth,
        ser11_b0 vB (hmB 0),
        ser11_lsr _ 1 (hmB 5) (Or.inl rfl), ser11_lsr _ 2 (hmB 2) (Or.inr (Or.inl rfl)),
        ser11_lsr _ 3 (hmB 7) (Or.inr (Or.inr rfl)),
        ser11_shl_lsr _ _ 6 5 (hmB 1) (hmB 2) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 4 7 (hmB 3) (hmB 4) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 7 4 (hmB 4) (hmB 5) rfl (by decide) (by decide),
        ser11_shl_lsr _ _ 5 6 (hmB 6) (hmB 7) rfl (by decide) (by decide)]
      simp only [BitVec.truncate_eq_setWidth,
        ser11_b1_sw (hmB 0) (hmB 1), ser11_bfxil_4 (hmB 2) (hmB 3), ser11_bfxil_8 (hmB 5) (hmB 6)]
      exact hcB
  have hp_join :
      (ea ↦ₛ ser11Chunk u c) ∗ (((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest) ⊢
      ((sp + 33888#64) ↦ₛ ser11Prefix u (c + 1)) ∗
        memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest := by
    have hea : ea = (sp + 33888#64) + BitVec.ofNat 64 (22 * c) := by
      dsimp only [ea]; clear * - hc; bv_omega
    rw [hea, ← ser11_prefix_append_chunk]; sep_frame
  by_cases hc15 : c < 15
  · refine step_bCond_taken (dst := blkPl06.base + offSeg7Inner)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [hpst]; clear * - hc15
          rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | simp | omega)
      (by clear * -; dsimp [offSeg7Inner]; bv_omega) ?_
    refine SepWP.done (by dsimp only [nextPc]; simp [hc15]) (by simp [hrun])
      ⟨by simp [hsp], by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, hp_join⟩
  · have hc_eq : c = 15 := by omega
    subst hc_eq
    refine step_bCond_not_taken (dst := blkPl06.base + offSeg7Bounce)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [hpst]) (by clear * -; dsimp [offSeg7Bounce]; bv_omega) ?_
    refine SepWP.done (by dsimp only [nextPc]; simp) (by simp [hrun])
      ⟨by simp [hsp], by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, hp_join⟩

end InnerStore

/-! ## 5. Full 16-Iteration Inner Loop, Bounce Copies, & Outer Loop (`+0xb040 → +0xb308`) -/

private theorem seg7_inner_from [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (u : Poly16) (sp : BitVec 64) (Rest : SepProp) :
    ∀ (rem c : Nat), rem + c = 16 → ∀ (s : State),
      s.pc = (if c < 16 then b + offSeg7Inner else b + offSeg7Bounce) →
      s.status = .Running → s.sp = sp →
      s.readReg64 .x8 = BitVec.ofNat 64 (22 * c) →
      s.readReg64 .x9 = sp + BitVec.ofNat 64 (30464 + 32 * c) →
      s.readReg64 .x26 = sp + 33888#64 →
      s.readVReg128 5#5 = c3329Vec → s.readVReg128 6#5 = c134215680Vec →
      s.readVReg128 7#5 = c1664Vec → s.readVReg128 16#5 = c10321340Vec →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Bounce) s
        (PolyMem (sp + 30448#64) (polyVecNat u) ∗ ((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
          memRegion (sp + BitVec.ofNat 64 (33888 + 22 * c)) (352 - 22 * c) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = s.spAligned ∧ PresFp19 sf (s.readReg64 .fp) (s.readReg64 .x19) ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧
          (Pf ⊢ PolyMem (sp + 30448#64) (polyVecNat u) ∗
            ((sp + 33888#64) ↦ₛ neonCompressSerialize11Poly u) ∗ Rest)) := by
  intro rem c
  induction rem generalizing c with
  | zero =>
    intro hrc s hpc hrun hsp _ _ _ _ _ _ _
    have hc_eq : c = 16 := by omega
    subst hc_eq
    have hpc' : s.pc = b + offSeg7Bounce := by simpa using hpc
    refine SepWP.done hpc' hrun ⟨hsp, rfl, PresFp19.rfl_of s, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [ser11Prefix_sixteen, show 352 - 22 * 16 = 0 by decide, memRegion_zero]; sep_frame
  | succ rem ih =>
    intro hrc s hpc hrun hsp hx8 hx9 hx26 hv5 hv6 hv7 hv16
    have hc16 : c < 16 := by omega
    have hpc' : s.pc = b + offSeg7Inner := by simpa [hc16] using hpc
    refine SepWP.seq (seg7_inner_simd hb hbase s sp hc16 u _ hpc' hrun hsp hx8 hx9 hx26 hv5 hv6 hv7 hv16) ?_
    rintro s1 _ hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hp1, hv1_1, hv0_1, rfl⟩
    refine SepWP.weaken_pre
      (show PolyMem (sp + 30448#64) (polyVecNat u) ∗ (((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
          memRegion (sp + BitVec.ofNat 64 (33888 + 22 * c)) (352 - 22 * c) ∗ Rest) ⊢
        ((sp + 33888#64) ↦ₛ ser11Prefix u c) ∗
          memRegion (sp + BitVec.ofNat 64 (33888 + 22 * c)) (352 - 22 * c) ∗
          (PolyMem (sp + 30448#64) (polyVecNat u) ∗ Rest) by sep_frame) ?_
    refine SepWP.seq (seg7_inner_store hb hbase s1 sp hc16 u _ hpc1 hrun1 hsp1 hpst1 hx10_1 hv1_1 hv0_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, rfp2, rx8_2, rx9_2, rx20_2, rx21_2, rx22_2, rx23_2,
      rx25_2, rx26_2, rx27_2, rv5_2, rv6_2, rv7_2, rv16_2, hP2⟩
    have hpc2' : s2.pc = if c + 1 < 16 then b + offSeg7Inner else b + offSeg7Bounce := by
      have hiff : (c + 1 < 16) ↔ (c < 15) := by omega
      simpa [hiff] using hpc2
    refine SepWP.weaken_pre
      (P' := PolyMem (sp + 30448#64) (polyVecNat u) ∗ ((sp + 33888#64) ↦ₛ ser11Prefix u (c + 1)) ∗
        memRegion (sp + BitVec.ofNat 64 (33888 + 22 * (c + 1))) (352 - 22 * (c + 1)) ∗ Rest)
      (Entails.trans hP2 (by sep_frame)) ?_
    refine SepWP.mono (ih (c + 1) (by omega) s2 hpc2' hrun2 hsp2
      (rx8_2.trans hx8_1) (rx9_2.trans hx9_1) ((rx26_2.trans hp1.x26).trans hx26)
      (rv5_2.trans hp1.v5) (rv6_2.trans hp1.v6) (rv7_2.trans hp1.v7) (rv16_2.trans hp1.v16)) ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, rfp_f, rx20_f, rx21_f, rx22_f, rx23_f, rx25_f, rx26_f, rx27_f, hPf⟩
    exact ⟨hsp_f, hspA_f.trans (hspA2.trans hspA1), rfp_f.trans (rfp2.trans hp1.fp),
      rx20_f.trans (rx20_2.trans hp1.x20), rx21_f.trans (rx21_2.trans hp1.x21),
      rx22_f.trans (rx22_2.trans hp1.x22), rx23_f.trans (rx23_2.trans hp1.x23),
      rx25_f.trans (rx25_2.trans hp1.x25), rx26_f.trans (rx26_2.trans hp1.x26),
      rx27_f.trans (rx27_2.trans hp1.x27), hPf⟩

private theorem seg7_bounce [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) {idx : Nat} (hidx : idx < 4)
    (bs : List (BitVec 8)) (hbs : bs.length = 352) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Bounce) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hx21 : s.readReg64 .x21 = sp + 14448#64)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (352 * idx))
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (idx + 1)) (hx25 : s.readReg64 .x25 = 352#64)
    (hx26 : s.readReg64 .x26 = sp + 33888#64) (hx27 : s.readReg64 .x27 = sp + 24704#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let outPtr := sp + BitVec.ofNat 64 (24704 + 352 * idx)
    let nextPc := if idx < 3 then b + offSeg7Outer else b + offSeg7RhatCopy
    SepWP (blkPC06.rebase b (fun _ => none)) nextPc s
      (((sp + 33888#64) ↦ₛ bs) ∗ memRegion (sp + 33536#64) 352 ∗ memRegion outPtr 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14448#64 ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x25 = 352#64 ∧
        sf.readReg64 .x26 = sp + 33888#64 ∧ sf.readReg64 .x27 = sp + 24704#64 ∧
        (Pf ⊢ (outPtr ↦ₛ bs) ∗ memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗ Rest)) := by
  subst hbase; intro outPtr nextPc
  have hout : (sp + 24704#64) + BitVec.ofNat 64 (352 * idx) = outPtr := by
    dsimp only [outPtr]; clear * - hidx; bv_omega
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 33536#64) 352 ∗ ((sp + 33888#64) ↦ₛ bs) ∗ (memRegion outPtr 352 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_cl hcl (mid := blkPl06.base + BitVec.ofNat 64 45772)
    (post1 := fun s1 P1 =>
      s1.sp = sp ∧ s1.spAligned = true ∧ PresFp19 s1 fpVal x19Val ∧
      s1.readReg64 .x20 = sp + 30448#64 ∧ s1.readReg64 .x21 = sp + 14448#64 ∧
      s1.readReg64 .x22 = BitVec.ofNat 64 (352 * idx) ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ s1.readReg64 .x25 = 352#64 ∧
      s1.readReg64 .x26 = sp + 33888#64 ∧ s1.readReg64 .x27 = sp + 24704#64 ∧
      (P1 ⊢ memRegion outPtr 352 ∗ ((sp + 33536#64) ↦ₛ bs) ∗ (((sp + 33888#64) ↦ₛ bs) ∗ Rest)))
    (by
      wp_cut_codeLoaded; wp_steps 6
      apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl1
      wp_call (blk28_memcpy_06 blkPl06.base) (sp + 33536#64, sp + 33888#64, bs)
      have hsp1 : sf.sp = sp := by simp [*]
      refine SepWP.done (by wp_norm_lhs) (by simp [*])
        ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*], by simp [*],
          by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
      sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 _hcl1 ⟨hsp1, hspA1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  wp_cut_codeLoaded; wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl2
  rw [← hout]
  wp_call (blk28_memcpy_06 blkPl06.base) ((sp + 24704#64) + BitVec.ofNat 64 (352 * idx), sp + 33536#64, bs)
  rw [hout]
  wp_steps 1
  have hm33888 : ((sp + 33888#64) ↦ₛ bs) ⊢ memRegion (sp + 33888#64) 352 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp + 33888#64) bs
  have hm33536 : ((sp + 33536#64) ↦ₛ bs) ⊢ memRegion (sp + 33536#64) 352 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp + 33536#64) bs
  have hP : (outPtr ↦ₛ bs) ∗ ((sp + 33536#64) ↦ₛ bs) ∗ (((sp + 33888#64) ↦ₛ bs) ∗ Rest) ⊢
      (outPtr ↦ₛ bs) ∗ memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗ Rest :=
    entails_sub hm33536 (by sep_frame) (entails_sub hm33888 (by sep_frame) (by sep_frame))
  by_cases hidx3 : idx < 3
  · refine step_bCond_taken (dst := blkPl06.base + offSeg7Outer)
      (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
      (by simp [*]; clear * - hidx3; rcases idx with _ | _ | _ | n <;> first | simp | omega)
      (by clear * -; dsimp [offSeg7Outer]; bv_omega) ?_
    exact SepWP.done (by dsimp only [nextPc]; simp [hidx3]) (by simp [*])
      ⟨by simp [*], spAligned_of_sp_eq hspA1 hsp1 (by simp [*]), by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*], hP⟩
  · have hidx_eq : idx = 3 := by omega
    subst hidx_eq
    refine step_bCond_not_taken (dst := blkPl06.base + offSeg7RhatCopy)
      (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
      (by simp [*]) (by clear * -; dsimp [offSeg7RhatCopy]; bv_omega) ?_
    exact SepWP.done (by dsimp only [nextPc]; simp) (by simp [*])
      ⟨by simp [*], spAligned_of_sp_eq hspA1 hsp1 (by simp [*]), by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*], hP⟩

private theorem seg7_poly_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) {idx : Nat} (hidx : idx < 4) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hx21 : s.readReg64 .x21 = sp + 14448#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 idx) (hx25 : s.readReg64 .x25 = 352#64)
    (hx26 : s.readReg64 .x26 = sp + 33888#64) (hx27 : s.readReg64 .x27 = sp + 24704#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (14448 + 512 * idx)
    let outPtr := sp + BitVec.ofNat 64 (24704 + 352 * idx)
    let nextPc := if idx < 3 then b + offSeg7Outer else b + offSeg7RhatCopy
    SepWP (blkPC06.rebase b (fun _ => none)) nextPc s
      (PolyMem uPtr (polyVecNat u) ∗ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
        memRegion outPtr 352 ∗ memRegion (sp + 30448#64) 520 ∗
        memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
        memRegion (sp + 33888#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14448#64 ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 (idx + 1) ∧ sf.readReg64 .x25 = 352#64 ∧
        sf.readReg64 .x26 = sp + 33888#64 ∧ sf.readReg64 .x27 = sp + 24704#64 ∧
        (Pf ⊢ PolyMem uPtr (polyVecNat u) ∗ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
          (outPtr ↦ₛ neonCompressSerialize11Poly u) ∗ memRegion (sp + 30448#64) 520 ∗
          memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
          memRegion (sp + 33888#64) 352 ∗ Rest)) := by
  intro uPtr outPtr nextPc
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_cl hcl (seg7_prep_poly hb hbase s sp fpVal x19Val hidx u _ hpc hrun hsp hspA hfp hx20 hx21 hx23 hx25 hx26 hx27 hcl) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hP1⟩
  refine SepWP.weaken_pre
    (P' := VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ memRegion (sp + 33888#64) 352 ∗
      (PolyMem uPtr (polyVecNat u) ∗ PolyMem (sp + 30448#64) (polyVecNat u) ∗
        memRegion (sp + 30960#64) 8 ∗ memRegion (sp + 33008#64) 520 ∗
        memRegion outPtr 352 ∗ memRegion (sp + 33536#64) 352 ∗ Rest))
    (Entails.trans hP1 (by sep_frame)) ?_
  refine sepWP_seq_cl hcl1 (seg7_zero_load hb hbase s1 sp fpVal x19Val _ hpc1 hrun1 hsp1 hspA1 hfp1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hspA2, hfp2, hx8_2, hx9_2, hx20_2, rx21_2, rx22_2, rx23_2, rx25_2, rx26_2, rx27_2,
    hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  have hpfx0 : ((sp + 33888#64) ↦ₛ ser11Prefix u 0) = emp := by
    dsimp [ser11Prefix]; exact pointsToBytes_nil _
  have ha0 : sp + BitVec.ofNat 64 (33888 + 22 * 0) = sp + 33888#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre
    (P' := PolyMem (sp + 30448#64) (polyVecNat u) ∗ ((sp + 33888#64) ↦ₛ ser11Prefix u 0) ∗
      memRegion (sp + BitVec.ofNat 64 (33888 + 22 * 0)) (352 - 22 * 0) ∗
      (VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 30960#64) 8 ∗ memRegion (sp + 33008#64) 520 ∗
        memRegion outPtr 352 ∗ memRegion (sp + 33536#64) 352 ∗ Rest))
    (Entails.trans hP2 (by rw [hpfx0, ha0]; sep_frame)) ?_
  refine sepWP_seq_cl hcl2 (seg7_inner_from hb hbase u sp _ 16 0 rfl s2 (by simpa using hpc2) hrun2 hsp2
    hx8_2 (by simpa using hx9_2) (rx26_2.trans hx26_1) hv5_2 hv6_2 hv7_2 hv16_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hsp3, hspA3, rfp3, rx20_3, rx21_3, rx22_3, rx23_3, rx25_3, rx26_3, rx27_3, hP3⟩
  refine SepWP.weaken_pre
    (P' := ((sp + 33888#64) ↦ₛ neonCompressSerialize11Poly u) ∗ memRegion (sp + 33536#64) 352 ∗
      memRegion outPtr 352 ∗
      (PolyMem (sp + 30448#64) (polyVecNat u) ∗ VecRangeMem 4 (sp + 2368#64) ser11ConstFn ∗
        PolyMem uPtr (polyVecNat u) ∗ memRegion (sp + 30960#64) 8 ∗
        memRegion (sp + 33008#64) 520 ∗ Rest))
    (Entails.trans hP3 (by sep_frame)) ?_
  refine SepWP.mono (seg7_bounce hb hbase s3 sp fpVal x19Val hidx (neonCompressSerialize11Poly u)
    (neonCompressSerialize11Poly_length u) _ hpc3 hrun3 hsp3 (hspA3.trans hspA2) (rfp3.trans hfp2)
    (rx20_3.trans hx20_2) ((rx21_3.trans rx21_2).trans hx21_1) ((rx22_3.trans rx22_2).trans hx22_1)
    ((rx23_3.trans rx23_2).trans hx23_1) ((rx25_3.trans rx25_2).trans hx25_1)
    ((rx26_3.trans rx26_2).trans hx26_1) ((rx27_3.trans rx27_2).trans hx27_1) hcl3) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx20_f, hx21_f, hx23_f, hx25_f, hx26_f, hx27_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hfp_f, hx20_f, hx21_f, hx23_f, hx25_f, hx26_f, hx27_f, Entails.trans hPf ?_⟩
  have hm520 : PolyMem (sp + 30448#64) (polyVecNat u) ∗ memRegion (sp + 30960#64) 8 ⊢
      memRegion (sp + 30448#64) 520 := by
    have hm := memRegion_split' (b := sp + 30448#64) (b' := sp + 30960#64) (n := 512) (k := (8 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
    rw [show 512 + 8 = 520 by decide] at hm
    rw [hm]
    exact sepConj_mono_left (vecRangeMem_entails_memRegion 32 (sp + 30448#64) (polyVecNat u))
  exact entails_sub hm520 (by sep_frame) (by sep_frame)

private theorem seg7_rhat_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) (r0 r1 r2 r3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7RhatCopy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Start) s
      (PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
        PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
        memRegion (sp + 14432#64) 2048 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 14432#64 ∧
        (Pf ⊢ PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
          PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
          memRegion (sp + 26320#64) 2048 ∗ Rest)) := by
  subst hbase
  generalize hbs_def : vecRangeBytes 32 (polyVecNat r0) ++ vecRangeBytes 32 (polyVecNat r1) ++
    vecRangeBytes 32 (polyVecNat r2) ++ vecRangeBytes 32 (polyVecNat r3) = bs
  have hbs : bs.length = 2048 := by rw [← hbs_def]; simp [List.length_append, vecRangeBytes_length]
  have hpSrc := polyMem4_eq_pointsToBytes (sp + 26320#64) r0 r1 r2 r3
  have hpDst := polyMem4_eq_pointsToBytes (sp + 14432#64) r0 r1 r2 r3
  rw [hbs_def] at hpSrc hpDst
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpSrc hpDst
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp + 14432#64) 2048 ∗ ((sp + 26320#64) ↦ₛ bs) ∗ Rest by
      exact entails_sub (Entails.of_eq hpSrc) (by sep_frame) (by sep_frame)) ?_
  wp_cut_codeLoaded; wp_steps 8
  apply SepWP.done (by wp_norm_lhs) (by assumption); intro _hcl1
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 14432#64, sp + 26320#64, bs)
  rw [← hpDst]
  have hsp1 : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp1, spAligned_of_sp_eq hspA hsp hsp1, by simp [*], by simp [*], ?_⟩
  have hm26 : ((sp + 26320#64) ↦ₛ bs) ⊢ memRegion (sp + 26320#64) 2048 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp + 26320#64) bs
  exact entails_sub hm26 (by sep_frame) (by sep_frame)

/-- `1,408`-byte `c₁'` byte list written by `Seg7UvecC1` at `[sp + 24704, sp + 26112)`. -/
noncomputable def c1Bytes06 (rho coins : List (BitVec 8)) : List (BitVec 8) :=
  neonCompressSerialize11Poly (uVecPoly06 rho coins 0) ++
  neonCompressSerialize11Poly (uVecPoly06 rho coins 1) ++
  neonCompressSerialize11Poly (uVecPoly06 rho coins 2) ++
  neonCompressSerialize11Poly (uVecPoly06 rho coins 3)

theorem c1Bytes06_length (rho coins : List (BitVec 8)) :
    (c1Bytes06 rho coins).length = 1408 := by
  simp [c1Bytes06, List.length_append, neonCompressSerialize11Poly_length]

theorem c1Bytes06_spec (rho : List (BitVec 8)) {coins : List (BitVec 8)}
    (hcoins : coins.length = 32) :
    let aTrans := sampleMatrixWith sampleNtt 4 rho false
    let rHat := (sampleVecCbd2 4 coins 0).map polyNtt
    let e1Vec := sampleVecCbd2 4 coins 4
    let uVec := (List.range 4).map fun i =>
      polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD i #[]) rHat)) (e1Vec.getD i zeroPoly)
    c1Bytes06 rho coins = (uVec.map (compressAndEncode 11)).flatten := by
  intro aTrans rHat e1Vec uVec
  have hrow : ∀ r, r < 4 →
      neonCompressSerialize11Poly (uVecPoly06 rho coins r) =
        compressAndEncode 11
          (polyAdd (polyInvNtt (vecDotNtt 4 (aTrans.getD r #[]) rHat)) (e1Vec.getD r zeroPoly)) := by
    intro r hr
    obtain ⟨hbnd, hrep⟩ := uVecPoly06_spec rho hcoins hr
    exact neonCompressSerialize11Poly_eq hbnd hrep
  dsimp only [c1Bytes06, uVec]
  rw [hrow 0 (by decide), hrow 1 (by decide), hrow 2 (by decide), hrow 3 (by decide)]
  simp [List.range_succ, List.append_assoc]

private theorem split_2000_368 (sp : BitVec 64) :
    memRegion (sp + 2000#64) 432 = memRegion (sp + 2000#64) 368 ∗ memRegion (sp + 2368#64) 64 := by
  simpa using memRegion_split' (b := sp + 2000#64) (b' := sp + 2368#64) (n := 368) (k := (64 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_14432_512' (sp : BitVec 64) :
    memRegion (sp + 14432#64) 2072 = memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1560 := by
  simpa using memRegion_split' (b := sp + 14432#64) (b' := sp + 14944#64) (n := 512) (k := (1560 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_14432_uvec (sp : BitVec 64) :
    memRegion (sp + 14432#64) 2072 =
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗
      memRegion (sp + 14448#64) 2048 ∗ memRegion (sp + 16496#64) 8 := by
  have h1 := memRegion_split' (b := sp + 14432#64) (b' := sp + 14440#64) (n := 8) (k := (2064 : Nat))
    rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp + 14440#64) (b' := sp + 14448#64) (n := 8) (k := (2056 : Nat))
    rfl (by bv_omega) (by decide)
  have h3 := memRegion_split' (b := sp + 14448#64) (b' := sp + 16496#64) (n := 2048) (k := (8 : Nat))
    rfl (by bv_omega) (by decide)
  change memRegion (sp + 14432#64) (8 + 2064) = _
  rw [h1]; change _ ∗ memRegion (sp + 14440#64) (8 + 2056) = _
  rw [h2]; change _ ∗ (_ ∗ memRegion (sp + 14448#64) (2048 + 8)) = _
  rw [h3]

private theorem split_14432_2048 (sp : BitVec 64) :
    memRegion (sp + 14432#64) 2072 = memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 16480#64) 24 := by
  simpa using memRegion_split' (b := sp + 14432#64) (b' := sp + 16480#64) (n := 2048) (k := (24 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_24704_4x352 (sp : BitVec 64) :
    memRegion (sp + 24704#64) 1408 =
      memRegion (sp + 24704#64) 352 ∗ memRegion (sp + 25056#64) 352 ∗
      memRegion (sp + 25408#64) 352 ∗ memRegion (sp + 25760#64) 352 := by
  have h1 := memRegion_split' (b := sp + 24704#64) (b' := sp + 25056#64) (n := 352) (k := (1056 : Nat))
    rfl (by bv_omega) (by decide)
  have h2 := memRegion_split' (b := sp + 25056#64) (b' := sp + 25408#64) (n := 352) (k := (704 : Nat))
    rfl (by bv_omega) (by decide)
  have h3 := memRegion_split' (b := sp + 25408#64) (b' := sp + 25760#64) (n := 352) (k := (352 : Nat))
    rfl (by bv_omega) (by decide)
  change memRegion (sp + 24704#64) (352 + 1056) = _
  rw [h1]; change _ ∗ memRegion (sp + 25056#64) (352 + 704) = _
  rw [h2]; change _ ∗ (_ ∗ memRegion (sp + 25408#64) (352 + 352)) = _
  rw [h3]

private theorem split_30448_520 (sp : BitVec 64) :
    memRegion (sp + 30448#64) 2048 = memRegion (sp + 30448#64) 520 ∗ memRegion (sp + 30968#64) 1528 := by
  simpa using memRegion_split' (b := sp + 30448#64) (b' := sp + 30968#64) (n := 520) (k := (1528 : Nat))
    rfl (by bv_omega) (by decide)

private theorem polyMem4_entails_memRegion2048 (a : BitVec 64) (u0 u1 u2 u3 : Poly16) :
    PolyMem a (polyVecNat u0) ∗ PolyMem (a + 512#64) (polyVecNat u1) ∗
      PolyMem (a + 1024#64) (polyVecNat u2) ∗ PolyMem (a + 1536#64) (polyVecNat u3) ⊢
    memRegion a 2048 := by
  rw [polyMem4_eq_pointsToBytes]
  have hlen : (vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
      vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3)).length = 2048 := by
    simp [List.length_append, vecRangeBytes_length]
  rw [← hlen]; exact pointsToBytes_entails_memRegion a _

private theorem c1_join4 (sp : BitVec 64) (b0 b1 b2 b3 : List (BitVec 8))
    (h0 : b0.length = 352) (h1 : b1.length = 352) (h2 : b2.length = 352) :
    ((sp + 24704#64) ↦ₛ b0) ∗ ((sp + 25056#64) ↦ₛ b1) ∗
      ((sp + 25408#64) ↦ₛ b2) ∗ ((sp + 25760#64) ↦ₛ b3) =
    ((sp + 24704#64) ↦ₛ (b0 ++ b1 ++ b2 ++ b3)) := by
  simp only [List.append_assoc, pointsToBytes_append, h0, h1, h2, BitVec.add_assoc, BitVec.reduceAdd]

private theorem seg7_c1_part [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal x19Val : BitVec 64) (u0 u1 u2 u3 r0 r1 r2 r3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Mid) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : PresFp19 s fpVal x19Val)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Start) s
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 14432#64) 2072 ∗
        memRegion (sp + 24704#64) 1408 ∗
        PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
        PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
        PolyMem (sp + 30448#64) (polyVecNat u0) ∗ PolyMem (sp + 30960#64) (polyVecNat u1) ∗
        PolyMem (sp + 31472#64) (polyVecNat u2) ∗ PolyMem (sp + 31984#64) (polyVecNat u3) ∗
        memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
        memRegion (sp + 33888#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ PresFp19 sf fpVal x19Val ∧
        sf.readReg64 .x20 = sp + 14432#64 ∧ mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 2368#64) 64 ∗
          PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
          PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
          memRegion (sp + 16480#64) 24 ∗
          ((sp + 24704#64) ↦ₛ (neonCompressSerialize11Poly u0 ++ neonCompressSerialize11Poly u1 ++
            neonCompressSerialize11Poly u2 ++ neonCompressSerialize11Poly u3)) ∗
          memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
          memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
          memRegion (sp + 33888#64) 352 ∗ Rest)) := by
  rw [split_14432_uvec sp, split_24704_4x352 sp]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_cl hcl (seg7_uvec_copy hb hbase s sp fpVal x19Val u0 u1 u2 u3 _ hpc hrun hsp hspA hfp hcl) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hfp1, hx20_1, hx21_1, hP1⟩
  rw [split_30448_520 sp] at hP1
  have hhdr := seg7_header hb hbase s1 sp fpVal x19Val
    (PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 14960#64) (polyVecNat u1) ∗
      PolyMem (sp + 15472#64) (polyVecNat u2) ∗ PolyMem (sp + 15984#64) (polyVecNat u3) ∗
      memRegion (sp + 30448#64) 520 ∗ memRegion (sp + 30968#64) 1528 ∗
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 24704#64) 352 ∗
      memRegion (sp + 25056#64) 352 ∗ memRegion (sp + 25408#64) 352 ∗
      memRegion (sp + 25760#64) 352 ∗ PolyMem (sp + 26320#64) (polyVecNat r0) ∗
      PolyMem (sp + 26832#64) (polyVecNat r1) ∗ PolyMem (sp + 27344#64) (polyVecNat r2) ∗
      PolyMem (sp + 27856#64) (polyVecNat r3) ∗ memRegion (sp + 33008#64) 520 ∗
      memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗ Rest)
    hpc1 hrun1 hsp1 hspA1 hfp1 hx20_1 hx21_1
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame)) (sepWP_seq_cl hcl1 hhdr ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hspA2, hfp2, hx20_2, hx21_2, hx23_2, hx25_2, hx26_2, hx27_2, hP2⟩
  have hu0_a : sp + BitVec.ofNat 64 (14448 + 512 * 0) = sp + 14448#64 := by clear * -; bv_omega
  have hu1_a : sp + BitVec.ofNat 64 (14448 + 512 * 1) = sp + 14960#64 := by clear * -; bv_omega
  have hu2_a : sp + BitVec.ofNat 64 (14448 + 512 * 2) = sp + 15472#64 := by clear * -; bv_omega
  have hu3_a : sp + BitVec.ofNat 64 (14448 + 512 * 3) = sp + 15984#64 := by clear * -; bv_omega
  have ho0_a : sp + BitVec.ofNat 64 (24704 + 352 * 0) = sp + 24704#64 := by clear * -; bv_omega
  have ho1_a : sp + BitVec.ofNat 64 (24704 + 352 * 1) = sp + 25056#64 := by clear * -; bv_omega
  have ho2_a : sp + BitVec.ofNat 64 (24704 + 352 * 2) = sp + 25408#64 := by clear * -; bv_omega
  have ho3_a : sp + BitVec.ofNat 64 (24704 + 352 * 3) = sp + 25760#64 := by clear * -; bv_omega
  have hit0 := seg7_poly_iter hb hbase s2 sp fpVal x19Val (idx := 0) (by decide) u0
    (PolyMem (sp + 14960#64) (polyVecNat u1) ∗ PolyMem (sp + 15472#64) (polyVecNat u2) ∗
      PolyMem (sp + 15984#64) (polyVecNat u3) ∗ memRegion (sp + 25056#64) 352 ∗
      memRegion (sp + 25408#64) 352 ∗ memRegion (sp + 25760#64) 352 ∗
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      memRegion (sp + 30968#64) 1528 ∗ Rest)
    hpc2 hrun2 hsp2 hspA2 hfp2 hx20_2 hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 hcl2
  dsimp only at hit0; simp only [show (0 : Nat) < 3 by decide, ↓reduceIte, hu0_a, ho0_a] at hit0
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) (sepWP_seq_cl hcl2 hit0 ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hsp3, hspA3, hfp3, hx20_3, hx21_3, hx23_3, hx25_3, hx26_3, hx27_3, hP3⟩
  have hit1 := seg7_poly_iter hb hbase s3 sp fpVal x19Val (idx := 1) (by decide) u1
    (PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 15472#64) (polyVecNat u2) ∗
      PolyMem (sp + 15984#64) (polyVecNat u3) ∗ ((sp + 24704#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      memRegion (sp + 25408#64) 352 ∗ memRegion (sp + 25760#64) 352 ∗
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      memRegion (sp + 30968#64) 1528 ∗ Rest)
    hpc3 hrun3 hsp3 hspA3 hfp3 hx20_3 hx21_3 hx23_3 hx25_3 hx26_3 hx27_3 hcl3
  dsimp only at hit1; simp only [show (1 : Nat) < 3 by decide, ↓reduceIte, hu1_a, ho1_a] at hit1
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame)) (sepWP_seq_cl hcl3 hit1 ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 ⟨hsp4, hspA4, hfp4, hx20_4, hx21_4, hx23_4, hx25_4, hx26_4, hx27_4, hP4⟩
  have hit2 := seg7_poly_iter hb hbase s4 sp fpVal x19Val (idx := 2) (by decide) u2
    (PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 14960#64) (polyVecNat u1) ∗
      PolyMem (sp + 15984#64) (polyVecNat u3) ∗ ((sp + 24704#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      ((sp + 25056#64) ↦ₛ neonCompressSerialize11Poly u1) ∗ memRegion (sp + 25760#64) 352 ∗
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      memRegion (sp + 30968#64) 1528 ∗ Rest)
    hpc4 hrun4 hsp4 hspA4 hfp4 hx20_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hcl4
  dsimp only at hit2; simp only [show (2 : Nat) < 3 by decide, ↓reduceIte, hu2_a, ho2_a] at hit2
  refine SepWP.weaken_pre (Entails.trans hP4 (by sep_frame)) (sepWP_seq_cl hcl4 hit2 ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 ⟨hsp5, hspA5, hfp5, hx20_5, hx21_5, hx23_5, hx25_5, hx26_5, hx27_5, hP5⟩
  have hit3 := seg7_poly_iter hb hbase s5 sp fpVal x19Val (idx := 3) (by decide) u3
    (PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 14960#64) (polyVecNat u1) ∗
      PolyMem (sp + 15472#64) (polyVecNat u2) ∗ ((sp + 24704#64) ↦ₛ neonCompressSerialize11Poly u0) ∗
      ((sp + 25056#64) ↦ₛ neonCompressSerialize11Poly u1) ∗
      ((sp + 25408#64) ↦ₛ neonCompressSerialize11Poly u2) ∗
      memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗ memRegion (sp + 16496#64) 8 ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      memRegion (sp + 30968#64) 1528 ∗ Rest)
    hpc5 hrun5 hsp5 hspA5 hfp5 hx20_5 hx21_5 hx23_5 hx25_5 hx26_5 hx27_5 hcl5
  dsimp only at hit3; simp only [Nat.lt_irrefl, ↓reduceIte, hu3_a, ho3_a] at hit3
  refine SepWP.weaken_pre (Entails.trans hP5 (by sep_frame)) (sepWP_seq_cl hcl5 hit3 ?_)
  rintro s6 P6 hpc6 hrun6 hcl6 ⟨hsp6, hspA6, hfp6, _, _, _, _, _, _, hP6⟩
  have hmU : PolyMem (sp + 14448#64) (polyVecNat u0) ∗ PolyMem (sp + 14960#64) (polyVecNat u1) ∗
      PolyMem (sp + 15472#64) (polyVecNat u2) ∗ PolyMem (sp + 15984#64) (polyVecNat u3) ⊢
      memRegion (sp + 14448#64) 2048 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using polyMem4_entails_memRegion2048 (sp + 14448#64) u0 u1 u2 u3
  have hm14_rejoin : memRegion (sp + 14432#64) 8 ∗ memRegion (sp + 14440#64) 8 ∗
      memRegion (sp + 14448#64) 2048 ∗ memRegion (sp + 16496#64) 8 =
      memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 16480#64) 24 :=
    (split_14432_uvec sp).symm.trans (split_14432_2048 sp)
  have hm30_rejoin := (split_30448_520 sp).symm
  have hm2368 := vecRangeMem_entails_memRegion 4 (sp + 2368#64) ser11ConstFn
  have hc1 := c1_join4 sp _ _ _ (neonCompressSerialize11Poly u3)
    (neonCompressSerialize11Poly_length u0) (neonCompressSerialize11Poly_length u1)
    (neonCompressSerialize11Poly_length u2)
  have hP6' : P6 ⊢ PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      memRegion (sp + 14432#64) 2048 ∗
      (memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 16480#64) 24 ∗
        ((sp + 24704#64) ↦ₛ (neonCompressSerialize11Poly u0 ++ neonCompressSerialize11Poly u1 ++
          neonCompressSerialize11Poly u2 ++ neonCompressSerialize11Poly u3)) ∗
        memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 520 ∗
        memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗ Rest) := by
    refine Entails.trans hP6 ?_
    refine entails_sub hmU (by sep_frame) (entails_sub hm2368 (by sep_frame) ?_)
    refine entails_sub (Entails.of_eq hm14_rejoin) (by sep_frame) ?_
    refine entails_sub (Entails.of_eq hm30_rejoin) (by sep_frame) ?_
    refine entails_sub (Entails.of_eq hc1) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP6'
    (sepWP_seq_cl hcl6 (seg7_rhat_copy hb hbase s6 sp fpVal x19Val r0 r1 r2 r3 _ hpc6 hrun6 hsp6 hspA6 hfp6 hcl6) ?_)
  rintro sf Pf hpc_f hrun_f hcl_f ⟨hsp_f, hspA_f, hfp_f, hx20_f, hPf⟩
  exact SepWP.done hpc_f hrun_f ⟨hsp_f, hspA_f, hfp_f, hx20_f, hcl_f, Entails.trans hPf (by sep_frame)⟩

/-- Full Segment 7 (`+0x9380 → +0xb308`): `uVec` + `compress_and_serialize_11` (`c₁'`) + `r̂` copy. -/
theorem seg7_uvec_c1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp fpVal : BitVec 64) (rho coins : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let r0 := rHatPoly16 (shake256List 128 (coins ++ [0#8]))
    let r1 := rHatPoly16 (shake256List 128 (coins ++ [1#8]))
    let r2 := rHatPoly16 (shake256List 128 (coins ++ [2#8]))
    let r3 := rHatPoly16 (shake256List 128 (coins ++ [3#8]))
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [6#8]))
    let e1_3 := neonCbd2Poly16 (shake256List 128 (coins ++ [7#8]))
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Start) s
      (memRegion (sp + 2000#64) 432 ∗ ATransAt (sp + 4160#64) rho ∗
        memRegion (sp + 14432#64) 2072 ∗ memRegion (sp + 24704#64) 1408 ∗
        PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
        PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
        PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗ PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗
        PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗ PolyMem (sp + 29904#64) (polyVecNat e1_3) ∗
        PolyMem (sp + 30448#64) (fun _ => 0#128) ∗ PolyMem (sp + 30960#64) (fun _ => 0#128) ∗
        PolyMem (sp + 31472#64) (fun _ => 0#128) ∗ PolyMem (sp + 31984#64) (fun _ => 0#128) ∗
        memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
        memRegion (sp + 33888#64) 352 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 12352#64 ∧ sf.readReg64 .x20 = sp + 14432#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 2000#64) 432 ∗ ATransAt (sp + 4160#64) rho ∗
          PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
          PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
          memRegion (sp + 16480#64) 24 ∗ ((sp + 24704#64) ↦ₛ c1Bytes06 rho coins) ∗
          memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 2048 ∗
          memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 520 ∗
          memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗ Rest)) := by
  intro r0 r1 r2 r3 e1_0 e1_1 e1_2 e1_3
  rw [split_14432_512' sp]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro (seg7_uvec_ok hb s sp fpVal rho coins _ hpc hrun hsp hspA hx20 hfp hcl hro) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, _, _, hP1⟩
  have hm14 := (split_14432_512' sp).symm
  have hm2000 := split_2000_368 sp
  have hmE1 : PolyMem (sp + 28368#64) (polyVecNat e1_0) ∗ PolyMem (sp + 28880#64) (polyVecNat e1_1) ∗
      PolyMem (sp + 29392#64) (polyVecNat e1_2) ∗ PolyMem (sp + 29904#64) (polyVecNat e1_3) ⊢
      memRegion (sp + 28368#64) 2048 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      polyMem4_entails_memRegion2048 (sp + 28368#64) e1_0 e1_1 e1_2 e1_3
  have hP1' : P1 ⊢ memRegion (sp + 2368#64) 64 ∗ memRegion (sp + 14432#64) 2072 ∗
      memRegion (sp + 24704#64) 1408 ∗
      PolyMem (sp + 26320#64) (polyVecNat r0) ∗ PolyMem (sp + 26832#64) (polyVecNat r1) ∗
      PolyMem (sp + 27344#64) (polyVecNat r2) ∗ PolyMem (sp + 27856#64) (polyVecNat r3) ∗
      PolyMem (sp + 30448#64) (polyVecNat (uVecPoly06 rho coins 0)) ∗
      PolyMem (sp + 30960#64) (polyVecNat (uVecPoly06 rho coins 1)) ∗
      PolyMem (sp + 31472#64) (polyVecNat (uVecPoly06 rho coins 2)) ∗
      PolyMem (sp + 31984#64) (polyVecNat (uVecPoly06 rho coins 3)) ∗
      memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗
      (memRegion (sp + 2000#64) 368 ∗ ATransAt (sp + 4160#64) rho ∗
        memRegion (sp + 28368#64) 2048 ∗ Rest) := by
    refine Entails.trans hP1 ?_
    refine entails_sub (Entails.of_eq hm14) (by sep_frame) ?_
    refine entails_sub (Entails.of_eq hm2000) (by sep_frame) ?_
    exact entails_sub hmE1 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1 (seg7_c1_part hb hbase s1 sp fpVal (sp + 12352#64) _ _ _ _ r0 r1 r2 r3 _
      hpc1 hrun1 hsp1 hspA1 ⟨hfp1, hx19_1⟩ hcl1) ?_)
  rintro sf Pf hpc_f hrun_f hcl_f hro_f ⟨hsp_f, hspA_f, ⟨hfp_f, hx19_f⟩, hx20_f, _, hPf⟩
  refine SepWP.done hpc_f hrun_f ⟨hsp_f, hspA_f, hfp_f, hx19_f, hx20_f, hcl_f, hro_f, ?_⟩
  refine Entails.trans hPf ?_
  dsimp only [c1Bytes06]
  exact entails_sub (Entails.of_eq (split_2000_368 sp).symm) (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1
