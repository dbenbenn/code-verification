/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd

/-! # `generate_keypair_compressed` (`B05`) — Segment 5 `serialize_12` Helpers (`Seg5Ser`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteEncode fipsZetas mlkemQ nttStage polyAdd polyNtt samplePolyCbd2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 lane16 lane16_dup8x16 lane16_pack8x16 lane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and lane16_simdAdd8h simdAdd8h simdCmltZero8h simdExt16b
  simdSli2d simdSli4s simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  lane16_toUnsignedRep_cmlt toUnsignedRep16 toUnsignedRep16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  butterflyStage butterflyStage_getD butterflyStage_size foldl_range_stepK)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  byteEncode_eq_flatten_halves)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  neonSerialize12Bytes neonSerialize12Half neonSerialize12Half_eq
  neonSerialize12Mix neonSerialize12Mix_unmasked)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 polyVecNat step_ldpQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  step_stpQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  exec_simdAdd_8h_svc step_vreg1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd (
  exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDupScalar_h2 exec_simdExt_16b_8
  exec_simdSli_2d_24 exec_simdSli_4s_12 ext8_self_lane16_2 ext8_self_low32 low32_eq_lane64_0
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h)

/-! ## 1. Pure `serialize_12` Equivalence (`Poly16` → `Spec.byteEncode 12`) -/

@[expose] def toUnsignedVec8h (v : BitVec 128) : BitVec 128 :=
  simdAdd8h (simdCmltZero8h v &&& dup8x16 3329#16) v

theorem lane16_toUnsignedVec8h (v : BitVec 128) (j : Fin 8) :
    lane16 (toUnsignedVec8h v) j = toUnsignedRep16 (lane16 v j) := by
  rw [toUnsignedVec8h, lane16_simdAdd8h, lane16_and, lane16_dup8x16,
    BitVec.add_comm, lane16_toUnsignedRep_cmlt]

theorem polyBounded16_mono {B₁ B₂ : Int} {p : Poly16}
    (hle : B₁ ≤ B₂) (hbnd : PolyBounded16 B₁ p) : PolyBounded16 B₂ p :=
  ⟨hbnd.1, fun i hi => ⟨Int.le_trans (Int.neg_le_neg hle) (hbnd.2 i hi).1,
    Int.le_trans (hbnd.2 i hi).2 hle⟩⟩

theorem toUnsignedVec8h_lane_lt_4096 {p : Poly16} {v : Nat}
    (hbnd : PolyBounded16 3328 p) (hv : v < 32) (j : Fin 8) :
    (lane16 (toUnsignedVec8h (polyVecNat p v)) j).toNat < 4096 := by
  rw [lane16_toUnsignedVec8h, polyVecNat, lane16_pack8x16]
  have hb := hbnd.2 (8 * v + j.val) (by omega)
  have hlt := (toUnsignedRep16_spec (x := p.getD (8 * v + j.val) 0#16) (by omega) (by omega)).2.1
  omega

@[expose] def ser12Chunk24 (p : Poly16) (k : Nat) : List (BitVec 8) :=
  neonSerialize12Bytes
    (toUnsignedVec8h (polyVecNat p (2 * k)))
    (toUnsignedVec8h (polyVecNat p (2 * k + 1)))

@[expose] def ser12Prefix (p : Poly16) (m : Nat) : List (BitVec 8) :=
  ((List.range m).map (ser12Chunk24 p)).flatten

@[simp] theorem ser12Prefix_zero (p : Poly16) : ser12Prefix p 0 = [] := rfl

theorem ser12Prefix_succ (p : Poly16) (k : Nat) :
    ser12Prefix p (k + 1) = ser12Prefix p k ++ ser12Chunk24 p k := by
  simp [ser12Prefix, List.range_succ, List.flatten_append]

theorem ser12Chunk24_length (p : Poly16) (k : Nat) :
    (ser12Chunk24 p k).length = 24 := by
  simp [ser12Chunk24, neonSerialize12Bytes, neonSerialize12Half]

theorem ser12Prefix_length (p : Poly16) : ∀ m : Nat, (ser12Prefix p m).length = 24 * m
  | 0 => rfl
  | m + 1 => by rw [ser12Prefix_succ, List.length_append, ser12Prefix_length p m,
      ser12Chunk24_length]; omega

private theorem flatten_pairs_eq_range2 {α : Type} (g : Nat → List α) :
    ∀ m : Nat, ((List.range m).map fun k => g (2 * k) ++ g (2 * k + 1)).flatten =
      ((List.range (2 * m)).map g).flatten
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_pairs_eq_range2 g m,
      show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.range_succ, List.range_succ]
    simp [List.flatten_append, List.append_assoc]

theorem ser12Prefix_16_eq_byteEncode {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 3328 p) (hrep : PolyRepresents p f)
    (hcan : ∀ i, i < 256 → f.getD i 0 < 3329) :
    ser12Prefix p 16 = byteEncode 12 f := by
  unfold ser12Prefix ser12Chunk24 neonSerialize12Bytes
  rw [flatten_pairs_eq_range2 (fun v => neonSerialize12Half (toUnsignedVec8h (polyVecNat p v))),
    show 2 * 16 = 32 from rfl, byteEncode_eq_flatten_halves 12 (by decide) f]
  congr 1; apply List.map_congr_left; intro v hv
  have hv32 : v < 32 := List.mem_range.mp hv
  rw [neonSerialize12Half_eq]
  congr 1; funext j
  rw [lane16_toUnsignedVec8h, polyVecNat, lane16_pack8x16]
  have hidx : 8 * v + j.val < 256 := by omega
  have hb := hbnd.2 (8 * v + j.val) hidx
  have hr := hrep.2 (8 * v + j.val) hidx
  have hc := hcan (8 * v + j.val) hidx
  have hspec := (toUnsignedRep16_spec (x := p.getD (8 * v + j.val) 0#16) (by omega) (by omega)).1
  apply BitVec.eq_of_toNat_eq
  rw [hspec, hr, BitVec.toNat_ofNat]
  omega

theorem polyAdd_canonical (a b : Poly) : ∀ i, i < 256 → (polyAdd a b).getD i 0 < 3329 := by
  intro i hi
  rw [Array.getD_eq_getD_getElem?, polyAdd, Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem samplePolyCbd2_size (bs : List (BitVec 8)) : (samplePolyCbd2 bs).size = 256 := by
  simp [samplePolyCbd2]

private def nttPairFn (kInit blk fj fjl : Nat) : Nat × Nat :=
  let t := (fipsZetas.getD (kInit + blk) 0 * fjl) % mlkemQ
  ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ)

private theorem nttStage_eq_butterfly' (len kInit : Nat) (f : Poly) :
    nttStage len kInit f = (butterflyStage len (nttPairFn kInit) 0 f, kInit + 256 / (2 * len)) := by
  unfold nttStage butterflyStage nttPairFn
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let fj := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          let t := (fipsZetas.getD k 0 * fjl) % mlkemQ
          (arr.set! j ((fj + t) % mlkemQ)).set! (j + len) ((fj + mlkemQ - t) % mlkemQ))
        cur)
    (· + 1) (kInit + ·) kInit (Nat.add_zero kInit) (fun b => (Nat.add_assoc kInit b 1).symm) f

theorem polyNtt_canonical {f : Poly} (hf : f.size = 256) :
    ∀ i, i < 256 → (polyNtt f).getD i 0 < 3329 := by
  unfold polyNtt
  simp only [nttStage_eq_butterfly']
  have hs1 := butterflyStage_size (nttPairFn 1) 0 hf (len := 128) (by decide) (by decide)
  have hs2 := butterflyStage_size (nttPairFn 2) 0 hs1 (len := 64) (by decide) (by decide)
  have hs3 := butterflyStage_size (nttPairFn 4) 0 hs2 (len := 32) (by decide) (by decide)
  have hs4 := butterflyStage_size (nttPairFn 8) 0 hs3 (len := 16) (by decide) (by decide)
  have hs5 := butterflyStage_size (nttPairFn 16) 0 hs4 (len := 8) (by decide) (by decide)
  have hs6 := butterflyStage_size (nttPairFn 32) 0 hs5 (len := 4) (by decide) (by decide)
  intro i hi
  rw [butterflyStage_getD (nttPairFn 64) 0 hs6 (by decide) (by decide) hi]
  dsimp only [nttPairFn]
  split <;> exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem orr_12_eq_add_12 {sp : BitVec 64} (hspA : sp.toNat % 16 = 0)
    (off : Nat) (hoff : off % 16 = 0) :
    (sp + BitVec.ofNat 64 off) ||| 12#64 = sp + BitVec.ofNat 64 (off + 12) := by
  have hm16 : (sp + BitVec.ofNat 64 off).toNat % 16 = 0 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hand15 : (sp + BitVec.ofNat 64 off) &&& 15#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (sp + BitVec.ofNat 64 off).toNat &&& (2 ^ 4 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact hm16
  have hand : (sp + BitVec.ofNat 64 off) &&& 12#64 = 0#64 := by
    rw [show (12#64 : BitVec 64) = 15#64 &&& 12#64 from rfl, ← BitVec.and_assoc, hand15]; rfl
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  bv_omega

theorem orr_12_eq_add_12_spA {s : State} (hspA : s.spAligned = true)
    (off : Nat) (hoff : off % 16 = 0) :
    (s.sp + BitVec.ofNat 64 off) ||| 12#64 = s.sp + BitVec.ofNat 64 (off + 12) := by
  have h0 : (s.sp &&& 15#64) = 0#64 := by simpa [State.spAligned] using hspA
  have hmod : s.sp.toNat % 16 = 0 := by
    have ht := congrArg BitVec.toNat h0
    rw [BitVec.toNat_and, BitVec.toNat_ofNat] at ht
    change s.sp.toNat &&& (2 ^ 4 - 1) = 0 at ht
    rwa [Nat.and_two_pow_sub_one_eq_mod] at ht
  exact orr_12_eq_add_12 hmod off hoff

/-! ## 2. Parametric `serialize_12` Load, AdvSIMD, and Dead-Store Helpers -/

attribute [local irreducible] toUnsignedVec8h neonSerialize12Mix

theorem step_dead_stpQ_sp {prog : Program} {b target_pc : BitVec 64}
    {s : State} {m : Memory} {Rest : SepProp} {post : State → SepProp → Prop}
    (baseOff total pcOff nextOff spImm regOff : Nat) (vt1 vt2 : BitVec 5)
    (hrun : s.status = .Running) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.stpSimd .Q128 vt1 vt2 (.Offset .sp (BitVec.ofNat 64 spImm))))
    (hnextOff : pcOff + 4 = nextOff)
    (hreg : baseOff + regOff = spImm)
    (hbounds : regOff + 32 ≤ total)
    (htotal : total ≤ 2 ^ 64)
    (hcont : ∀ m' : Memory,
      SepWP prog target_pc
        ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        (memRegion (s.sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post) :
    SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (memRegion (s.sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post := by
  have hea : (s.sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 regOff =
      s.sp + BitVec.ofNat 64 spImm := by subst hreg; bv_omega
  have hpc_next : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine step_stpQ128_region (pc := b + BitVec.ofNat 64 pcOff)
    rfl hrun hfetch hspA rfl hbounds htotal hea fun m' => ?_
  rw [hpc_next]; exact hcont m'

theorem step_ldp_polyChunk {prog : Program} {target_pc src : BitVec 64}
    {s : State} {p : Poly16} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff k : Nat) (addr : AddrMode) (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.ldpSimd .Q128 1#5 2#5 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (src + BitVec.ofNat 64 (32 * k), none))
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 1#5 (polyVecNat p (2 * k))).writeVReg128 2#5
          (polyVecNat p (2 * k + 1))).setPC (b + BitVec.ofNat 64 nextOff))
      (PolyMem src (polyVecNat p) ∗ F) post) :
    SepWP prog target_pc s (PolyMem src (polyVecNat p) ∗ F) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_ldpQ128 hpc hrun hfetch hsp haddr rfl
    ((SepLoad128.vecRange (n := 32) (k := 2 * k) (by omega)
      (by clear * -; bv_omega)).left)
    ((SepLoad128.vecRange (n := 32) (k := 2 * k + 1) (by omega)
      (by clear * -; bv_omega)).left)
    (by simp [applyWriteback, hpc']) hnext

@[simp] private theorem sp_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).sp = s.sp := rfl
@[simp] private theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).pstate = s.pstate := rfl
@[simp] private theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) : (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp] private theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) : (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
private theorem csv1 (s : State) (w : BitVec 128) : calleeSavedVRegs (s.writeVReg128 1#5 w) = calleeSavedVRegs s := calleeSavedVRegs_writeVReg128 s 1#5 w
private theorem csv2 (s : State) (w : BitVec 128) : calleeSavedVRegs (s.writeVReg128 2#5 w) = calleeSavedVRegs s := calleeSavedVRegs_writeVReg128 s 2#5 w
private theorem csv3 (s : State) (w : BitVec 128) : calleeSavedVRegs (s.writeVReg128 3#5 w) = calleeSavedVRegs s := calleeSavedVRegs_writeVReg128 s 3#5 w
private theorem csv4 (s : State) (w : BitVec 128) : calleeSavedVRegs (s.writeVReg128 4#5 w) = calleeSavedVRegs s := calleeSavedVRegs_writeVReg128 s 4#5 w
private theorem csv5 (s : State) (w : BitVec 128) : calleeSavedVRegs (s.writeVReg128 5#5 w) = calleeSavedVRegs s := calleeSavedVRegs_writeVReg128 s 5#5 w

theorem step_ser12_simd18 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 k : Nat) (p : Poly16)
    (hbnd : PolyBounded16 3328 p) (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16)
    (hv1 : s.readVReg128 1#5 = polyVecNat p (2 * k))
    (hv2 : s.readVReg128 2#5 = polyVecNat p (2 * k + 1))
    (hf0  : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdTwoRegMisc true false 0b01#2 0b01010#5 1#5 3#5))
    (hf1  : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdTwoRegMisc true false 0b01#2 0b01010#5 2#5 4#5))
    (hf2  : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.simdThreeSame true false 0b00#2 0#5 0b00011#5 3#5 3#5))
    (hf3  : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdThreeSame true false 0b00#2 0#5 0b00011#5 4#5 4#5))
    (hf4  : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdThreeSame true false 0b01#2 1#5 0b10000#5 3#5 1#5))
    (hf5  : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.simdThreeSame true false 0b01#2 2#5 0b10000#5 4#5 2#5))
    (hf6  : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdPermute true 0b01#2 1#5 0b010#3 1#5 3#5))
    (hf7  : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.simdPermute true 0b01#2 1#5 0b110#3 1#5 1#5))
    (hf8  : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some (.simdPermute true 0b01#2 2#5 0b010#3 2#5 4#5))
    (hf9  : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.simdPermute true 0b01#2 2#5 0b110#3 2#5 2#5))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.simdImmShift true true 0b0101#4 0b100#3 0b01010#5 1#5 3#5))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.simdImmShift true true 0b0101#4 0b100#3 0b01010#5 2#5 4#5))
    (hf12 : prog.fetch (b + BitVec.ofNat 64 (p0 + 48)) = some (.simdPermute true 0b10#2 3#5 0b010#3 3#5 1#5))
    (hf13 : prog.fetch (b + BitVec.ofNat 64 (p0 + 52)) = some (.simdPermute true 0b10#2 3#5 0b110#3 3#5 2#5))
    (hf14 : prog.fetch (b + BitVec.ofNat 64 (p0 + 56)) = some (.simdPermute true 0b10#2 4#5 0b010#3 4#5 3#5))
    (hf15 : prog.fetch (b + BitVec.ofNat 64 (p0 + 60)) = some (.simdPermute true 0b10#2 4#5 0b110#3 4#5 4#5))
    (hf16 : prog.fetch (b + BitVec.ofNat 64 (p0 + 64)) = some (.simdImmShift true true 0b1011#4 0b000#3 0b01010#5 2#5 1#5))
    (hf17 : prog.fetch (b + BitVec.ofNat 64 (p0 + 68)) = some (.simdImmShift true true 0b1011#4 0b000#3 0b01010#5 4#5 3#5))
    (hnext : ∀ s' : State,
      s'.pc = b + BitVec.ofNat 64 (p0 + 72) →
      s'.status = .Running →
      s'.sp = s.sp →
      (∀ r : Reg, s'.readReg64 r = s.readReg64 r) →
      s'.pstate = s.pstate →
      s'.readVReg128 0#5 = s.readVReg128 0#5 →
      s'.readVReg128 1#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k))) →
      s'.readVReg128 3#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1))) →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  let r0 := polyVecNat p (2 * k)
  let r1 := polyVecNat p (2 * k + 1)
  let d0 := toUnsignedVec8h r0
  let d1 := toUnsignedVec8h r1
  let mix0 := simdSli4s (simdTrn1_8h d0 d0) (simdTrn2_8h d0 d0) 12
  let mix1 := simdSli4s (simdTrn1_8h d1 d1) (simdTrn2_8h d1 d1) 12
  have hd0_eq : simdAdd8h (simdCmltZero8h r0 &&& dup8x16 3329#16) r0 = d0 := by
    dsimp only [d0]; unfold toUnsignedVec8h; rfl
  have hd1_eq : simdAdd8h (simdCmltZero8h r1 &&& dup8x16 3329#16) r1 = d1 := by
    dsimp only [d1]; unfold toUnsignedVec8h; rfl
  have hunm0 : simdSli2d (simdTrn1_4s mix0 mix0) (simdTrn2_4s mix0 mix0) 24 = neonSerialize12Mix d0 :=
    neonSerialize12Mix_unmasked d0 (toUnsignedVec8h_lane_lt_4096 hbnd (by omega))
  have hunm1 : simdSli2d (simdTrn1_4s mix1 mix1) (simdTrn2_4s mix1 mix1) 24 = neonSerialize12Mix d1 :=
    neonSerialize12Mix_unmasked d1 (toUnsignedVec8h_lane_lt_4096 hbnd (by omega))
  refine step_vreg1 b p0 (p0 + 4) 3#5 (simdCmltZero8h r0) hpc hrun hf0
    (by rw [exec_simdCmltZero_8h]; simp [hv1, r0]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 4#5 (simdCmltZero8h r1) rfl (by simp [hrun]) hf1
    (by rw [exec_simdCmltZero_8h]; simp [hv2, r1]) (by omega) ?_
  refine step_vreg1 b (p0 + 8) (p0 + 12) 3#5 (simdCmltZero8h r0 &&& dup8x16 3329#16) rfl (by simp [hrun]) hf2
    (by rw [exec_simdAnd_16b]; simp [hv0]) (by omega) ?_
  refine step_vreg1 b (p0 + 12) (p0 + 16) 4#5 (simdCmltZero8h r1 &&& dup8x16 3329#16) rfl (by simp [hrun]) hf3
    (by rw [exec_simdAnd_16b]; simp [hv0]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 1#5 d0 rfl (by simp [hrun]) hf4
    (by rw [exec_simdAdd_8h_svc]; simp [hv1, r0, hd0_eq]) (by omega) ?_
  refine step_vreg1 b (p0 + 20) (p0 + 24) 2#5 d1 rfl (by simp [hrun]) hf5
    (by rw [exec_simdAdd_8h_svc]; simp [hv2, r1, hd1_eq]) (by omega) ?_
  refine step_vreg1 b (p0 + 24) (p0 + 28) 3#5 (simdTrn1_8h d0 d0) rfl (by simp [hrun]) hf6
    (by rw [svc_simdTrn1_8h]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 28) (p0 + 32) 1#5 (simdTrn2_8h d0 d0) rfl (by simp [hrun]) hf7
    (by rw [svc_simdTrn2_8h]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 32) (p0 + 36) 4#5 (simdTrn1_8h d1 d1) rfl (by simp [hrun]) hf8
    (by rw [svc_simdTrn1_8h]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 36) (p0 + 40) 2#5 (simdTrn2_8h d1 d1) rfl (by simp [hrun]) hf9
    (by rw [svc_simdTrn2_8h]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 40) (p0 + 44) 3#5 mix0 rfl (by simp [hrun]) hf10
    (by rw [exec_simdSli_4s_12]; simp [mix0]) (by omega) ?_
  refine step_vreg1 b (p0 + 44) (p0 + 48) 4#5 mix1 rfl (by simp [hrun]) hf11
    (by rw [exec_simdSli_4s_12]; simp [mix1]) (by omega) ?_
  refine step_vreg1 b (p0 + 48) (p0 + 52) 1#5 (simdTrn1_4s mix0 mix0) rfl (by simp [hrun]) hf12
    (by rw [svc_simdTrn1_4s]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 52) (p0 + 56) 2#5 (simdTrn2_4s mix0 mix0) rfl (by simp [hrun]) hf13
    (by rw [svc_simdTrn2_4s]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 56) (p0 + 60) 3#5 (simdTrn1_4s mix1 mix1) rfl (by simp [hrun]) hf14
    (by rw [svc_simdTrn1_4s]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 60) (p0 + 64) 4#5 (simdTrn2_4s mix1 mix1) rfl (by simp [hrun]) hf15
    (by rw [svc_simdTrn2_4s]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 64) (p0 + 68) 1#5 (neonSerialize12Mix d0) rfl (by simp [hrun]) hf16
    (by rw [exec_simdSli_2d_24]; simp [hunm0]) (by omega) ?_
  refine step_vreg1 b (p0 + 68) (p0 + 72) 3#5 (neonSerialize12Mix d1) rfl (by simp [hrun]) hf17
    (by rw [exec_simdSli_2d_24]; simp [hunm1]) (by omega) ?_
  refine hnext _ rfl (by simp [hrun]) (by simp) (fun r => by simp) (by simp) (by simp)
    (by simp [d0, r0]) (by simp [d1, r1])
    (by simp only [calleeSavedVRegs_setPC, csv1, csv2, csv3, csv4])

/-! ## 3. Three `serialize_12` Store-Tail Shapes (`pos`, `neg12`, `off384`) -/

private theorem sepWP_elim_cell4 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 32, SepWP prog target s ((a ↦₃₂ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 4 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm; exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_cell2 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 16, SepWP prog target s ((a ↦₁₆ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 2 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_two, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm; exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_region6 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w : BitVec 32) (u : BitVec 16),
      SepWP prog target s ((a ↦₃₂ w) ∗ ((a + 4#64) ↦₁₆ u) ∗ R0) post) :
    SepWP prog target s (memRegion a 6 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 4#64) (n := 4) (k := (2 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_cell4; intro w
  refine SepWP.weaken_pre (show (a ↦₃₂ w) ∗ (memRegion (a + 4#64) 2 ∗ R0) ⊢
      memRegion (a + 4#64) 2 ∗ ((a ↦₃₂ w) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_cell2; intro u
  exact SepWP.weaken_pre (by sep_frame) (h w u)

private theorem sepWP_elim_region12 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 16) (w2 : BitVec 32) (u3 : BitVec 16),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ ((a + 6#64) ↦₃₂ w2) ∗ ((a + 10#64) ↦₁₆ u3) ∗ R0) post) :
    SepWP prog target s (memRegion a 12 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 6#64) (n := 6) (k := (6 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_region6; intro w0 u1
  refine SepWP.weaken_pre (show (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ (memRegion (a + 6#64) 6 ∗ R0) ⊢
      memRegion (a + 6#64) 6 ∗ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_region6; intro w2 u3
  refine SepWP.weaken_pre ?_ (h w0 u1 w2 u3)
  rw [show a + 6#64 + 4#64 = a + 10#64 by bv_omega]; sep_frame

private theorem sepWP_elim_region24 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 16) (w2 : BitVec 32) (u3 : BitVec 16)
        (w4 : BitVec 32) (u5 : BitVec 16) (w6 : BitVec 32) (u7 : BitVec 16),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ ((a + 6#64) ↦₃₂ w2) ∗ ((a + 10#64) ↦₁₆ u3) ∗
         ((a + 12#64) ↦₃₂ w4) ∗ ((a + 16#64) ↦₁₆ u5) ∗ ((a + 18#64) ↦₃₂ w6) ∗
         ((a + 22#64) ↦₁₆ u7) ∗ R0) post) :
    SepWP prog target s (memRegion a 24 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 12#64) (n := 12) (k := (12 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_region12; intro w0 u1 w2 u3
  refine SepWP.weaken_pre (show (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ ((a + 6#64) ↦₃₂ w2) ∗
        ((a + 10#64) ↦₁₆ u3) ∗ (memRegion (a + 12#64) 12 ∗ R0) ⊢
      memRegion (a + 12#64) 12 ∗ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ u1) ∗ ((a + 6#64) ↦₃₂ w2) ∗
        ((a + 10#64) ↦₁₆ u3) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_region12; intro w4 u5 w6 u7
  refine SepWP.weaken_pre ?_ (h w0 u1 w2 u3 w4 u5 w6 u7)
  rw [show a + 12#64 + 4#64 = a + 16#64 by bv_omega,
      show a + 12#64 + 6#64 = a + 18#64 by bv_omega,
      show a + 12#64 + 10#64 = a + 22#64 by bv_omega]; sep_frame

private theorem cells12_eq_neonSerialize12Half (a : BitVec 64) (v : BitVec 128) :
    let m := neonSerialize12Mix v
    let mHi := simdExt16b m m 8
    (a ↦₃₂ (lane64 m 0).truncate 32) ∗ ((a + 4#64) ↦₁₆ lane16 m 2) ∗
    ((a + 6#64) ↦₃₂ (lane64 mHi 0).truncate 32) ∗ ((a + 10#64) ↦₁₆ lane16 mHi 2) =
    (a ↦ₛ neonSerialize12Half v) := by
  dsimp only [neonSerialize12Half]
  simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack16_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo16_eq_pointsToBytes,
    show a + 4#64 + 2#64 = a + 6#64 by bv_omega,
    show a + 6#64 + 4#64 = a + 10#64 by bv_omega]

private theorem cells24_eq_ser12Chunk24 (a : BitVec 64) (p : Poly16) (k : Nat) :
    let m0 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k)))
    let m1 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1)))
    (a ↦₃₂ (lane64 m0 0).truncate 32) ∗ ((a + 4#64) ↦₁₆ lane16 m0 2) ∗
    ((a + 6#64) ↦₃₂ (lane64 (simdExt16b m0 m0 8) 0).truncate 32) ∗
    ((a + 10#64) ↦₁₆ lane16 (simdExt16b m0 m0 8) 2) ∗
    ((a + 12#64) ↦₃₂ (lane64 m1 0).truncate 32) ∗ ((a + 16#64) ↦₁₆ lane16 m1 2) ∗
    ((a + 18#64) ↦₃₂ (lane64 (simdExt16b m1 m1 8) 0).truncate 32) ∗
    ((a + 22#64) ↦₁₆ lane16 (simdExt16b m1 m1 8) 2) =
    (a ↦ₛ ser12Chunk24 p k) := by
  dsimp only
  have hc0 := cells12_eq_neonSerialize12Half a (toUnsignedVec8h (polyVecNat p (2 * k)))
  have hc1 := cells12_eq_neonSerialize12Half (a + 12#64) (toUnsignedVec8h (polyVecNat p (2 * k + 1)))
  dsimp only at hc0 hc1
  rw [ser12Chunk24, neonSerialize12Bytes, pointsToBytes_append,
    show (neonSerialize12Half (toUnsignedVec8h (polyVecNat p (2 * k)))).length = 12 by
      simp [neonSerialize12Half], ← hc0, ← hc1]
  simp only [sepConj_assoc, show a + 12#64 + 4#64 = a + 16#64 by bv_omega,
    show a + 12#64 + 6#64 = a + 18#64 by bv_omega, show a + 12#64 + 10#64 = a + 22#64 by bv_omega]

@[simp] private theorem setWidth16_zext128 (x : BitVec 16) : (x.zeroExtend 128).setWidth 16 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]

private theorem ser12Prefix_append_chunk (dst : BitVec 64) (p : Poly16) (k : Nat) :
    (dst ↦ₛ ser12Prefix p k) ∗
      ((dst + BitVec.ofNat 64 (24 * k)) ↦ₛ ser12Chunk24 p k) =
      (dst ↦ₛ ser12Prefix p (k + 1)) := by
  rw [ser12Prefix_succ, pointsToBytes_append, ser12Prefix_length]

private theorem step_strS32_addr {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b addrEA : BitVec 64) (pcOff nextOff : Nat) (vt : BitVec 5) (addr : AddrMode) (v : BitVec 32)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.strSimd .S32 vt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (addrEA, none))
    (hv : (s.readVReg128 vt).extractLsb' 0 32 = v)
    (hstore : SepStore32 addrEA v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_strSimd32 (wb := none) hpc hrun hfetch hsp haddr hv hstore
    (by simp [applyWriteback, hpc']) hnext

private theorem step_strH16_addr {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b addrEA : BitVec 64) (pcOff nextOff : Nat) (vt : BitVec 5) (addr : AddrMode) (v : BitVec 16)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.strSimd .H16 vt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (addrEA, none))
    (hv : (s.readVReg128 vt).truncate 16 = v)
    (hstore : SepStore16 addrEA v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strSimd16 (wb := none) hpc hrun hfetch hsp haddr hv hstore
    (by simp [applyWriteback, hpc']) hnext

private theorem checkAddr_of_nonSp (s : State) {a : AddrMode} (h : a.baseReg ≠ .sp) :
    checkAddrSPAligned s a = true := by
  unfold checkAddrSPAligned checkRegSPAligned
  cases hb : a.baseReg <;> simp_all

theorem step_ser12_tail14 {prog : Program} {target_pc dst : BitVec 64}
    {s : State} {p : Poly16} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 k : Nat) (a0 a12 a6 a4 a16 a18 a10 a22 : AddrMode) (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hv1 : s.readVReg128 1#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k))))
    (hv3 : s.readVReg128 3#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1))))
    (hf0  : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdExt true 1#5 8#4 1#5 2#5))
    (hf1  : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdDupScalar 0b01010#5 1#5 4#5))
    (hf2  : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.strSimd .S32 1#5 a0))
    (hf3  : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdExt true 3#5 8#4 3#5 5#5))
    (hf4  : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdDupScalar 0b01010#5 3#5 1#5))
    (hf5  : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.strSimd .S32 3#5 a12))
    (hf6  : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdDupScalar 0b01010#5 2#5 3#5))
    (hf7  : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.strSimd .S32 2#5 a6))
    (hf8  : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some (.simdDupScalar 0b01010#5 5#5 2#5))
    (hf9  : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.strSimd .H16 4#5 a4))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.strSimd .H16 1#5 a16))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.strSimd .S32 5#5 a18))
    (hf12 : prog.fetch (b + BitVec.ofNat 64 (p0 + 48)) = some (.strSimd .H16 3#5 a10))
    (hf13 : prog.fetch (b + BitVec.ofNat 64 (p0 + 52)) = some (.strSimd .H16 2#5 a22))
    (hb0 : a0.baseReg ≠ .sp) (hb12 : a12.baseReg ≠ .sp) (hb6 : a6.baseReg ≠ .sp) (hb4 : a4.baseReg ≠ .sp)
    (hb16 : a16.baseReg ≠ .sp) (hb18 : a18.baseReg ≠ .sp) (hb10 : a10.baseReg ≠ .sp) (hb22 : a22.baseReg ≠ .sp)
    (he0  : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a0 = (dst + BitVec.ofNat 64 (24 * k), none))
    (he12 : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a12 = (dst + BitVec.ofNat 64 (24 * k) + 12#64, none))
    (he6  : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a6 = (dst + BitVec.ofNat 64 (24 * k) + 6#64, none))
    (he4  : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a4 = (dst + BitVec.ofNat 64 (24 * k) + 4#64, none))
    (he16 : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a16 = (dst + BitVec.ofNat 64 (24 * k) + 16#64, none))
    (he18 : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a18 = (dst + BitVec.ofNat 64 (24 * k) + 18#64, none))
    (he10 : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a10 = (dst + BitVec.ofNat 64 (24 * k) + 10#64, none))
    (he22 : ∀ s' : State, (∀ r, s'.readReg64 r = s.readReg64 r) → evalAddrMode s' a22 = (dst + BitVec.ofNat 64 (24 * k) + 22#64, none))
    (hnext : ∀ s' : State,
      s'.pc = b + BitVec.ofNat 64 (p0 + 56) →
      s'.status = .Running →
      s'.sp = s.sp →
      (∀ r : Reg, s'.readReg64 r = s.readReg64 r) →
      s'.pstate = s.pstate →
      s'.readVReg128 0#5 = s.readVReg128 0#5 →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP prog target_pc s'
        ((dst ↦ₛ ser12Prefix p (k + 1)) ∗
          memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) post) :
    SepWP prog target_pc s
      ((dst ↦ₛ ser12Prefix p k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F) post := by
  let ea := dst + BitVec.ofNat 64 (24 * k)
  let m0 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k)))
  let m1 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1)))
  let e0 := m0.truncate 64 ++ m0.extractLsb' 64 64
  let e1 := m1.truncate 64 ++ m1.extractLsb' 64 64
  have hsplit : memRegion ea (384 - 24 * k) =
      memRegion ea 24 ∗ memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) := by
    have hm := memRegion_split ea 24 (384 - 24 * (k + 1)) (by omega)
    have ha : ea + BitVec.ofNat 64 24 = dst + BitVec.ofNat 64 (24 * (k + 1)) := by
      dsimp only [ea]; clear * -; bv_omega
    rw [show 24 + (384 - 24 * (k + 1)) = 384 - 24 * k by omega, ha] at hm
    exact hm
  refine SepWP.weaken_pre
    (show (dst ↦ₛ ser12Prefix p k) ∗ memRegion ea (384 - 24 * k) ∗ F ⊢
      memRegion ea 24 ∗ ((dst ↦ₛ ser12Prefix p k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region24; intro w0 u1 w2 u3 w4 u5 w6 u7
  refine step_vreg1 b p0 (p0 + 4) 2#5 e0 hpc hrun hf0
    (by rw [exec_simdExt_16b_8]; simp [hv1, e0, m0]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 4#5 ((lane16 m0 2).zeroExtend 128) rfl (by simp [hrun]) hf1
    (by rw [exec_simdDupScalar_h2]; simp [hv1, m0]) (by omega) ?_
  refine step_strS32_addr b ea (p0 + 8) (p0 + 12) 1#5 a0 ((lane64 m0 0).truncate 32)
    rfl (by simp [hrun]) hf2 (checkAddr_of_nonSp _ hb0) (he0 _ fun r => by simp)
    (by simp [hv1, m0, low32_eq_lane64_0])
    (SepStore32.left (SepStore32.here rfl)) (by omega) ?_; intro mem1
  refine step_vreg1 b (p0 + 12) (p0 + 16) 5#5 e1 rfl (by simp [hrun]) hf3
    (by rw [exec_simdExt_16b_8]; simp [hv3, e1, m1]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 1#5 ((lane16 m1 2).zeroExtend 128) rfl (by simp [hrun]) hf4
    (by rw [exec_simdDupScalar_h2]; simp [hv3, m1]) (by omega) ?_
  refine step_strS32_addr b (ea + 12#64) (p0 + 20) (p0 + 24) 3#5 a12 ((lane64 m1 0).truncate 32)
    rfl (by simp [hrun]) hf5 (checkAddr_of_nonSp _ hb12) (he12 _ fun r => by simp)
    (by simp [hv3, m1, low32_eq_lane64_0])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))
    (by omega) ?_; intro mem2
  refine step_vreg1 b (p0 + 24) (p0 + 28) 3#5 ((lane16 (simdExt16b m0 m0 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf6 (by rw [exec_simdDupScalar_h2]; simp [e0, ext8_self_lane16_2]) (by omega) ?_
  refine step_strS32_addr b (ea + 6#64) (p0 + 28) (p0 + 32) 2#5 a6 ((lane64 (simdExt16b m0 m0 8) 0).truncate 32)
    rfl (by simp [hrun]) hf7 (checkAddr_of_nonSp _ hb6) (he6 _ fun r => by simp)
    (by simp [e0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl)))) (by omega) ?_; intro mem3
  refine step_vreg1 b (p0 + 32) (p0 + 36) 2#5 ((lane16 (simdExt16b m1 m1 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf8 (by rw [exec_simdDupScalar_h2]; simp [e1, ext8_self_lane16_2]) (by omega) ?_
  refine step_strH16_addr b (ea + 4#64) (p0 + 36) (p0 + 40) 4#5 a4 (lane16 m0 2)
    rfl (by simp [hrun]) hf9 (checkAddr_of_nonSp _ hb4) (he4 _ fun r => by simp) (by simp)
    (SepStore16.right (SepStore16.left (SepStore16.here rfl))) (by omega) ?_; intro mem4
  refine step_strH16_addr b (ea + 16#64) (p0 + 40) (p0 + 44) 1#5 a16 (lane16 m1 2)
    rfl (by simp [hrun]) hf10 (checkAddr_of_nonSp _ hb16) (he16 _ fun r => by simp) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))
    (by omega) ?_; intro mem5
  refine step_strS32_addr b (ea + 18#64) (p0 + 44) (p0 + 48) 5#5 a18 ((lane64 (simdExt16b m1 m1 8) 0).truncate 32)
    rfl (by simp [hrun]) hf11 (checkAddr_of_nonSp _ hb18) (he18 _ fun r => by simp) (by simp [e1, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))))
    (by omega) ?_; intro mem6
  refine step_strH16_addr b (ea + 10#64) (p0 + 48) (p0 + 52) 3#5 a10 (lane16 (simdExt16b m0 m0 8) 2)
    rfl (by simp [hrun]) hf12 (checkAddr_of_nonSp _ hb10) (he10 _ fun r => by simp) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))
    (by omega) ?_; intro mem7
  refine step_strH16_addr b (ea + 22#64) (p0 + 52) (p0 + 56) 2#5 a22 (lane16 (simdExt16b m1 m1 8) 2)
    rfl (by simp [hrun]) hf13 (checkAddr_of_nonSp _ hb22) (he22 _ fun r => by simp) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))))
    (by omega) ?_; intro mem8
  refine SepWP.weaken_pre (P' := (dst ↦ₛ ser12Prefix p (k + 1)) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) ?_ ?_
  · have hc := cells24_eq_ser12Chunk24 ea p k
    have hp := ser12Prefix_append_chunk dst p k
    dsimp only [m0, m1] at hc ⊢; rw [← hp, ← hc]; sep_frame
  · refine hnext _ (by simp) (by simp [hrun]) (by simp) (fun r => by simp) (by simp) (by simp) ?_
    simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, csv1, csv2, csv3, csv4, csv5]

private theorem step_reg1 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rd : Reg) (val : BitVec 64) {inst : Instr}
    (hrd : rd ≠ .sp) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some inst)
    (hexec : execInstWithSvc (evalSvc prog.svc) inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).writeReg64 rd val).advancePC)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeReg64 rd val).setPC (b + BitVec.ofNat 64 nextOff)) P post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hev : prog.evalInst inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      (s.writeReg64 rd val).setPC (b + BitVec.ofNat 64 nextOff) := by
    unfold Program.evalInst; rw [hexec]
    cases rd <;> cases s <;> simp_all [State.setPC, State.writeReg64, State.advancePC]
  exact SepWP.step_pure hpc hrun hfetch hev (by cases rd <;> simp_all [State.writeReg64]) hnext

theorem step_ser12_tail15_off384 {prog : Program} {target_pc dst : BitVec 64}
    {s : State} {p : Poly16} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 k : Nat) {instAdd : Instr} (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 + 384#64 = dst + BitVec.ofNat 64 (24 * k))
    (hx11 : s.readReg64 .x11 = dst + BitVec.ofNat 64 (24 * k) + 6#64)
    (hv1 : s.readVReg128 1#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k))))
    (hv3 : s.readVReg128 3#5 = neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1))))
    (hf0  : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdExt true 1#5 8#4 1#5 2#5))
    (hf1  : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdDupScalar 0b01010#5 1#5 4#5))
    (hf2  : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.strSimd .S32 1#5 (.Offset .x10 384#64)))
    (hf3  : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdExt true 3#5 8#4 3#5 5#5))
    (hf4  : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdDupScalar 0b01010#5 3#5 1#5))
    (hf5  : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.strSimd .S32 3#5 (.Offset .x10 396#64)))
    (hf6  : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdDupScalar 0b01010#5 2#5 3#5))
    (hf7  : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.strSimd .S32 2#5 (.Offset .x11 0#64)))
    (hf8  : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some instAdd)
    (hadd : ∀ (svc : State → State) (st : State),
      execInstWithSvc svc instAdd st = (st.writeReg64 .x11 (st.readReg64 .x10 + 402#64)).advancePC)
    (hf9  : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.simdDupScalar 0b01010#5 5#5 2#5))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.strSimd .H16 4#5 (.Offset .x10 388#64)))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.strSimd .H16 1#5 (.Offset .x10 400#64)))
    (hf12 : prog.fetch (b + BitVec.ofNat 64 (p0 + 48)) = some (.strSimd .S32 5#5 (.Offset .x11 0#64)))
    (hf13 : prog.fetch (b + BitVec.ofNat 64 (p0 + 52)) = some (.strSimd .H16 3#5 (.Offset .x10 394#64)))
    (hf14 : prog.fetch (b + BitVec.ofNat 64 (p0 + 56)) = some (.strSimd .H16 2#5 (.Offset .x10 406#64)))
    (hnext : ∀ s' : State,
      s'.pc = b + BitVec.ofNat 64 (p0 + 60) →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.spAligned = s.spAligned →
      (∀ r : Reg, r ≠ .x11 → s'.readReg64 r = s.readReg64 r) →
      s'.pstate = s.pstate →
      s'.readVReg128 0#5 = s.readVReg128 0#5 →
      SepWP prog target_pc s'
        ((dst ↦ₛ ser12Prefix p (k + 1)) ∗
          memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) post) :
    SepWP prog target_pc s
      ((dst ↦ₛ ser12Prefix p k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F) post := by
  let ea := dst + BitVec.ofNat 64 (24 * k)
  let m0 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k)))
  let m1 := neonSerialize12Mix (toUnsignedVec8h (polyVecNat p (2 * k + 1)))
  let e0 := m0.truncate 64 ++ m0.extractLsb' 64 64
  let e1 := m1.truncate 64 ++ m1.extractLsb' 64 64
  have hsplit : memRegion ea (384 - 24 * k) =
      memRegion ea 24 ∗ memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) := by
    have hm := memRegion_split ea 24 (384 - 24 * (k + 1)) (by omega)
    have ha : ea + BitVec.ofNat 64 24 = dst + BitVec.ofNat 64 (24 * (k + 1)) := by
      dsimp only [ea]; clear * -; bv_omega
    rw [show 24 + (384 - 24 * (k + 1)) = 384 - 24 * k by omega, ha] at hm
    exact hm
  refine SepWP.weaken_pre
    (show (dst ↦ₛ ser12Prefix p k) ∗ memRegion ea (384 - 24 * k) ∗ F ⊢
      memRegion ea 24 ∗ ((dst ↦ₛ ser12Prefix p k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region24; intro w0 u1 w2 u3 w4 u5 w6 u7
  refine step_vreg1 b p0 (p0 + 4) 2#5 e0 hpc hrun hf0
    (by rw [exec_simdExt_16b_8]; simp [hv1, e0, m0]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 4#5 ((lane16 m0 2).zeroExtend 128) rfl (by simp [hrun]) hf1
    (by rw [exec_simdDupScalar_h2]; simp [hv1, m0]) (by omega) ?_
  refine step_strS32_addr b ea (p0 + 8) (p0 + 12) 1#5 (.Offset .x10 384#64) ((lane64 m0 0).truncate 32)
    rfl (by simp [hrun]) hf2 (checkAddr_of_nonSp _ (by decide)) (by simp [evalAddrMode, hx10, ea])
    (by simp [hv1, m0, low32_eq_lane64_0])
    (SepStore32.left (SepStore32.here rfl)) (by omega) ?_; intro mem1
  refine step_vreg1 b (p0 + 12) (p0 + 16) 5#5 e1 rfl (by simp [hrun]) hf3
    (by rw [exec_simdExt_16b_8]; simp [hv3, e1, m1]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 1#5 ((lane16 m1 2).zeroExtend 128) rfl (by simp [hrun]) hf4
    (by rw [exec_simdDupScalar_h2]; simp [hv3, m1]) (by omega) ?_
  refine step_strS32_addr b (ea + 12#64) (p0 + 20) (p0 + 24) 3#5 (.Offset .x10 396#64) ((lane64 m1 0).truncate 32)
    rfl (by simp [hrun]) hf5 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega)
    (by simp [hv3, m1, low32_eq_lane64_0])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))
    (by omega) ?_; intro mem2
  refine step_vreg1 b (p0 + 24) (p0 + 28) 3#5 ((lane16 (simdExt16b m0 m0 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf6 (by rw [exec_simdDupScalar_h2]; simp [e0, ext8_self_lane16_2]) (by omega) ?_
  refine step_strS32_addr b (ea + 6#64) (p0 + 28) (p0 + 32) 2#5 (.Offset .x11 0#64) ((lane64 (simdExt16b m0 m0 8) 0).truncate 32)
    rfl (by simp [hrun]) hf7 (checkAddr_of_nonSp _ (by decide)) (by simp [evalAddrMode, hx11, ea])
    (by simp [e0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl)))) (by omega) ?_; intro mem3
  refine step_reg1 b (p0 + 32) (p0 + 36) .x11 (s.readReg64 .x10 + 402#64)
    (by decide) rfl (by simp [hrun]) hf8 (by rw [hadd]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 36) (p0 + 40) 2#5 ((lane16 (simdExt16b m1 m1 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf9 (by rw [exec_simdDupScalar_h2]; simp [e1, ext8_self_lane16_2]) (by omega) ?_
  refine step_strH16_addr b (ea + 4#64) (p0 + 40) (p0 + 44) 4#5 (.Offset .x10 388#64) (lane16 m0 2)
    rfl (by simp [hrun]) hf10 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega) (by simp)
    (SepStore16.right (SepStore16.left (SepStore16.here rfl))) (by omega) ?_; intro mem4
  refine step_strH16_addr b (ea + 16#64) (p0 + 44) (p0 + 48) 1#5 (.Offset .x10 400#64) (lane16 m1 2)
    rfl (by simp [hrun]) hf11 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))
    (by omega) ?_; intro mem5
  refine step_strS32_addr b (ea + 18#64) (p0 + 48) (p0 + 52) 5#5 (.Offset .x11 0#64) ((lane64 (simdExt16b m1 m1 8) 0).truncate 32)
    rfl (by simp [hrun]) hf12 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega) (by simp [e1, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))))
    (by omega) ?_; intro mem6
  refine step_strH16_addr b (ea + 10#64) (p0 + 52) (p0 + 56) 3#5 (.Offset .x10 394#64) (lane16 (simdExt16b m0 m0 8) 2)
    rfl (by simp [hrun]) hf13 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))
    (by omega) ?_; intro mem7
  refine step_strH16_addr b (ea + 22#64) (p0 + 56) (p0 + 60) 2#5 (.Offset .x10 406#64) (lane16 (simdExt16b m1 m1 8) 2)
    rfl (by simp [hrun]) hf14 (checkAddr_of_nonSp _ (by decide))
    (by simp [evalAddrMode]; dsimp only [ea]; rw [← hx10]; clear * -; bv_omega) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))))
    (by omega) ?_; intro mem8
  refine SepWP.weaken_pre (P' := (dst ↦ₛ ser12Prefix p (k + 1)) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) ?_ ?_
  · have hc := cells24_eq_ser12Chunk24 ea p k
    have hp := ser12Prefix_append_chunk dst p k
    dsimp only [m0, m1] at hc ⊢; rw [← hp, ← hc]; sep_frame
  · refine hnext _ (by simp) (by simp [hrun]) (by simp) (by simp [State.spAligned]) (fun r hr => by simp [hr]) (by simp) (by simp)

theorem step_dead_stpQ_reg {prog : Program} {b target_pc base : BitVec 64}
    {s : State} {m : Memory} {Rest : SepProp} {post : State → SepProp → Prop}
    (rn : Reg) (total pcOff nextOff off : Nat) (vt1 vt2 : BitVec 5)
    (hrn_sp : rn ≠ .sp) (hrun : s.status = .Running) (hrn : s.readReg64 rn = base)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.stpSimd .Q128 vt1 vt2 (.Offset rn (BitVec.ofNat 64 off))))
    (hnextOff : pcOff + 4 = nextOff)
    (hbounds : off + 32 ≤ total) (htotal : total ≤ 2 ^ 64)
    (hcont : ∀ m' : Memory,
      SepWP prog target_pc
        ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        (memRegion base total ∗ Rest) post) :
    SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (memRegion base total ∗ Rest) post := by
  have haddr : evalAddrMode ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (.Offset rn (BitVec.ofNat 64 off)) = (base + BitVec.ofNat 64 off, none) := by
    simp [evalAddrMode, hrn]
  have hpc_next : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine step_stpQ128_region (pc := b + BitVec.ofNat 64 pcOff) rfl hrun hfetch
    (checkAddr_of_nonSp _ hrn_sp) haddr hbounds htotal rfl fun m' => ?_
  rw [hpc_next]; exact hcont m'

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser
