/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import

/-!
# `validate_pk_bytes` (`B21`) — Segment 2 Helpers & Interface (`+0x00b0 .. +0x044c`)

Pure deserialized vector/polynomial representations (`deserVec8h`, `deserChunk32`,
`reducedPolyBytes`), `Seg3Pre`/`Seg3Spatial` interface, `.rodata` Q-load and `O(1)` dead-store
`memRegion` step lemmas, and AdvSIMD `execInstWithSvc` bridges for `deserialize_12`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  cst16Vec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  sha3_256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16
  fin8_cases
  lane16
  lane16_pack8x16
  lane16_zipSimdLanes_true_16
  lane8
  pack16x8
  pack8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_and
  lane16_simdAdd8h
  lane16_simdCmhs8h
  lane16_simdUshl8h
  simdAdd8h
  simdCmhs8h
  simdTbl16b
  simdUshl8h
  simdUshlElem16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  rawCoeff0
  rawCoeff0_lt_4096
  rawCoeff1
  rawCoeff1_lt_4096
  reduce12
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  SavedFrame
  UnspilledSaved
  cells16_entails_memRegion
  cells32_entails_memRegion
  entails_sub
  sepWP_elim_region16
  sepWP_elim_region32
)

/-! ## 1. Deserialized Vector / Polynomial Representation & `Seg3` Interface -/

/-- One 128-bit (`8 × u16`) output vector of NEON `deserialize_12` on the 12 bytes of `bs`
    starting at `off` (`4` 3-byte triples → `8` coefficients reduced into `[0, 3329)`). -/
@[expose] def deserVec8h (bs : List (BitVec 8)) (off : Nat) : BitVec 128 :=
  pack8x16 fun i =>
    let t := i.val / 2
    if i.val % 2 == 0 then
      reduce12 (rawCoeff0 (bs.getD (off + 3 * t) 0#8) (bs.getD (off + 3 * t + 1) 0#8))
    else
      reduce12 (rawCoeff1 (bs.getD (off + 3 * t + 1) 0#8) (bs.getD (off + 3 * t + 2) 0#8))

@[simp] theorem lane16_deserVec8h (bs : List (BitVec 8)) (off : Nat) (i : Fin 8) :
    lane16 (deserVec8h bs off) i =
      let t := i.val / 2
      if i.val % 2 == 0 then
        reduce12 (rawCoeff0 (bs.getD (off + 3 * t) 0#8) (bs.getD (off + 3 * t + 1) 0#8))
      else
        reduce12 (rawCoeff1 (bs.getD (off + 3 * t + 1) 0#8) (bs.getD (off + 3 * t + 2) 0#8)) := by
  simp [deserVec8h]

/-- Little-endian 16-byte representation of a 128-bit NEON register (`STR Qt` / `STP Qt1, Qt2`). -/
@[expose] def vec128Bytes (v : BitVec 128) : List (BitVec 8) :=
  unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64)

@[simp] theorem vec128Bytes_length (v : BitVec 128) : (vec128Bytes v).length = 16 := by
  simp [vec128Bytes]

/-- 32-byte (`2 × 128`-bit) output of iteration `k` of `deserialize_12` (`24` input bytes at `24 * k`). -/
@[expose] def deserChunk32 (bs : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  vec128Bytes (deserVec8h bs (24 * k)) ++ vec128Bytes (deserVec8h bs (24 * k + 12))

@[simp] theorem deserChunk32_length (bs : List (BitVec 8)) (k : Nat) :
    (deserChunk32 bs k).length = 32 := by
  simp [deserChunk32]

/-- Prefix of `k` 32-byte deserialized chunks (`32 * k` bytes). -/
@[expose] def reducedPolyPrefix (bs : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  ((List.range k).map (deserChunk32 bs)).flatten

@[simp] theorem reducedPolyPrefix_zero (bs : List (BitVec 8)) :
    reducedPolyPrefix bs 0 = [] := rfl

theorem reducedPolyPrefix_succ (bs : List (BitVec 8)) (k : Nat) :
    reducedPolyPrefix bs (k + 1) = reducedPolyPrefix bs k ++ deserChunk32 bs k := by
  simp [reducedPolyPrefix, List.range_succ]

@[simp] theorem reducedPolyPrefix_length (bs : List (BitVec 8)) :
    ∀ k : Nat, (reducedPolyPrefix bs k).length = 32 * k
  | 0 => rfl
  | k + 1 => by
    rw [reducedPolyPrefix_succ, List.length_append, reducedPolyPrefix_length bs k,
      deserChunk32_length]
    omega

/-- Full 512-byte (`16 × 32`-byte) in-memory representation of a `deserialize_12`-decoded polynomial. -/
@[expose] def reducedPolyBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  reducedPolyPrefix bs 16

@[simp] theorem reducedPolyBytes_length (bs : List (BitVec 8)) :
    (reducedPolyBytes bs).length = 512 := by
  simp [reducedPolyBytes]

/-- Register/pure invariant entering `Seg3` at `b + 0x044c#64`. -/
@[expose] def Seg3Pre (s0 s : State) (hdr ek : List (BitVec 8)) : Prop :=
  hdr.length = 64 ∧
  ek.length = 1152 ∧
  sha3_256List (ek ++ hdr.take 32) = (hdr.drop 32).take 32 ∧
  s.sp = s0.sp - 4784#64 ∧
  UnspilledSaved s0 s ∧
  s.readReg64 .x19 = (s0.sp - 4784#64) + 1168#64 ∧
  s.readReg64 .x20 = (s0.sp - 4784#64) + 2736#64 ∧
  s.readReg64 .x21 = (s0.sp - 4784#64) + 1200#64

/-- Spatial assertion entering `Seg3` at `b + 0x044c#64`. -/
@[expose] def Seg3Spatial (s0 : State) (hdrA : BitVec 64) (hdr : List (BitVec 8))
    (ekA : BitVec 64) (ek : List (BitVec 8)) (R : SepProp) : SepProp :=
  let sp := s0.sp - 4784#64
  SavedFrame s0.sp s0 ∗
    memRegion sp 16 ∗
    ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
    ((sp + 1200#64) ↦ₛ reducedPolyBytes (ek.take 384)) ∗
    ((sp + 1712#64) ↦ₛ reducedPolyBytes ((ek.drop 384).take 384)) ∗
    ((sp + 2224#64) ↦ₛ reducedPolyBytes ((ek.drop 768).take 384)) ∗
    memRegion (sp + 2736#64) 1984 ∗
    stackAt sp 1040 ∗
    (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R

/-! ## 2. `.rodata` Load & O(1) Dead-Store `memRegion` Step Lemmas -/

/-- Collapse chained `(setPC · |>.setMem ·)` updates so unrolled dead-store blocks stay `O(1)`. -/
@[simp] theorem setPC_setMem_collapse (s : State) (p1 p2 : BitVec 64) (m1 m2 : Memory) :
    (((s.setPC p1).setMem m1).setPC p2).setMem m2 = (s.setPC p2).setMem m2 := rfl

/-- Step `LDR Qt, [addr]` against a 16-byte `.rodata` constant without retaining `.rodata` atoms in `P`. -/
theorem step_ldrQ128_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc roAddr : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {v : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (roAddr, wb))
    (hro : RoDataAt s.mem roAddr bs)
    (hlen : bs.length = 16 := by simp)
    (hv : cst16Vec bs = v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hm' : s.mem ⊨ (roAddr ↦ᵣ bs) ∗ (P ∗ R) :=
    Satisfies.rodata_intro hro.1 hro.2 (by omega) hm
  have hload1 : SepLoad64 roAddr (roAddr ↦ᵣ bs) (ByteSlice.readLE bs 0 8) :=
    SepLoad64.of_pointsToBytes_readLE_RO (sepConj_emp _).symm (by omega) (by clear * -; bv_omega)
  have hload2 : SepLoad64 (roAddr + 8#64) (roAddr ↦ᵣ bs) (ByteSlice.readLE bs 8 8) :=
    SepLoad64.of_pointsToBytes_readLE_RO (sepConj_emp _).symm (by omega) (by clear * -; bv_omega)
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 roAddr = ByteSlice.readLE bs 0 8 := hload1.load hm'
  have hread2 : s.mem.read64 (roAddr + 8#64) = ByteSlice.readLE bs 8 8 := hload2.load hm'
  have hcan16 : s.mem.canRead roAddr 16 = true :=
    Memory.canRead_16_of_8_8 (hload1.readable hm') (hload2.readable hm')
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .Q128 vt addr) s = s' := by
    rw [← hexec, ← hv, cst16Vec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, Memory.read128,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hread1, hread2, hcan16,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- Step a dead `STR Qt, [addr]` (no writeback) directly inside `memRegion base total ∗ Rest` in `O(1)`. -/
theorem step_strQ128_region {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc base ea : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {off total : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hbounds : off + 16 ≤ total)
    (htotal : total ≤ 2 ^ 64)
    (hea : base + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') (memRegion base total ∗ Rest) post) :
    SepWP prog target_pc s (memRegion base total ∗ Rest) post := by
  have hsplit1 : memRegion base total =
      memRegion base off ∗ memRegion (base + BitVec.ofNat 64 off) (total - off) := by
    have h := memRegion_split base off (total - off) (by omega)
    rwa [Nat.add_sub_of_le (by omega)] at h
  have hsplit2 : memRegion (base + BitVec.ofNat 64 off) (total - off) =
      memRegion ea 16 ∗ memRegion (ea + 16#64) (total - off - 16) := by
    rw [← hea]
    have h := memRegion_split (base + BitVec.ofNat 64 off) 16 (total - off - 16) (by omega)
    rw [show 16 + (total - off - 16) = total - off by omega] at h
    simpa [BitVec.add_assoc] using h
  refine SepWP.weaken_pre
    (show memRegion base total ∗ Rest ⊢
        memRegion ea 16 ∗ (memRegion base off ∗ memRegion (ea + 16#64) (total - off - 16) ∗ Rest) by
      rw [hsplit1, hsplit2]; sep_frame) ?_
  apply sepWP_elim_region16
  intro w0 w1
  apply SepWP.step_strSimd128 hpc hrun hfetch hsp haddr rfl rfl rfl
    (SepStore64.left (SepStore64.here rfl))
    (SepStore64.right (SepStore64.left (SepStore64.here rfl)))
    rfl
  intro m'
  refine SepWP.weaken_pre ?_ (hnext m')
  rw [hsplit1, hsplit2]
  exact entails_sub (cells16_entails_memRegion ea _ _) (by sep_frame) (by sep_frame)

/-- Step a dead `STP Qt1, Qt2, [addr]` (no writeback) directly inside `memRegion base total ∗ Rest` in `O(1)`. -/
theorem step_stpQ128_region {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc base ea : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {off total : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hbounds : off + 32 ≤ total)
    (htotal : total ≤ 2 ^ 64)
    (hea : base + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') (memRegion base total ∗ Rest) post) :
    SepWP prog target_pc s (memRegion base total ∗ Rest) post := by
  have hsplit1 : memRegion base total =
      memRegion base off ∗ memRegion (base + BitVec.ofNat 64 off) (total - off) := by
    have h := memRegion_split base off (total - off) (by omega)
    rwa [Nat.add_sub_of_le (by omega)] at h
  have hsplit2 : memRegion (base + BitVec.ofNat 64 off) (total - off) =
      memRegion ea 32 ∗ memRegion (ea + 32#64) (total - off - 32) := by
    rw [← hea]
    have h := memRegion_split (base + BitVec.ofNat 64 off) 32 (total - off - 32) (by omega)
    rw [show 32 + (total - off - 32) = total - off by omega] at h
    simpa [BitVec.add_assoc] using h
  refine SepWP.weaken_pre
    (show memRegion base total ∗ Rest ⊢
        memRegion ea 32 ∗ (memRegion base off ∗ memRegion (ea + 32#64) (total - off - 32) ∗ Rest) by
      rw [hsplit1, hsplit2]; sep_frame) ?_
  apply sepWP_elim_region32
  intro w0 w1 w2 w3
  apply SepWP.step_stpSimd128 hpc hrun hfetch hsp haddr rfl rfl (by clear * -; bv_omega)
    rfl rfl rfl rfl
    (SepStore64.left (SepStore64.here rfl))
    (SepStore64.right (SepStore64.left (SepStore64.here rfl)))
    (SepStore64.right (SepStore64.right (SepStore64.left (SepStore64.here rfl))))
    (SepStore64.right (SepStore64.right (SepStore64.right (SepStore64.left (SepStore64.here rfl)))))
    rfl
  intro m'
  refine SepWP.weaken_pre ?_ (hnext m')
  rw [hsplit1, hsplit2]
  exact entails_sub (cells32_entails_memRegion ea _ _ _ _) (by sep_frame) (by sep_frame)

/-! ## 3. AdvSIMD `execInstWithSvc` Bridges & Pure `neonDeser12 = deserVec8h` Equivalence -/

private theorem getLsbD_0xff128 :
    ∀ k : Fin 128, (0xff#128).getLsbD k.val = decide (k.val < 8) := by
  decide +kernel

private theorem getLsbD_0xffff128 :
    ∀ k : Fin 128, ((1#128 <<< 16 - 1#128) : BitVec 128).getLsbD k.val = decide (k.val < 16) := by
  decide +kernel

private theorem getLsbD_0xffffffff128 :
    ∀ k : Fin 128, (0xffffffff#128).getLsbD k.val = decide (k.val < 32) := by
  decide +kernel

private theorem getLsbD_not_lane2_mask128 :
    ∀ k : Fin 128, (~~~(0xffffffff#128 <<< 64)).getLsbD k.val = decide (k.val < 64 ∨ 96 ≤ k.val) := by
  decide +kernel

private theorem tblByte_1 (vn : BitVec 128) (idx : Nat) (h : idx < 16) :
    ((vn >>> (idx * 8)) &&& 0xff#128) = (lane8 vn ⟨idx, h⟩).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hm := getLsbD_0xff128 ⟨b, hb⟩
  dsimp only at hm
  simp only [lane8, BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, hm]
  by_cases hb8 : b < 8
  · simp only [hb8, decide_true, Bool.true_and, Bool.and_true, Nat.mul_comm idx 8]
  · simp only [hb8, decide_false, Bool.false_and, Bool.and_false]

private theorem tblIdx_eq (vm : BitVec 128) (j : Fin 16) :
    ((vm >>> (j.val * 8)) &&& 0xff#128).toNat = (lane8 vm j).toNat := by
  have h : ((vm >>> (j.val * 8)) &&& 0xff#128) = (lane8 vm j).zeroExtend 128 :=
    tblByte_1 vm j.val j.isLt
  rw [h, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hj := (lane8 vm j).isLt
  exact Nat.mod_eq_of_lt (by omega)

private theorem zext_or_shift {w : Nat} (lo : BitVec w) (hi : BitVec 8) (_hw : w + 8 ≤ 128) :
    lo.zeroExtend 128 ||| (hi.zeroExtend 128 <<< w) = (hi ++ lo).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases hbw : b < w
  · simp [hbw]
  · by_cases hb8 : b < w + 8
    · have hlo : lo.getLsbD b = false := BitVec.getLsbD_of_ge lo b (by omega)
      simp [hbw, hlo, show b - w < 128 by omega]
    · have hlo : lo.getLsbD b = false := BitVec.getLsbD_of_ge lo b (by omega)
      have hhi : hi.getLsbD (b - w) = false := BitVec.getLsbD_of_ge hi (b - w) (by omega)
      simp [hbw, hlo, hhi]

private theorem zext_or_16 (f : Fin 16 → BitVec 8) :
    (((((((((((((((0#128 ||| ((f 0).zeroExtend 128 <<< (0 * 8))) ||| ((f 1).zeroExtend 128 <<< (1 * 8))) |||
      ((f 2).zeroExtend 128 <<< (2 * 8))) ||| ((f 3).zeroExtend 128 <<< (3 * 8))) |||
      ((f 4).zeroExtend 128 <<< (4 * 8))) ||| ((f 5).zeroExtend 128 <<< (5 * 8))) |||
      ((f 6).zeroExtend 128 <<< (6 * 8))) ||| ((f 7).zeroExtend 128 <<< (7 * 8))) |||
      ((f 8).zeroExtend 128 <<< (8 * 8))) ||| ((f 9).zeroExtend 128 <<< (9 * 8))) |||
      ((f 10).zeroExtend 128 <<< (10 * 8))) ||| ((f 11).zeroExtend 128 <<< (11 * 8))) |||
      ((f 12).zeroExtend 128 <<< (12 * 8))) ||| ((f 13).zeroExtend 128 <<< (13 * 8))) |||
      ((f 14).zeroExtend 128 <<< (14 * 8))) ||| ((f 15).zeroExtend 128 <<< (15 * 8)) =
    pack16x8 f := by
  simp only [Nat.zero_mul, BitVec.shiftLeft_zero, BitVec.zero_or]
  rw [zext_or_shift (f 0) (f 1) (by decide),
      zext_or_shift _ (f 2) (by decide),
      zext_or_shift _ (f 3) (by decide),
      zext_or_shift _ (f 4) (by decide),
      zext_or_shift _ (f 5) (by decide),
      zext_or_shift _ (f 6) (by decide),
      zext_or_shift _ (f 7) (by decide),
      zext_or_shift _ (f 8) (by decide),
      zext_or_shift _ (f 9) (by decide),
      zext_or_shift _ (f 10) (by decide),
      zext_or_shift _ (f 11) (by decide),
      zext_or_shift _ (f 12) (by decide),
      zext_or_shift _ (f 13) (by decide),
      zext_or_shift _ (f 14) (by decide),
      zext_or_shift _ (f 15) (by decide)]
  apply ext_lane16; apply fin8_cases
  all_goals {
    unfold lane16 pack16x8 BitVec.zeroExtend
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    repeat rw [BitVec.getLsbD_append]
    rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b
    all_goals rfl
  }

/-- Single-register `TBL Vd.16B, {Vn.16B}, Vm.16B` (`len = 0`, `isTbx = false`) matches `simdTbl16b`. -/
@[simp, arm64_norm, wp_norm]
theorem exec_simdTbl_16b_1 (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdTbl true rm 0#2 false rn rd) s =
      (s.writeVReg128 rd (simdTbl16b (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  congr 2
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  let f : Fin 16 → BitVec 8 := fun j =>
    if h : (lane8 vm j).toNat < 16 then lane8 vn ⟨(lane8 vm j).toNat, h⟩ else 0#8
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:16] : Std.Legacy.Range).start ([:16] : Std.Legacy.Range).size
      ([:16] : Std.Legacy.Range).step = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  have hstep (j : Fin 16) :
      (if ((vm >>> (j.val * 8)) &&& 0xff#128).toNat < 16 then
        (s.readVReg128 (rn + BitVec.ofNat 5 (((vm >>> (j.val * 8)) &&& 0xff#128).toNat / 16)) >>>
          ((((vm >>> (j.val * 8)) &&& 0xff#128).toNat % 16) * 8)) &&& 0xff#128
       else 0#128) = (f j).zeroExtend 128 := by
    dsimp only [f]
    rw [tblIdx_eq vm j]
    by_cases h : (lane8 vm j).toNat < 16
    · have hdiv : (lane8 vm j).toNat / 16 = 0 := Nat.div_eq_of_lt h
      have hmod : (lane8 vm j).toNat % 16 = (lane8 vm j).toNat := Nat.mod_eq_of_lt h
      simp only [h, ↓reduceIte, ↓reduceDIte, hdiv, hmod, BitVec.add_zero]
      exact tblByte_1 vn (lane8 vm j).toNat h
    · simp only [h, ↓reduceIte, ↓reduceDIte]; rfl
  change _ = pack16x8 f
  rw [hstep ⟨0, by decide⟩, hstep ⟨1, by decide⟩, hstep ⟨2, by decide⟩, hstep ⟨3, by decide⟩,
      hstep ⟨4, by decide⟩, hstep ⟨5, by decide⟩, hstep ⟨6, by decide⟩, hstep ⟨7, by decide⟩,
      hstep ⟨8, by decide⟩, hstep ⟨9, by decide⟩, hstep ⟨10, by decide⟩, hstep ⟨11, by decide⟩,
      hstep ⟨12, by decide⟩, hstep ⟨13, by decide⟩, hstep ⟨14, by decide⟩, hstep ⟨15, by decide⟩]
  exact zext_or_16 f

/-- `USHL Vd.8H, Vn.8H, Vm.8H` (`q = true, u = true, size = 01, opcode = 01000`) matches `simdUshl8h`. -/
@[simp, arm64_norm, wp_norm]
theorem exec_simdUshl_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true true 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    Bool.true_or, decide_false, decide_true, ↓reduceIte, BitVec.reduceEq,
    show (8 <<< (0b01#2).toNat) = 16 from rfl]
  congr 2
  apply ext_lane16
  intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdUshl8h]
  set x := lane16 (s.readVReg128 rn) i
  set sh := lane16 (s.readVReg128 rm) i
  have htr : ((sh.zeroExtend 128).truncate 8) = sh.truncate 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hk,
      show k < 128 by omega, decide_true, Bool.true_and]
  dsimp only [simdUshlElem16]
  rw [htr]
  set sb := (sh.truncate 8).toInt
  by_cases hge : sb ≥ 0
  · simp only [hge, ↓reduceIte]
    by_cases hamt : sb.toNat ≥ 16
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [BitVec.truncate_eq_setWidth, show k < sb.toNat by omega]
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      have hm := getLsbD_0xffff128 ⟨k, by omega⟩
      dsimp only at hm
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
        BitVec.getLsbD_shiftLeft, hm, hk, show k < 128 by omega, decide_true, Bool.true_and]
      by_cases hlt : k < sb.toNat
      · simp [hlt]
      · simp [hlt, show k - sb.toNat < 16 by omega, show k - sb.toNat < 128 by omega]
  · simp only [hge, ↓reduceIte]
    by_cases hamt : (-sb).toNat ≥ 16
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      have hx : x.getLsbD ((-sb).toNat + k) = false :=
        BitVec.getLsbD_of_ge x ((-sb).toNat + k) (by omega)
      simp [BitVec.truncate_eq_setWidth, hx]
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        hk, show (-sb).toNat + k < 128 by omega, decide_true, Bool.true_and]

/-- `CMHS Vd.8H, Vn.8H, Vm.8H` (`q = true, u = true, size = 01, opcode = 00111`) matches `simdCmhs8h`. -/
@[simp, arm64_norm, wp_norm]
theorem exec_simdCmhs_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true true 0b01#2 rm 0b00111#5 rn rd) s =
      (s.writeVReg128 rd (simdCmhs8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq, show (8 <<< (0b01#2).toNat) = 16 from rfl]
  congr 2
  apply ext_lane16
  intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdCmhs8h]
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  have hx := x.isLt; have hy := y.isLt
  have hule : BitVec.ule (y.zeroExtend 128) (x.zeroExtend 128) = decide (y.toNat ≤ x.toNat) := by
    simp only [BitVec.ule, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128)]
  rw [hule]
  by_cases hle : y.toNat ≤ x.toNat <;> simp [hle]

/-- `ADD Vd.8H, Vn.8H, Vm.8H` (`q = true, u = false, size = 01, opcode = 10000`) matches `simdAdd8h`. -/
@[simp, arm64_norm, wp_norm]
theorem exec_simdAdd_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq, show (8 <<< (0b01#2).toNat) = 16 from rfl]
  congr 2
  apply ext_lane16
  intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdAdd8h]
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  have hx := x.isLt; have hy := y.isLt
  change ((x.zeroExtend 128 + y.zeroExtend 128).setWidth 16) = x + y
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128)]
  omega

/-- The 12-byte load state produced by `LDR Dt, [p]` followed by `LD1 {Vt.S}[2], [p + 8]`. -/
@[expose] def loadVec12 (bs : List (BitVec 8)) (off : Nat) : BitVec 128 :=
  setSimdLane
    ((pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)).zeroExtend 128)
    32 2
    ((pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)).zeroExtend 128)

/-- Pure composition of the 6 AdvSIMD instructions in `deserialize_12`. -/
@[expose] def neonDeser12 (v : BitVec 128) : BitVec 128 :=
  let t := simdTbl16b v 0x0b0a0a09080707060504040302010100#128
  let u := simdUshl8h t 0xfffc0000fffc0000fffc0000fffc0000#128
  let m := u &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128
  let c := simdCmhs8h m 0x0d010d010d010d010d010d010d010d01#128
  let s := c &&& 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128
  simdAdd8h s m

private theorem loadVec12_eq_bytes (bs : List (BitVec 8)) (off : Nat) :
    loadVec12 bs off =
      0#32 ++
      pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
        (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8) ++
      pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
        (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
        (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) := by
  unfold loadVec12 setSimdLane
  set lo := pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)
  set mid := pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
      (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hm1 := getLsbD_not_lane2_mask128 ⟨k, hk⟩
  dsimp only at hm1
  simp only [show 32 * 2 = 64 from rfl, show (1#128 <<< 32 - 1#128) = 0xffffffff#128 from rfl,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, hm1, hk, decide_true, Bool.true_and]
  repeat rw [BitVec.getLsbD_append]
  by_cases hk64 : k < 64
  · simp [hk64]
  · have hm2 := getLsbD_0xffffffff128 ⟨k - 64, by omega⟩
    dsimp only at hm2
    rw [hm2]
    by_cases hk96 : k < 96
    · simp [hk64, show ¬ (96 ≤ k) by omega, show k - 64 < 32 by omega, show k - 64 < 128 by omega]
    · have hlo : lo.getLsbD k = false := BitVec.getLsbD_of_ge lo k (by omega)
      simp [hk64, hlo, show 96 ≤ k by omega, show ¬ (k - 64 < 32) by omega,
        show k - 64 < 128 by omega, BitVec.getLsbD_zero]

private theorem lane8_pack12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : BitVec 8) :
    let v : BitVec 128 := 0#32 ++ pack32 b8 b9 b10 b11 ++ pack64 b0 b1 b2 b3 b4 b5 b6 b7
    lane8 v 0 = b0 ∧ lane8 v 1 = b1 ∧ lane8 v 2 = b2 ∧ lane8 v 3 = b3 ∧
    lane8 v 4 = b4 ∧ lane8 v 5 = b5 ∧ lane8 v 6 = b6 ∧ lane8 v 7 = b7 ∧
    lane8 v 8 = b8 ∧ lane8 v 9 = b9 ∧ lane8 v 10 = b10 ∧ lane8 v 11 = b11 := by
  dsimp only [lane8, pack32, pack64]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals {
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_extractLsb']
    repeat rw [BitVec.getLsbD_append]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals first | rfl | omega
  }

private theorem pack16x8_eq_pack8x16 (f : Fin 16 → BitVec 8) :
    pack16x8 f = pack8x16 (fun i => f ⟨2 * i.val + 1, by omega⟩ ++ f ⟨2 * i.val, by omega⟩) := by
  apply ext_lane16; apply fin8_cases
  all_goals {
    rw [lane16_pack8x16]
    unfold lane16 pack16x8
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_extractLsb']
    repeat rw [BitVec.getLsbD_append]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals first | rfl | omega
  }

private theorem cst16_3_lane8_even :
    ∀ i : Fin 8,
      (lane8 0x0b0a0a09080707060504040302010100#128 ⟨2 * i.val, by omega⟩).toNat =
        3 * (i.val / 2) + i.val % 2 := by
  decide +kernel

private theorem cst16_3_lane8_odd :
    ∀ i : Fin 8,
      (lane8 0x0b0a0a09080707060504040302010100#128 ⟨2 * i.val + 1, by omega⟩).toNat =
        3 * (i.val / 2) + i.val % 2 + 1 := by
  decide +kernel

private theorem tbl_loadVec12_eq (bs : List (BitVec 8)) (off : Nat) :
    simdTbl16b (loadVec12 bs off) 0x0b0a0a09080707060504040302010100#128 =
      pack8x16 fun i =>
        let t := i.val / 2
        if i.val % 2 == 0 then
          bs.getD (off + 3 * t + 1) 0#8 ++ bs.getD (off + 3 * t) 0#8
        else
          bs.getD (off + 3 * t + 2) 0#8 ++ bs.getD (off + 3 * t + 1) 0#8 := by
  rw [loadVec12_eq_bytes]
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11⟩ :=
    lane8_pack12 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
      (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) (bs.getD (off + 8) 0#8)
      (bs.getD (off + 9) 0#8) (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  unfold simdTbl16b
  rw [pack16x8_eq_pack8x16]
  apply ext_lane16
  intro i
  rw [lane16_pack8x16, lane16_pack8x16, cst16_3_lane8_odd i, cst16_3_lane8_even i]
  revert i; apply fin8_cases
  · exact congrArg₂ (· ++ ·) hl1 hl0
  · exact congrArg₂ (· ++ ·) hl2 hl1
  · exact congrArg₂ (· ++ ·) hl4 hl3
  · exact congrArg₂ (· ++ ·) hl5 hl4
  · exact congrArg₂ (· ++ ·) hl7 hl6
  · exact congrArg₂ (· ++ ·) hl8 hl7
  · exact congrArg₂ (· ++ ·) hl10 hl9
  · exact congrArg₂ (· ++ ·) hl11 hl10

private theorem getLsbD_0x0fff16 :
    ∀ k : Fin 16, (0x0fff#16).getLsbD k.val = decide (k.val < 12) := by
  decide +kernel

private theorem getLsbD_0x0f16 :
    ∀ k : Fin 16, (0x0f#16).getLsbD k.val = decide (k.val < 4) := by
  decide +kernel

private theorem even_mask_rawCoeff0 (b0 b1 : BitVec 8) :
    (b1 ++ b0) &&& 0x0fff#16 = BitVec.ofNat 16 (rawCoeff0 b0 b1) := by
  have h : (b1 ++ b0) &&& 0x0fff#16 =
      b0.zeroExtend 16 ||| ((b1.zeroExtend 16 &&& 0x0f#16) <<< 8) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hm12 := getLsbD_0x0fff16 ⟨i, hi⟩
    dsimp only at hm12
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hm12, hi,
      decide_true, Bool.true_and]
    by_cases hi8 : i < 8
    · simp only [hi8, show i < 12 by omega, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_and, Bool.or_false, ↓reduceIte]
    · by_cases hi12 : i < 12
      · have hm4 := getLsbD_0x0f16 ⟨i - 8, by omega⟩
        dsimp only at hm4
        have hb0 : b0.getLsbD i = false := BitVec.getLsbD_of_ge b0 i (by omega)
        simp only [hi8, hi12, hm4, hb0, show i - 8 < 4 by omega, show i - 8 < 16 by omega,
          decide_true, decide_false, Bool.and_true, Bool.not_false, Bool.true_and,
          Bool.false_or, ↓reduceIte]
      · have hm4 := getLsbD_0x0f16 ⟨i - 8, by omega⟩
        dsimp only at hm4
        have hb0 : b0.getLsbD i = false := BitVec.getLsbD_of_ge b0 i (by omega)
        simp only [hi8, hi12, hm4, hb0, show ¬ (i - 8 < 4) by omega, show i - 8 < 16 by omega,
          decide_true, decide_false, Bool.and_false, Bool.not_false, Bool.true_and,
          Bool.false_or, ↓reduceIte]
  rw [h, rawCoeff0, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem odd_mask_rawCoeff1 (b1 b2 : BitVec 8) :
    ((b2 ++ b1) >>> 4) &&& 0x0fff#16 = BitVec.ofNat 16 (rawCoeff1 b1 b2) := by
  have h : ((b2 ++ b1) >>> 4) &&& 0x0fff#16 =
      (b1.zeroExtend 16 >>> 4) ||| (b2.zeroExtend 16 <<< 4) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hm12 := getLsbD_0x0fff16 ⟨i, hi⟩
    dsimp only at hm12
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, hm12, hi, decide_true, Bool.true_and]
    by_cases hi4 : i < 4
    · simp only [hi4, show i < 12 by omega, show 4 + i < 16 by omega, show 4 + i < 8 by omega,
        decide_true, Bool.true_and, Bool.and_true, Bool.not_true, Bool.false_and, Bool.or_false, ↓reduceIte]
    · by_cases hi12 : i < 12
      · have hb1 : b1.getLsbD (4 + i) = false := BitVec.getLsbD_of_ge b1 (4 + i) (by omega)
        simp only [hi4, hi12, hb1, show 4 + i < 16 by omega, show ¬ (4 + i < 8) by omega,
          show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega,
          decide_true, decide_false, Bool.and_true, Bool.not_false, Bool.true_and,
          Bool.false_or, ↓reduceIte]
      · have hb2 : b2.getLsbD (i - 4) = false := BitVec.getLsbD_of_ge b2 (i - 4) (by omega)
        by_cases h16 : 4 + i < 16
        · have hb1 : b1.getLsbD (4 + i) = false := BitVec.getLsbD_of_ge b1 (4 + i) (by omega)
          simp only [hi4, hi12, h16, hb1, hb2, show ¬ (4 + i < 8) by omega,
            show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega,
            decide_true, decide_false, Bool.and_false, Bool.not_false,
            Bool.false_or, ↓reduceIte]
        · simp only [hi4, hi12, h16, hb2, show ¬ (4 + i < 8) by omega,
            show 4 + i - 8 = i - 4 by omega, show i - 4 < 16 by omega,
            decide_true, decide_false, Bool.and_false, Bool.false_and, Bool.not_false,
            Bool.false_or, ↓reduceIte]
  rw [h, rawCoeff1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem neon_cond_sub_blocks :
    ∀ hi : Fin 16, ∀ lo : Fin 256,
      let d := 256 * hi.val + lo.val
      (((if (3329#16).toNat ≤ (BitVec.ofNat 16 d).toNat then 0xffff#16 else 0#16) &&&
          0xf2ff#16) + BitVec.ofNat 16 d) == reduce12 d := by
  decide +kernel

private theorem neon_cond_sub_eq {d : Nat} (hd : d < 4096) :
    ((if (3329#16).toNat ≤ (BitVec.ofNat 16 d).toNat then 0xffff#16 else 0#16) &&&
        0xf2ff#16) + BitVec.ofNat 16 d = reduce12 d := by
  have h := eq_of_beq (neon_cond_sub_blocks ⟨d / 256, by omega⟩ ⟨d % 256, by omega⟩)
  dsimp only at h
  rwa [Nat.div_add_mod d 256] at h

/-- Exact vector equivalence: `neonDeser12 (loadVec12 bs off) = deserVec8h bs off`. -/
theorem neonDeser12_loadVec12 (bs : List (BitVec 8)) (off : Nat) :
    neonDeser12 (loadVec12 bs off) = deserVec8h bs off := by
  unfold neonDeser12
  rw [tbl_loadVec12_eq]
  apply ext_lane16
  have hushl0 (x : BitVec 16) : simdUshlElem16 x 0x0000#16 = x := by
    simp [simdUshlElem16]
  have hushl4 (x : BitVec 16) : simdUshlElem16 x 0xfffc#16 = x >>> 4 := by
    simp [simdUshlElem16]
  apply fin8_cases
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 0 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 0 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 0 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 0 = 0xf2ff#16 from rfl,
      show (0 : Fin 8).val = 0 from rfl, show 0 / 2 = 0 from rfl, show (0 % 2 == 0) = true from rfl,
      ↓reduceIte, Nat.mul_zero, Nat.add_zero, hushl0, even_mask_rawCoeff0]
    exact neon_cond_sub_eq (rawCoeff0_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 1 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 1 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 1 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 1 = 0xf2ff#16 from rfl,
      show (1 : Fin 8).val = 1 from rfl, show 1 / 2 = 0 from rfl,
      show (1 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Nat.mul_zero, Nat.add_zero, hushl4, odd_mask_rawCoeff1]
    exact neon_cond_sub_eq (rawCoeff1_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 2 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 2 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 2 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 2 = 0xf2ff#16 from rfl,
      show (2 : Fin 8).val = 2 from rfl, show 2 / 2 = 1 from rfl,
      show (2 % 2 == 0) = true from rfl, ↓reduceIte, hushl0, even_mask_rawCoeff0]
    exact neon_cond_sub_eq (rawCoeff0_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 3 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 3 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 3 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 3 = 0xf2ff#16 from rfl,
      show (3 : Fin 8).val = 3 from rfl, show 3 / 2 = 1 from rfl,
      show (3 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1]
    exact neon_cond_sub_eq (rawCoeff1_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 4 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 4 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 4 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 4 = 0xf2ff#16 from rfl,
      show (4 : Fin 8).val = 4 from rfl, show 4 / 2 = 2 from rfl,
      show (4 % 2 == 0) = true from rfl, ↓reduceIte, hushl0, even_mask_rawCoeff0]
    exact neon_cond_sub_eq (rawCoeff0_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 5 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 5 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 5 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 5 = 0xf2ff#16 from rfl,
      show (5 : Fin 8).val = 5 from rfl, show 5 / 2 = 2 from rfl,
      show (5 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1]
    exact neon_cond_sub_eq (rawCoeff1_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 6 = 0x0000#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 6 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 6 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 6 = 0xf2ff#16 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show 6 / 2 = 3 from rfl,
      show (6 % 2 == 0) = true from rfl, ↓reduceIte, hushl0, even_mask_rawCoeff0]
    exact neon_cond_sub_eq (rawCoeff0_lt_4096 _ _)
  · simp only [lane16_simdAdd8h, lane16_and, lane16_simdCmhs8h, lane16_simdUshl8h,
      lane16_pack8x16, lane16_deserVec8h,
      show lane16 0xfffc0000fffc0000fffc0000fffc0000#128 7 = 0xfffc#16 from rfl,
      show lane16 0x0fff0fff0fff0fff0fff0fff0fff0fff#128 7 = 0x0fff#16 from rfl,
      show lane16 0x0d010d010d010d010d010d010d010d01#128 7 = 3329#16 from rfl,
      show lane16 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128 7 = 0xf2ff#16 from rfl,
      show (7 : Fin 8).val = 7 from rfl, show 7 / 2 = 3 from rfl,
      show (7 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hushl4, odd_mask_rawCoeff1]
    exact neon_cond_sub_eq (rawCoeff1_lt_4096 _ _)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
