/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop

/-! # `validate_pk_bytes` (`B21`) — Segment 3 `serialize_12` Iteration Step Lemmas (`Role::Proof`). -/

set_option autoImplicit false
public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Step

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16 lane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdExt16b lane16_simdAdd8h
  simdSli2d simdSli4s simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  neonSerialize12Bytes neonSerialize12Half neonSerialize12Mix neonSerialize12Mix_unmasked)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  deserChunk32 deserChunk32_length deserVec8h reducedPolyBytes reducedPolyPrefix
  reducedPolyPrefix_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  cells32_eq_deserChunk32 exec_simdAdd_8h_svc step_vreg1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd (
  cmltZero_deserVec8h deserVec8h_lane_lt_4096 exec_simdAnd_16b exec_simdCmltZero_8h
  exec_simdDupScalar_h2 exec_simdExt_16b_8 exec_simdSli_2d_24 exec_simdSli_4s_12
  ext8_self_lane16_2 ext8_self_low32 low32_eq_lane64_0 reencodeChunk24 reencodePolyPrefix
  reencodePolyPrefix_length reencodePolyPrefix_succ svc_simdTrn1_4s svc_simdTrn1_8h
  svc_simdTrn2_4s svc_simdTrn2_8h)

/-! ## 1. `LDP Q1, Q2, [X9, #-16]` Chunk Load from `reducedPolyBytes` -/

private theorem range_split_at : ∀ (n k : Nat), k < n →
    ∃ suf : List Nat, List.range n = List.range k ++ [k] ++ suf
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · obtain ⟨suf, hsuf⟩ := range_split_at n k hlt
      exact ⟨suf ++ [n], by rw [List.range_succ, hsuf, List.append_assoc, List.append_assoc]⟩
    · exact ⟨[], by simp [List.range_succ]⟩

private theorem concat_extract64 (w : BitVec 128) :
    w.extractLsb' 64 64 ++ w.setWidth 64 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [BitVec.getLsbD_append]
  by_cases h64 : b < 64
  · simp [h64]
  · simp only [h64, ↓reduceIte, BitVec.getLsbD_extractLsb', show b - 64 < 64 by omega,
      decide_true, Bool.true_and]
    congr 1; omega

attribute [local irreducible] deserVec8h neonSerialize12Mix

theorem step_ldp_deserChunk {prog : Program} {target_pc src : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff k : Nat) (addr : AddrMode) (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.ldpSimd .Q128 1#5 2#5 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (src + BitVec.ofNat 64 (32 * k), none))
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 1#5 (deserVec8h bs (24 * k))).writeVReg128 2#5
          (deserVec8h bs (24 * k + 12))).setPC (b + BitVec.ofNat 64 nextOff))
      ((src ↦ₛ reducedPolyBytes bs) ∗ F) post) :
    SepWP prog target_pc s ((src ↦ₛ reducedPolyBytes bs) ∗ F) post := by
  obtain ⟨suf, hsuf⟩ := range_split_at 16 k hk16
  let tail := (suf.map (deserChunk32 bs)).flatten
  let d0 := deserVec8h bs (24 * k)
  let d1 := deserVec8h bs (24 * k + 12)
  have hbytes : reducedPolyBytes bs = reducedPolyPrefix bs k ++ (deserChunk32 bs k ++ tail) := by
    unfold reducedPolyBytes reducedPolyPrefix
    rw [hsuf, List.map_append, List.map_append, List.flatten_append, List.flatten_append]
    simp [tail, List.append_assoc]
  have hcells := cells32_eq_deserChunk32 (src + BitVec.ofNat 64 (32 * k)) bs k
  dsimp only at hcells
  let Rest := (src ↦ₛ reducedPolyPrefix bs k) ∗ ((src + BitVec.ofNat 64 (32 * k) + 32#64) ↦ₛ tail) ∗ F
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine SepWP.weaken_pre (show (src ↦ₛ reducedPolyBytes bs) ∗ F ⊢
      ((src + BitVec.ofNat 64 (32 * k)) ↦₆₄ d0.extractLsb' 0 64) ∗
      ((src + BitVec.ofNat 64 (32 * k) + 8#64) ↦₆₄ d0.extractLsb' 64 64) ∗
      ((src + BitVec.ofNat 64 (32 * k) + 16#64) ↦₆₄ d1.extractLsb' 0 64) ∗
      ((src + BitVec.ofNat 64 (32 * k) + 24#64) ↦₆₄ d1.extractLsb' 64 64) ∗ Rest by
      dsimp only [d0, d1, Rest]; rw [hbytes, pointsToBytes_append, reducedPolyPrefix_length,
        pointsToBytes_append, deserChunk32_length, ← hcells]; sep_frame) ?_
  refine SepWP.step_ldpSimd128
    (s' := (((s.writeVReg128 1#5 d0).writeVReg128 2#5 d1).setPC (b + BitVec.ofNat 64 nextOff)))
    (ea := src + BitVec.ofNat 64 (32 * k)) (wb := none)
    hpc hrun hfetch hsp haddr rfl rfl (by clear * -; bv_omega)
    (SepLoad64.left (SepLoad64.here rfl))
    (SepLoad64.right (SepLoad64.left (SepLoad64.here rfl)))
    (SepLoad64.right (SepLoad64.right (SepLoad64.left (SepLoad64.here rfl))))
    (SepLoad64.right (SepLoad64.right (SepLoad64.right (SepLoad64.left (SepLoad64.here rfl)))))
    (by simp [applyWriteback, d0, d1, concat_extract64, hpc']) ?_
  refine SepWP.weaken_pre ?_ hnext
  dsimp only [d0, d1, Rest]; rw [hbytes, pointsToBytes_append, reducedPolyPrefix_length,
    pointsToBytes_append, deserChunk32_length, ← hcells]; sep_frame

/-! ## 2. 18-Instruction AdvSIMD `serialize_12` Bit-Packing Block -/

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

private theorem simdAdd8h_zero_left (v : BitVec 128) : simdAdd8h 0#128 v = v := by
  apply Poly.Lane16.ext_lane16; intro i
  have hz : lane16 0#128 i = 0#16 := by simp [lane16]
  rw [lane16_simdAdd8h, hz, BitVec.zero_add]

theorem step_ser12_simd18 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 k : Nat) (bs : List (BitVec 8))
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hv1 : s.readVReg128 1#5 = deserVec8h bs (24 * k))
    (hv2 : s.readVReg128 2#5 = deserVec8h bs (24 * k + 12))
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
      s'.readVReg128 1#5 = neonSerialize12Mix (deserVec8h bs (24 * k)) →
      s'.readVReg128 3#5 = neonSerialize12Mix (deserVec8h bs (24 * k + 12)) →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  let d0 := deserVec8h bs (24 * k)
  let d1 := deserVec8h bs (24 * k + 12)
  let mix0 := simdSli4s (simdTrn1_8h d0 d0) (simdTrn2_8h d0 d0) 12
  let mix1 := simdSli4s (simdTrn1_8h d1 d1) (simdTrn2_8h d1 d1) 12
  have hunm0 : simdSli2d (simdTrn1_4s mix0 mix0) (simdTrn2_4s mix0 mix0) 24 = neonSerialize12Mix d0 :=
    neonSerialize12Mix_unmasked d0 (deserVec8h_lane_lt_4096 bs (24 * k))
  have hunm1 : simdSli2d (simdTrn1_4s mix1 mix1) (simdTrn2_4s mix1 mix1) 24 = neonSerialize12Mix d1 :=
    neonSerialize12Mix_unmasked d1 (deserVec8h_lane_lt_4096 bs (24 * k + 12))
  refine step_vreg1 b p0 (p0 + 4) 3#5 0#128 hpc hrun hf0
    (by rw [exec_simdCmltZero_8h]; simp [hv1, cmltZero_deserVec8h]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 4#5 0#128 rfl (by simp [hrun]) hf1
    (by rw [exec_simdCmltZero_8h]; simp [hv2, cmltZero_deserVec8h]) (by omega) ?_
  refine step_vreg1 b (p0 + 8) (p0 + 12) 3#5 0#128 rfl (by simp [hrun]) hf2
    (by rw [exec_simdAnd_16b]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 12) (p0 + 16) 4#5 0#128 rfl (by simp [hrun]) hf3
    (by rw [exec_simdAnd_16b]; simp) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 1#5 d0 rfl (by simp [hrun]) hf4
    (by rw [exec_simdAdd_8h_svc]; simp [hv1, d0, simdAdd8h_zero_left]) (by omega) ?_
  refine step_vreg1 b (p0 + 20) (p0 + 24) 2#5 d1 rfl (by simp [hrun]) hf5
    (by rw [exec_simdAdd_8h_svc]; simp [hv2, d1, simdAdd8h_zero_left]) (by omega) ?_
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
  refine hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp [hrun]
  · simp
  · intro r; simp
  · simp
  · simp
  · simp [d0]
  · simp [d1]
  · simp only [calleeSavedVRegs_setPC, csv1, csv2, csv3, csv4]

/-! ## 3. 14-Instruction Interleaved `serialize_12` Store Tail -/

private theorem sepWP_elim_cell4 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 32, SepWP prog target s ((a ↦₃₂ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 4 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_cell2 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 16, SepWP prog target s ((a ↦₁₆ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 2 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_two, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_region6 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w : BitVec 32) (u : BitVec 16),
      SepWP prog target s ((a ↦₃₂ w) ∗ ((a + 4#64) ↦₁₆ u) ∗ R0) post) :
    SepWP prog target s (memRegion a 6 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 4#64) (n := 4) (k := 2) rfl (by bv_omega) (by decide), sepConj_assoc]
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
  rw [memRegion_split' (b' := a + 6#64) (n := 6) (k := 6) rfl (by bv_omega) (by decide), sepConj_assoc]
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
  rw [memRegion_split' (b' := a + 12#64) (n := 12) (k := 12) rfl (by bv_omega) (by decide), sepConj_assoc]
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

private theorem cells24_eq_reencodeChunk24 (a : BitVec 64) (bs : List (BitVec 8)) (k : Nat) :
    let m0 := neonSerialize12Mix (deserVec8h bs (24 * k))
    let m1 := neonSerialize12Mix (deserVec8h bs (24 * k + 12))
    (a ↦₃₂ (lane64 m0 0).truncate 32) ∗ ((a + 4#64) ↦₁₆ lane16 m0 2) ∗
    ((a + 6#64) ↦₃₂ (lane64 (simdExt16b m0 m0 8) 0).truncate 32) ∗
    ((a + 10#64) ↦₁₆ lane16 (simdExt16b m0 m0 8) 2) ∗
    ((a + 12#64) ↦₃₂ (lane64 m1 0).truncate 32) ∗ ((a + 16#64) ↦₁₆ lane16 m1 2) ∗
    ((a + 18#64) ↦₃₂ (lane64 (simdExt16b m1 m1 8) 0).truncate 32) ∗
    ((a + 22#64) ↦₁₆ lane16 (simdExt16b m1 m1 8) 2) =
    (a ↦ₛ reencodeChunk24 bs k) := by
  dsimp only
  have hc0 := cells12_eq_neonSerialize12Half a (deserVec8h bs (24 * k))
  have hc1 := cells12_eq_neonSerialize12Half (a + 12#64) (deserVec8h bs (24 * k + 12))
  dsimp only at hc0 hc1
  rw [reencodeChunk24, neonSerialize12Bytes, pointsToBytes_append,
    show (neonSerialize12Half (deserVec8h bs (24 * k))).length = 12 by simp [neonSerialize12Half],
    ← hc0, ← hc1]
  simp only [sepConj_assoc, show a + 12#64 + 4#64 = a + 16#64 by bv_omega,
    show a + 12#64 + 6#64 = a + 18#64 by bv_omega, show a + 12#64 + 10#64 = a + 22#64 by bv_omega]

@[simp] private theorem setWidth16_zext128 (x : BitVec 16) : (x.zeroExtend 128).setWidth 16 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [hb]

private theorem step_strS32_off {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff off : Nat) (unscaled : Bool) (vt : BitVec 5) (ptrReg : Reg) (v : BitVec 32)
    (hptr : ptrReg ≠ .sp) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.strSimd .S32 vt
      (if unscaled then .UnscaledOffset ptrReg (BitVec.ofNat 64 off) else .Offset ptrReg (BitVec.ofNat 64 off))))
    (hea : s.readReg64 ptrReg = ea) (hv : (s.readVReg128 vt).extractLsb' 0 32 = v)
    (hstore : SepStore32 (ea + BitVec.ofNat 64 off) v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_strSimd32 (wb := none) hpc hrun hfetch
    (by cases unscaled <;> cases ptrReg <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned])
    (by cases unscaled <;> simp [evalAddrMode, hea]) hv hstore (by simp [applyWriteback, hpc']) hnext

private theorem step_strH16_off {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff off : Nat) (vt : BitVec 5) (ptrReg : Reg) (v : BitVec 16)
    (hptr : ptrReg ≠ .sp) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .H16 vt (.Offset ptrReg (BitVec.ofNat 64 off))))
    (hea : s.readReg64 ptrReg = ea) (hv : (s.readVReg128 vt).truncate 16 = v)
    (hstore : SepStore16 (ea + BitVec.ofNat 64 off) v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hsp : checkAddrSPAligned s (.Offset ptrReg (BitVec.ofNat 64 off)) = true := by
    cases ptrReg <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned]
  exact step_strSimd16 (wb := none) hpc hrun hfetch hsp (by simp [evalAddrMode, hea]) hv hstore
    (by simp [applyWriteback, hpc']) hnext

private theorem reencode_prefix_append_chunk (dst : BitVec 64) (bs : List (BitVec 8)) (k : Nat) :
    (dst ↦ₛ reencodePolyPrefix bs k) ∗
      ((dst + BitVec.ofNat 64 (24 * k)) ↦ₛ reencodeChunk24 bs k) =
      (dst ↦ₛ reencodePolyPrefix bs (k + 1)) := by
  rw [reencodePolyPrefix_succ, pointsToBytes_append, reencodePolyPrefix_length]

theorem step_ser12_tail14 {prog : Program} {target_pc dst : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 k : Nat) (ptrReg : Reg) (hk16 : k < 16) (hptr : ptrReg ≠ .sp)
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hea : s.readReg64 ptrReg = dst + BitVec.ofNat 64 (24 * k))
    (hv1 : s.readVReg128 1#5 = neonSerialize12Mix (deserVec8h bs (24 * k)))
    (hv3 : s.readVReg128 3#5 = neonSerialize12Mix (deserVec8h bs (24 * k + 12)))
    (hf0  : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdExt true 1#5 8#4 1#5 2#5))
    (hf1  : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdDupScalar 0b01010#5 1#5 4#5))
    (hf2  : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.strSimd .S32 1#5 (.Offset ptrReg 0#64)))
    (hf3  : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdExt true 3#5 8#4 3#5 5#5))
    (hf4  : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdDupScalar 0b01010#5 3#5 1#5))
    (hf5  : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.strSimd .S32 3#5 (.Offset ptrReg 12#64)))
    (hf6  : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdDupScalar 0b01010#5 2#5 3#5))
    (hf7  : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.strSimd .S32 2#5 (.UnscaledOffset ptrReg 6#64)))
    (hf8  : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some (.simdDupScalar 0b01010#5 5#5 2#5))
    (hf9  : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.strSimd .H16 4#5 (.Offset ptrReg 4#64)))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.strSimd .H16 1#5 (.Offset ptrReg 16#64)))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.strSimd .S32 5#5 (.UnscaledOffset ptrReg 18#64)))
    (hf12 : prog.fetch (b + BitVec.ofNat 64 (p0 + 48)) = some (.strSimd .H16 3#5 (.Offset ptrReg 10#64)))
    (hf13 : prog.fetch (b + BitVec.ofNat 64 (p0 + 52)) = some (.strSimd .H16 2#5 (.Offset ptrReg 22#64)))
    (hnext : ∀ s' : State,
      s'.pc = b + BitVec.ofNat 64 (p0 + 56) →
      s'.status = .Running →
      s'.sp = s.sp →
      (∀ r : Reg, s'.readReg64 r = s.readReg64 r) →
      s'.pstate = s.pstate →
      s'.readVReg128 0#5 = s.readVReg128 0#5 →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP prog target_pc s'
        ((dst ↦ₛ reencodePolyPrefix bs (k + 1)) ∗
          memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) post) :
    SepWP prog target_pc s
      ((dst ↦ₛ reencodePolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F) post := by
  let ea := dst + BitVec.ofNat 64 (24 * k)
  let m0 := neonSerialize12Mix (deserVec8h bs (24 * k))
  let m1 := neonSerialize12Mix (deserVec8h bs (24 * k + 12))
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
    (show (dst ↦ₛ reencodePolyPrefix bs k) ∗ memRegion ea (384 - 24 * k) ∗ F ⊢
      memRegion ea 24 ∗ ((dst ↦ₛ reencodePolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region24; intro w0 u1 w2 u3 w4 u5 w6 u7
  refine step_vreg1 b p0 (p0 + 4) 2#5 e0 hpc hrun hf0
    (by rw [exec_simdExt_16b_8]; simp [hv1, e0, m0]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 4#5 ((lane16 m0 2).zeroExtend 128) rfl (by simp [hrun]) hf1
    (by rw [exec_simdDupScalar_h2]; simp [hv1, m0]) (by omega) ?_
  refine step_strS32_off b ea (p0 + 8) (p0 + 12) 0 false 1#5 ptrReg ((lane64 m0 0).truncate 32)
    hptr rfl (by simp [hrun]) hf2 (by simp [hea, ea]) (by simp [hv1, m0, low32_eq_lane64_0])
    (SepStore32.left (SepStore32.here (by dsimp only [ea]; clear * -; bv_omega))) (by omega) ?_; intro mem1
  refine step_vreg1 b (p0 + 12) (p0 + 16) 5#5 e1 rfl (by simp [hrun]) hf3
    (by rw [exec_simdExt_16b_8]; simp [hv3, e1, m1]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 1#5 ((lane16 m1 2).zeroExtend 128) rfl (by simp [hrun]) hf4
    (by rw [exec_simdDupScalar_h2]; simp [hv3, m1]) (by omega) ?_
  refine step_strS32_off b ea (p0 + 20) (p0 + 24) 12 false 3#5 ptrReg ((lane64 m1 0).truncate 32)
    hptr rfl (by simp [hrun]) hf5 (by simp [hea, ea]) (by simp [hv3, m1, low32_eq_lane64_0])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))
    (by omega) ?_; intro mem2
  refine step_vreg1 b (p0 + 24) (p0 + 28) 3#5 ((lane16 (simdExt16b m0 m0 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf6 (by rw [exec_simdDupScalar_h2]; simp [e0, ext8_self_lane16_2]) (by omega) ?_
  refine step_strS32_off b ea (p0 + 28) (p0 + 32) 6 true 2#5 ptrReg ((lane64 (simdExt16b m0 m0 8) 0).truncate 32)
    hptr rfl (by simp [hrun]) hf7 (by simp [hea, ea]) (by simp [e0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl)))) (by omega) ?_; intro mem3
  refine step_vreg1 b (p0 + 32) (p0 + 36) 2#5 ((lane16 (simdExt16b m1 m1 8) 2).zeroExtend 128)
    rfl (by simp [hrun]) hf8 (by rw [exec_simdDupScalar_h2]; simp [e1, ext8_self_lane16_2]) (by omega) ?_
  refine step_strH16_off b ea (p0 + 36) (p0 + 40) 4 4#5 ptrReg (lane16 m0 2)
    hptr rfl (by simp [hrun]) hf9 (by simp [hea, ea]) (by simp)
    (SepStore16.right (SepStore16.left (SepStore16.here rfl))) (by omega) ?_; intro mem4
  refine step_strH16_off b ea (p0 + 40) (p0 + 44) 16 1#5 ptrReg (lane16 m1 2)
    hptr rfl (by simp [hrun]) hf10 (by simp [hea, ea]) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))
    (by omega) ?_; intro mem5
  refine step_strS32_off b ea (p0 + 44) (p0 + 48) 18 true 5#5 ptrReg ((lane64 (simdExt16b m1 m1 8) 0).truncate 32)
    hptr rfl (by simp [hrun]) hf11 (by simp [hea, ea]) (by simp [e1, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here rfl))))))))
    (by omega) ?_; intro mem6
  refine step_strH16_off b ea (p0 + 48) (p0 + 52) 10 3#5 ptrReg (lane16 (simdExt16b m0 m0 8) 2)
    hptr rfl (by simp [hrun]) hf12 (by simp [hea, ea]) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))
    (by omega) ?_; intro mem7
  refine step_strH16_off b ea (p0 + 52) (p0 + 56) 22 2#5 ptrReg (lane16 (simdExt16b m1 m1 8) 2)
    hptr rfl (by simp [hrun]) hf13 (by simp [hea, ea]) (by simp)
    (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.right (SepStore16.left (SepStore16.here rfl)))))))))
    (by omega) ?_; intro mem8
  refine SepWP.weaken_pre (P' := (dst ↦ₛ reencodePolyPrefix bs (k + 1)) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * (k + 1))) (384 - 24 * (k + 1)) ∗ F) ?_ ?_
  · have hc := cells24_eq_reencodeChunk24 ea bs k
    have hp := reencode_prefix_append_chunk dst bs k
    dsimp only [m0, m1] at hc ⊢; rw [← hp, ← hc]; sep_frame
  · refine hnext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · simp [hrun]
    · simp
    · intro r; simp
    · simp
    · simp
    · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, csv1, csv2, csv3, csv4, csv5]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Step
