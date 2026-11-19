/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps

/-!
# `validate_pk_bytes` (`B21`) — Segment 2 AdvSIMD Bridges & Step Helpers

AdvSIMD `{svc}`-polymorphic `execInstWithSvc` bridges, `O(1)` dead-store `memRegion` wrappers,
reversible `pointsToBytes` chunking helpers, and the reusable 12-instruction `deserialize_12` step.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 lane16_dup8x16 lane16_mapLanes_8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmhs8h simdTbl16b simdUshl8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  entails_sub sepWP_elim_region32
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  deserChunk32 deserVec8h exec_simdAdd_8h exec_simdCmhs_8h exec_simdTbl_16b_1 exec_simdUshl_8h
  loadVec12 neonDeser12 neonDeser12_loadVec12 reducedPolyPrefix reducedPolyPrefix_length
  reducedPolyPrefix_succ step_stpQ128_region step_strQ128_region vec128Bytes vec128Bytes_length
)

/-! ## 1. AdvSIMD `{svc}`-Polymorphic `execInstWithSvc` Bridges -/

private theorem writeV_adv_congr {rd : BitVec 5} {v1 v2 : BitVec 128} {s : State} (h : v1 = v2) :
    (s.writeVReg128 rd v1).advancePC = (s.writeVReg128 rd v2).advancePC :=
  h ▸ rfl

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdTbl_16b_1_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTbl true rm 0#2 false rn rd) s =
      (s.writeVReg128 rd (simdTbl16b (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdTbl_16b_1 rm rn rd s

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdUshl_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdUshl_8h rm rn rd s

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdCmhs_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b00111#5 rn rd) s =
      (s.writeVReg128 rd (simdCmhs8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdCmhs_8h rm rn rd s

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdAdd_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdAdd_8h rm rn rd s

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by
  simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdMvni_4s_msl16_3 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11010#5 3#5 rd) s =
      (s.writeVReg128 rd 0xfffc0000fffc0000fffc0000fffc0000#128).advancePC := by
  simp [execInstWithSvc, applySimdResult, evalSimdModImmExt, advSimdExpandImm]

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdBic_8h_f0_lsl8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 7#3 0b10110#5 16#5 rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rd) &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128)).advancePC := by
  simp [execInstWithSvc, applySimdResult, evalSimdModImmExt, advSimdExpandImm]

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdBic_8h_13_lsl8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rd) &&& 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128)).advancePC := by
  simp [execInstWithSvc, applySimdResult, evalSimdModImmExt, advSimdExpandImm]

private theorem mask_getLsbD_16_128 :
    ∀ k : Fin 128, (65535#128).getLsbD k.val = decide (k.val < 16) := by
  decide +kernel

private theorem zext64_and_ffff_eq (w : BitVec 64) :
    (w.zeroExtend 128) &&& (1#128 <<< 16 - 1#128) = (w.truncate 16).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hm := mask_getLsbD_16_128 ⟨k, hk⟩
  dsimp only at hm
  simp only [show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    hm, hk, decide_true, Bool.true_and, Bool.and_comm]

@[simp, arm64_norm, wp_norm ↓]
theorem exec_simdDup_8h_gpr {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc] at hz ⊢
  rw [hz]
  refine writeV_adv_congr ?_
  apply ext_lane16
  intro i
  rw [lane16_mapLanes_8, lane16_dup8x16]
  simp

theorem dup8x16_3329 :
    dup8x16 ((3329#64 : BitVec 64).truncate 16) = 0x0d010d010d010d010d010d010d010d01#128 := by
  decide

/-! ## 2. Spatial Split/Join Lemmas & `O(1)` Dead-Store Wrappers -/

theorem pk_pointsToBytes_split4 (sp : BitVec 64) (hdr ek : List (BitVec 8))
    (hek : ek.length = 1152) :
    ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) =
      ((sp + 16#64) ↦ₛ ek.take 384) ∗
      ((sp + 400#64) ↦ₛ (ek.drop 384).take 384) ∗
      ((sp + 784#64) ↦ₛ (ek.drop 768).take 384) ∗
      ((sp + 1168#64) ↦ₛ hdr.take 32) := by
  have hek_split : ek = ek.take 384 ++ ((ek.drop 384).take 384 ++ (ek.drop 768).take 384) := by
    have h1 := (List.take_append_drop 384 ek).symm
    have h2 := (List.take_append_drop 384 (ek.drop 384)).symm
    rw [List.drop_drop] at h2
    have h3 : (ek.drop 768).take 384 = ek.drop 768 :=
      List.take_of_length_le (by simp [hek])
    rw [h3]
    exact h1.trans (congrArg (ek.take 384 ++ ·) h2)
  have hl0 : (ek.take 384).length = 384 := by simp [hek]
  have hl1 : ((ek.drop 384).take 384).length = 384 := by simp [hek]
  have hl2 : ((ek.drop 768).take 384).length = 384 := by simp [hek]
  have ha1 : sp + 16#64 + 384#64 = sp + 400#64 := by bv_omega
  have ha2 : sp + 400#64 + 384#64 = sp + 784#64 := by bv_omega
  have ha3 : sp + 784#64 + 384#64 = sp + 1168#64 := by bv_omega
  conv_lhs => rw [hek_split]
  simp only [List.append_assoc, pointsToBytes_append, hl0, hl1, hl2, ha1, ha2, ha3]

theorem cells16_eq_vec128Bytes (a : BitVec 64) (v : BitVec 128) :
    (a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v.extractLsb' 64 64) =
      (a ↦ₛ vec128Bytes v) := by
  rw [vec128Bytes, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

theorem cells32_eq_deserChunk32 (a : BitVec 64) (bs : List (BitVec 8)) (k : Nat) :
    let v2 := deserVec8h bs (24 * k)
    let v3 := deserVec8h bs (24 * k + 12)
    (a ↦₆₄ v2.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v2.extractLsb' 64 64) ∗
      ((a + 16#64) ↦₆₄ v3.extractLsb' 0 64) ∗ ((a + 24#64) ↦₆₄ v3.extractLsb' 64 64) =
      (a ↦ₛ deserChunk32 bs k) := by
  dsimp only
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [deserChunk32, pointsToBytes_append, vec128Bytes_length,
    ← cells16_eq_vec128Bytes a, ← cells16_eq_vec128Bytes (a + 16#64), h24]
  simp only [sepConj_assoc]

theorem prefix_append_chunk (dst : BitVec 64) (bs : List (BitVec 8)) (k : Nat) :
    (dst ↦ₛ reducedPolyPrefix bs k) ∗
      ((dst + BitVec.ofNat 64 (32 * k)) ↦ₛ deserChunk32 bs k) =
      (dst ↦ₛ reducedPolyPrefix bs (k + 1)) := by
  rw [reducedPolyPrefix_succ, pointsToBytes_append, reducedPolyPrefix_length]

theorem step_dead_strQ {prog : Program} {b target_pc : BitVec 64}
    {s : State} {m : Memory} {Rest : SepProp} {post : State → SepProp → Prop}
    (baseOff total pcOff nextOff spImm regOff : Nat) (vt : BitVec 5)
    (hrun : s.status = .Running) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 spImm))))
    (hnextOff : pcOff + 4 = nextOff)
    (hreg : baseOff + regOff = spImm)
    (hbounds : regOff + 16 ≤ total)
    (htotal : total ≤ 2 ^ 64)
    (hcont : ∀ m' : Memory,
      SepWP prog target_pc
        ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        (memRegion (s.sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post) :
    SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (memRegion (s.sp + BitVec.ofNat 64 baseOff) total ∗ Rest) post := by
  have hea : (s.sp + BitVec.ofNat 64 baseOff) + BitVec.ofNat 64 regOff =
      s.sp + BitVec.ofNat 64 spImm := by
    subst hreg; bv_omega
  have hpc_next : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine step_strQ128_region (pc := b + BitVec.ofNat 64 pcOff)
    rfl hrun hfetch hspA rfl hbounds htotal hea fun m' => ?_
  rw [hpc_next]
  exact hcont m'

theorem step_dead_stpQ {prog : Program} {b target_pc base : BitVec 64}
    {s : State} {m : Memory} {Rest : SepProp} {post : State → SepProp → Prop}
    (total pcOff nextOff off : Nat) (vt1 vt2 : BitVec 5)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = base)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.stpSimd .Q128 vt1 vt2 (.Offset .x21 (BitVec.ofNat 64 off))))
    (hnextOff : pcOff + 4 = nextOff)
    (hbounds : off + 32 ≤ total)
    (htotal : total ≤ 2 ^ 64)
    (hcont : ∀ m' : Memory,
      SepWP prog target_pc
        ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        (memRegion base total ∗ Rest) post) :
    SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (memRegion base total ∗ Rest) post := by
  have haddr : evalAddrMode ((s.setPC (b + BitVec.ofNat 64 pcOff)).setMem m)
      (.Offset .x21 (BitVec.ofNat 64 off)) = (base + BitVec.ofNat 64 off, none) := by
    simp [evalAddrMode, hx21]
  have hpc_next : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine step_stpQ128_region (pc := b + BitVec.ofNat 64 pcOff)
    rfl hrun hfetch rfl haddr hbounds htotal rfl fun m' => ?_
  rw [hpc_next]
  exact hcont m'

/-! ## 3. Opaque 12-Byte Load Wrappers & Shared `deserChunk32` Store Step -/

def rawLo64 (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
    (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
    (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)

def rawHi32 (bs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
    (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)

theorem neonDeser12_raw (bs : List (BitVec 8)) (off : Nat) :
    neonDeser12 (setSimdLane ((rawLo64 bs off).zeroExtend 128) 32 2
      ((rawHi32 bs off).zeroExtend 128)) = deserVec8h bs off := by
  simpa only [rawLo64, rawHi32, loadVec12] using neonDeser12_loadVec12 bs off

theorem step_ldrD64_raw {prog : Program} {target_pc base : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (vt : BitVec 5) (addr : AddrMode) (off : Nat)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (base + BitVec.ofNat 64 off, none))
    (hoff : off + 8 ≤ bs.length) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt ((rawLo64 bs off).zeroExtend 128)).setPC (b + BitVec.ofNat 64 nextOff))
      ((base ↦ₛ bs) ∗ F) post) :
    SepWP prog target_pc s ((base ↦ₛ bs) ∗ F) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hload : SepLoad64 (base + BitVec.ofNat 64 off) ((base ↦ₛ bs) ∗ F) (rawLo64 bs off) := by
    simpa only [rawLo64] using (SepLoad64.of_pointsToBytes (off := off) rfl hoff rfl :
      SepLoad64 (base + BitVec.ofNat 64 off) ((base ↦ₛ bs) ∗ F) _)
  exact SepWP.step_ldrSimd64 hpc hrun hfetch hsp haddr hload (by simp [applyWriteback, hpc']) hnext

theorem step_ld1S2_raw {prog : Program} {target_pc base : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rn : Reg) (vt : BitVec 5) (off : Nat)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.simdLdSt1Single true true false 0#5 0x4#3 false 0x0#2 rn vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = base + BitVec.ofNat 64 (off + 8))
    (hoff : off + 12 ≤ bs.length) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (setSimdLane (s.readVReg128 vt) 32 2
        ((rawHi32 bs off).zeroExtend 128))).setPC (b + BitVec.ofNat 64 nextOff))
      ((base ↦ₛ bs) ∗ F) post) :
    SepWP prog target_pc s ((base ↦ₛ bs) ∗ F) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hload : SepLoad32 (base + BitVec.ofNat 64 (off + 8)) ((base ↦ₛ bs) ∗ F) (rawHi32 bs off) := by
    simpa only [rawHi32, Nat.add_assoc] using (SepLoad32.of_pointsToBytes (off := off + 8) rfl (by omega) rfl :
      SepLoad32 (base + BitVec.ofNat 64 (off + 8)) ((base ↦ₛ bs) ∗ F) _)
  exact step_simdLd1Single32 hpc hrun hfetch hsp hea hload (by simp [simdLdSt1SingleLaneIdx, hpc']) hnext

theorem step_stp_deserChunk {prog : Program} {target_pc src dst : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff k : Nat) (addr : AddrMode) (hk16 : k < 16)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.stpSimd .Q128 2#5 3#5 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (dst + BitVec.ofNat 64 (32 * k), none))
    (hv2 : s.readVReg128 2#5 = deserVec8h bs (24 * k))
    (hv3 : s.readVReg128 3#5 = deserVec8h bs (24 * k + 12))
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
        ((src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs (k + 1)) ∗
          memRegion (dst + BitVec.ofNat 64 (32 * (k + 1))) (512 - 32 * (k + 1)) ∗ F) post) :
    SepWP prog target_pc s
      ((src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) ∗ F) post := by
  have hsplit : memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) =
      memRegion (dst + BitVec.ofNat 64 (32 * k)) 32 ∗
        memRegion (dst + BitVec.ofNat 64 (32 * (k + 1))) (512 - 32 * (k + 1)) := by
    have hm := memRegion_split (dst + BitVec.ofNat 64 (32 * k)) 32 (512 - 32 * (k + 1)) (by omega)
    have ha : dst + BitVec.ofNat 64 (32 * k) + BitVec.ofNat 64 32 =
        dst + BitVec.ofNat 64 (32 * (k + 1)) := by clear * -; bv_omega
    rw [show 32 + (512 - 32 * (k + 1)) = 512 - 32 * k by omega, ha] at hm
    exact hm
  refine SepWP.weaken_pre
    (show (src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) ∗ F ⊢
      memRegion (dst + BitVec.ofNat 64 (32 * k)) 32 ∗
        ((src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
          memRegion (dst + BitVec.ofNat 64 (32 * (k + 1))) (512 - 32 * (k + 1)) ∗ F) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region32
  intro w0 w1 w2 w3
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  refine SepWP.step_stpSimd128 (s' := s.setPC (b + BitVec.ofNat 64 nextOff))
    (pc := b + BitVec.ofNat 64 pcOff) (vt1 := 2#5) (vt2 := 3#5)
    (addr := addr) (ea := dst + BitVec.ofNat 64 (32 * k))
    (v1 := (deserVec8h bs (24 * k)).extractLsb' 0 64)
    (v2 := (deserVec8h bs (24 * k)).extractLsb' 64 64)
    (v3 := (deserVec8h bs (24 * k + 12)).extractLsb' 0 64)
    (v4 := (deserVec8h bs (24 * k + 12)).extractLsb' 64 64)
    hpc hrun hfetch hsp haddr rfl rfl (by clear * -; bv_omega)
    (by rw [hv2]) (by rw [hv2]) (by rw [hv3]) (by rw [hv3])
    (SepStore64.left (SepStore64.here rfl))
    (SepStore64.right (SepStore64.left (SepStore64.here rfl)))
    (SepStore64.right (SepStore64.right (SepStore64.left (SepStore64.here rfl))))
    (SepStore64.right (SepStore64.right (SepStore64.right (SepStore64.left (SepStore64.here rfl)))))
    (by simp [applyWriteback, hpc']) ?_
  intro m'
  refine SepWP.weaken_pre ?_ (hnext m')
  have hc := cells32_eq_deserChunk32 (dst + BitVec.ofNat 64 (32 * k)) bs k
  have hp := prefix_append_chunk dst bs k
  dsimp only at hc
  rw [← hp, ← hc]; sep_frame

/-! ## 4. Reusable 12-Instruction `deserialize_12` AdvSIMD Block -/

def deserTmp4 (v : BitVec 128) : BitVec 128 :=
  let t := simdTbl16b v 0x0b0a0a09080707060504040302010100#128
  let u := simdUshl8h t 0xfffc0000fffc0000fffc0000fffc0000#128
  let m := u &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128
  simdCmhs8h m 0x0d010d010d010d010d010d010d010d01#128 &&&
    0xf2fff2fff2fff2fff2fff2fff2fff2ff#128

theorem step_vreg1 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rd : BitVec 5) (val : BitVec 128) {inst : Instr}
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some inst)
    (hexec : execInstWithSvc (evalSvc prog.svc) inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).writeVReg128 rd val).advancePC)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 rd val).setPC (b + BitVec.ofNat 64 nextOff)) P post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hev : prog.evalInst inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      (s.writeVReg128 rd val).setPC (b + BitVec.ofNat 64 nextOff) := by
    unfold Program.evalInst; rw [hexec]; cases s; simp [State.setPC, State.writeVReg128, State.advancePC, hpc']
  exact SepWP.step_pure hpc hrun hfetch hev (by simp) hnext

theorem step_deser12_simd12 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 : Nat) (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hv0 : s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128)
    (hv1 : s.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128)
    (hv6 : s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128)
    (hf0 : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdTbl true 6#5 0#2 false 2#5 2#5))
    (hf1 : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdTbl true 6#5 0#2 false 3#5 3#5))
    (hf2 : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.simdThreeSame true true 0b01#2 0#5 0b01000#5 2#5 2#5))
    (hf3 : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdThreeSame true true 0b01#2 0#5 0b01000#5 3#5 3#5))
    (hf4 : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdImmShift true true 0#4 7#3 0b10110#5 16#5 2#5))
    (hf5 : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.simdImmShift true true 0#4 7#3 0b10110#5 16#5 3#5))
    (hf6 : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdThreeSame true true 0b01#2 1#5 0b00111#5 2#5 4#5))
    (hf7 : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.simdThreeSame true true 0b01#2 1#5 0b00111#5 3#5 5#5))
    (hf8 : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 4#5))
    (hf9 : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 5#5))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.simdThreeSame true false 0b01#2 2#5 0b10000#5 4#5 2#5))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.simdThreeSame true false 0b01#2 3#5 0b10000#5 5#5 3#5))
    (hnext : SepWP prog target_pc
      (((((s.writeVReg128 4#5 (deserTmp4 (s.readVReg128 2#5))).writeVReg128 5#5
          (deserTmp4 (s.readVReg128 3#5))).writeVReg128 2#5
          (neonDeser12 (s.readVReg128 2#5))).writeVReg128 3#5
          (neonDeser12 (s.readVReg128 3#5))).setPC (b + BitVec.ofNat 64 (p0 + 48))) P post) :
    SepWP prog target_pc s P post := by
  let v2 := s.readVReg128 2#5
  let v3 := s.readVReg128 3#5
  let t2 := simdTbl16b v2 0x0b0a0a09080707060504040302010100#128
  let t3 := simdTbl16b v3 0x0b0a0a09080707060504040302010100#128
  let u2 := simdUshl8h t2 0xfffc0000fffc0000fffc0000fffc0000#128
  let u3 := simdUshl8h t3 0xfffc0000fffc0000fffc0000fffc0000#128
  let m2 := u2 &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128
  let m3 := u3 &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128
  let c2 := simdCmhs8h m2 0x0d010d010d010d010d010d010d010d01#128
  let c3 := simdCmhs8h m3 0x0d010d010d010d010d010d010d010d01#128
  refine step_vreg1 b p0 (p0 + 4) 2#5 t2 hpc hrun hf0
    (by rw [exec_simdTbl_16b_1_svc]; simp [hv6, t2, v2]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 3#5 t3 rfl (by simp [hrun]) hf1
    (by rw [exec_simdTbl_16b_1_svc]; simp [hv6, t3, v3]) (by omega) ?_
  refine step_vreg1 b (p0 + 8) (p0 + 12) 2#5 u2 rfl (by simp [hrun]) hf2
    (by rw [exec_simdUshl_8h_svc]; simp [hv0, u2]) (by omega) ?_
  refine step_vreg1 b (p0 + 12) (p0 + 16) 3#5 u3 rfl (by simp [hrun]) hf3
    (by rw [exec_simdUshl_8h_svc]; simp [hv0, u3]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 2#5 m2 rfl (by simp [hrun]) hf4
    (by rw [exec_simdBic_8h_f0_lsl8]; simp [m2]) (by omega) ?_
  refine step_vreg1 b (p0 + 20) (p0 + 24) 3#5 m3 rfl (by simp [hrun]) hf5
    (by rw [exec_simdBic_8h_f0_lsl8]; simp [m3]) (by omega) ?_
  refine step_vreg1 b (p0 + 24) (p0 + 28) 4#5 c2 rfl (by simp [hrun]) hf6
    (by rw [exec_simdCmhs_8h_svc]; simp [hv1, c2]) (by omega) ?_
  refine step_vreg1 b (p0 + 28) (p0 + 32) 5#5 c3 rfl (by simp [hrun]) hf7
    (by rw [exec_simdCmhs_8h_svc]; simp [hv1, c3]) (by omega) ?_
  refine step_vreg1 b (p0 + 32) (p0 + 36) 4#5 (deserTmp4 v2) rfl (by simp [hrun]) hf8
    (by rw [exec_simdBic_8h_13_lsl8]; simp [deserTmp4, c2, m2, u2, t2]) (by omega) ?_
  refine step_vreg1 b (p0 + 36) (p0 + 40) 5#5 (deserTmp4 v3) rfl (by simp [hrun]) hf9
    (by rw [exec_simdBic_8h_13_lsl8]; simp [deserTmp4, c3, m3, u3, t3]) (by omega) ?_
  refine step_vreg1 b (p0 + 40) (p0 + 44) 2#5 (neonDeser12 v2) rfl (by simp [hrun]) hf10
    (by rw [exec_simdAdd_8h_svc]; simp [neonDeser12, deserTmp4, c2, m2, u2, t2]) (by omega) ?_
  refine step_vreg1 b (p0 + 44) (p0 + 48) 3#5 (neonDeser12 v3) rfl (by simp [hrun]) hf11
    (by rw [exec_simdAdd_8h_svc]; simp [neonDeser12, deserTmp4, c3, m3, u3, t3]) (by omega) ?_
  refine SepWP.congr_state ?_ hnext
  dsimp only [v2, v3]
  cases s; simp only [State.writeVReg128, State.setPC, VRegFile.write]
  congr 1; congr 1; funext r
  by_cases h3 : r = 3#5; · subst h3; rfl
  by_cases h2 : r = 2#5; · subst h2; rfl
  by_cases h5 : r = 5#5; · subst h5; rfl
  by_cases h4 : r = 4#5; · subst h4; rfl
  simp [h3, h2, h5, h4]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop
