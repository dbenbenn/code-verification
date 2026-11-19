/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Permission-Preserving 32-Bit / SIMD Store Rules & Block Cell Layouts (`CbcDec.StoreRules`)
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules

open Arm64 ProofLib SepProp ProofLib.SepLogic
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon

theorem sepWP_weaken_pre {P : Program} {pc : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P1 ⊢ P2) (hw : SepWP P pc s P2 post oom) :
    SepWP P pc s P1 post oom :=
  SepWP.of_reaches_pc fun _ hm => hw.to_reaches_pc (Satisfies.mono (sepConj_mono_left h) hm)

/-! ## 1. Permission-Preserving Store Lemmas & Scoped Macros -/

theorem step_str32_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 32}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.str .W32 rt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write32 s.mem ea val)) hm'

theorem step_stp32_perm {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {v1 v2 : BitVec 32}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 4#64 = ea2)
    (hv1 : s.readReg32 rt1 = v1) (hv2 : s.readReg32 rt2 = v2)
    (hstore1 : SepStore32 ea v1 P P1) (hstore2 : SepStore32 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  have htrunc1 : (s.readReg64 rt1).truncate 32 = v1 := hv1
  have htrunc2 : (s.readReg64 rt2).truncate 32 = v2 := hv2
  let m1 := s.mem.write32 ea v1; let m2 := m1.write32 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 4 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 4 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write32 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, htrunc1, htrunc2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write32 m1 ea2 v2).trans (Memory.perm_write32 s.mem ea v1))) hm2

theorem step_strSimd128_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hcan16 : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

theorem step_stpSimd128_perm {prog : Program}
    {target_pc pc ea ea2 ea3 ea4 v1 v2 v3 v4 : BitVec 64}
    {s s' : State} {P P1 P2 P3 P4 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4)
    (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt1).extractLsb' 64 64 = v2)
    (hv3 : (s.readVReg128 vt2).extractLsb' 0 64 = v3)
    (hv4 : (s.readVReg128 vt2).extractLsb' 64 64 = v4)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hstore3 : SepStore64 ea3 v3 P2 P3) (hstore4 : SepStore64 ea4 v4 P3 P4)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P4 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  let m3 := m2.write64 ea3 v3; let m4 := m3.write64 ea4 v4
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := hstore3.store hm2; have hm4 : m4 ⊨ P4 ∗ R := hstore4.store hm3
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hcan3 : m2.canWrite ea3 8 = true := hstore3.writable hm2
  have hcan4 : m3.canWrite ea4 8 = true := hstore4.writable hm3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan4
  have hcan_lo : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canWrite ea3 16 = true :=
    Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s = s'.setMem m4 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hea3, hea4, hv1, hv2, hv3, hv4, hcan_lo, hcan_hi,
      SimdMemSize.bytes, hpc, m1, m2, m3, m4]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m4 ((Memory.perm_write64 m3 ea4 v4).trans
      ((Memory.perm_write64 m2 ea3 v3).trans
        ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))))) hm4

namespace Macros

scoped macro "wp_str32 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str32_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_stp32 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp32_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_str128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_strSimd128_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_stp128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stpSimd128_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

end Macros

namespace Simp

@[scoped simp, scoped wp_norm]
theorem extractLsb'_0_64_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[scoped simp, scoped wp_norm]
theorem extractLsb'_64_64_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

end Simp

/-! ## 2. 16-Byte, 64-Byte & 56-Byte Spill Cell Decompositions -/

abbrev pack8LE (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

@[expose] def bytes16At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
  ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
  ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15)

theorem pointsToBytes16_eq_bytes16At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      bytes16At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  unfold bytes16At
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes16_eq_pts64_pair (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      ((a ↦₆₄ pack8LE b0 b1 b2 b3 b4 b5 b6 b7) ∗
       ((a + 8#64) ↦₆₄ pack8LE b8 b9 b10 b11 b12 b13 b14 b15)) := by
  rw [show [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
        [b0, b1, b2, b3, b4, b5, b6, b7] ++ [b8, b9, b10, b11, b12, b13, b14, b15] from rfl,
      pointsToBytes_append,
      show ([b0, b1, b2, b3, b4, b5, b6, b7] : List (BitVec 8)).length = 8 from rfl,
      pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64]

theorem pts64_pair_eq_bytes16At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    ((a ↦₆₄ pack8LE b0 b1 b2 b3 b4 b5 b6 b7) ∗
     ((a + 8#64) ↦₆₄ pack8LE b8 b9 b10 b11 b12 b13 b14 b15)) =
      bytes16At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 :=
  (pointsToBytes16_eq_pts64_pair a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15).symm.trans
    (pointsToBytes16_eq_bytes16At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15)

theorem pts64_pair_off_eq_bytes16At (ptr off1 off2 : BitVec 64)
    (hoff : ptr + off1 + 8#64 = ptr + off2)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) (R : SepProp) :
    (((ptr + off1) ↦₆₄ pack8LE b0 b1 b2 b3 b4 b5 b6 b7) ∗
     ((ptr + off2) ↦₆₄ pack8LE b8 b9 b10 b11 b12 b13 b14 b15) ∗ R) =
      (bytes16At (ptr + off1) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 ∗ R) := by
  rw [← hoff, ← sepConj_assoc, pts64_pair_eq_bytes16At]

theorem exists_bytes16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8,
      bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩

@[expose] def pts64x8At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)

theorem pts64_entails_memRegion8 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ memRegion a 8 :=
  Entails.trans (Entails.of_eq (pointsTo64_eq_pointsToBytes a w))
    (by simpa only [unpack64_length] using pointsToBytes_entails_memRegion a (unpack64 w))

theorem pts64x8At_entails_memRegion64 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    pts64x8At a w0 w1 w2 w3 w4 w5 w6 w7 ⊢ memRegion a 64 := by
  rw [show (64 : Nat) = 8 + 56 from rfl, memRegion_split a 8 56 (by decide),
      show (56 : Nat) = 8 + 48 from rfl, memRegion_split _ 8 48 (by decide),
      show (48 : Nat) = 8 + 40 from rfl, memRegion_split _ 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split _ 8 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split _ 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split _ 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split _ 8 8 (by decide)]
  unfold pts64x8At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pts64_entails_memRegion8 _ _)
    (sepConj_mono (pts64_entails_memRegion8 _ _)
      (sepConj_mono (pts64_entails_memRegion8 _ _)
        (sepConj_mono (pts64_entails_memRegion8 _ _)
          (sepConj_mono (pts64_entails_memRegion8 _ _)
            (sepConj_mono (pts64_entails_memRegion8 _ _)
              (sepConj_mono (pts64_entails_memRegion8 _ _)
                (pts64_entails_memRegion8 _ _)))))))

theorem sepWP_memRegion8_elim {P : Program} {target_pc a : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ w : BitVec 64, SepWP P target_pc s ((a ↦₆₄ w) ∗ Rest) post oom) :
    SepWP P target_pc s (memRegion a 8 ∗ Rest) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  rw [memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨w, hm⟩
  exact SepWP.to_reaches_pc (h w) hm

theorem sepWP_memRegion64_pts64x8_elim {P : Program} {target_pc a : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      SepWP P target_pc s (pts64x8At a w0 w1 w2 w3 w4 w5 w6 w7 ∗ Rest) post oom) :
    SepWP P target_pc s (memRegion a 64 ∗ Rest) post oom := by
  rw [show (64 : Nat) = 8 + 56 from rfl, memRegion_split a 8 56 (by decide),
      show (56 : Nat) = 8 + 48 from rfl, memRegion_split _ 8 48 (by decide),
      show (48 : Nat) = 8 + 40 from rfl, memRegion_split _ 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split _ 8 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split _ 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split _ 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split _ 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWP_memRegion8_elim fun w0 => ?_
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 8#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w1 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 16#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w2 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 24#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w3 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 32#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w4 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 40#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w5 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 48#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w6 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 56#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_elim fun w7 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (by unfold pts64x8At; sep_ac_rfl)) (h w0 w1 w2 w3 w4 w5 w6 w7)

@[expose] def spill14At (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 32) : SepProp :=
  (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1) ∗ ((a + 8#64) ↦₃₂ v2) ∗ ((a + 12#64) ↦₃₂ v3) ∗
  ((a + 16#64) ↦₃₂ v4) ∗ ((a + 20#64) ↦₃₂ v5) ∗ ((a + 24#64) ↦₃₂ v6) ∗ ((a + 28#64) ↦₃₂ v7) ∗
  ((a + 32#64) ↦₃₂ v8) ∗ ((a + 36#64) ↦₃₂ v9) ∗ ((a + 40#64) ↦₃₂ v10) ∗ ((a + 44#64) ↦₃₂ v11) ∗
  ((a + 48#64) ↦₃₂ v12) ∗ ((a + 52#64) ↦₃₂ v13)

theorem pts32_pair_entails_memRegion8 (a : BitVec 64) (v0 v1 : BitVec 32) :
    ((a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1)) ⊢ memRegion a 8 := by
  rw [pointsTo32_pair]
  exact pts64_entails_memRegion8 a _

theorem spill14At_entails_memRegion56 (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 32) :
    spill14At a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ⊢ memRegion a 56 := by
  unfold spill14At
  rw [show (56 : Nat) = 8 + 48 from rfl, memRegion_split a 8 48 (by decide),
      show (48 : Nat) = 8 + 40 from rfl, memRegion_split _ 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split _ 8 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split _ 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split _ 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split _ 8 8 (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
      ((a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1)) ∗
      (((a + 8#64) ↦₃₂ v2) ∗ ((a + 8#64 + 4#64) ↦₃₂ v3)) ∗
      (((a + 16#64) ↦₃₂ v4) ∗ ((a + 16#64 + 4#64) ↦₃₂ v5)) ∗
      (((a + 24#64) ↦₃₂ v6) ∗ ((a + 24#64 + 4#64) ↦₃₂ v7)) ∗
      (((a + 32#64) ↦₃₂ v8) ∗ ((a + 32#64 + 4#64) ↦₃₂ v9)) ∗
      (((a + 40#64) ↦₃₂ v10) ∗ ((a + 40#64 + 4#64) ↦₃₂ v11)) ∗
      (((a + 48#64) ↦₃₂ v12) ∗ ((a + 48#64 + 4#64) ↦₃₂ v13)) by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pts32_pair_entails_memRegion8 a v0 v1)
    (sepConj_mono (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 8#64) v2 v3)
      (sepConj_mono (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 16#64) v4 v5)
        (sepConj_mono (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 24#64) v6 v7)
          (sepConj_mono (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 32#64) v8 v9)
            (sepConj_mono (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 40#64) v10 v11)
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pts32_pair_entails_memRegion8 (a + 48#64) v12 v13))))))

theorem sepWP_memRegion8_pts32_elim {P : Program} {target_pc a : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ v0 v1 : BitVec 32,
      SepWP P target_pc s (((a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1)) ∗ Rest) post oom) :
    SepWP P target_pc s (memRegion a 8 ∗ Rest) post oom := by
  refine sepWP_memRegion8_elim fun w => ?_
  rw [pointsTo64_split32]
  exact h _ _

theorem sepWP_memRegion56_spill14_elim {P : Program} {target_pc a : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 32,
      SepWP P target_pc s
        (spill14At a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ∗ Rest) post oom) :
    SepWP P target_pc s (memRegion a 56 ∗ Rest) post oom := by
  rw [show (56 : Nat) = 8 + 48 from rfl, memRegion_split a 8 48 (by decide),
      show (48 : Nat) = 8 + 40 from rfl, memRegion_split _ 8 40 (by decide),
      show (40 : Nat) = 8 + 32 from rfl, memRegion_split _ 8 32 (by decide),
      show (32 : Nat) = 8 + 24 from rfl, memRegion_split _ 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split _ 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split _ 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepWP_memRegion8_pts32_elim fun v0 v1 => ?_
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 8#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v2 v3 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 16#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v4 v5 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 24#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v6 v7 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 32#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v8 v9 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 40#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v10 v11 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion (a + 48#64) 8 ∗ _ by sep_ac_rfl))
    (sepWP_memRegion8_pts32_elim fun v12 v13 => ?_)
  refine sepWP_weaken_pre (Entails.of_eq ?_) (h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13)
  unfold spill14At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  sep_ac_rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
