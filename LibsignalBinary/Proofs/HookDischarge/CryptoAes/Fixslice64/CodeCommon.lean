/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.StdDetect
public meta import ProofLib.StdStartup.StdDetect
public import LibsignalBinary.Heap.IfaceBudget
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model

/-!
# Shared Separation-Logic Layouts & Stepping Combinators (`Fixslice64.CodeCommon`)

Shared memory representations and `SepWP` stepping infrastructure for `libaes` (`Fixslice64`) and
`signal_crypto::aes_cbc` binary proofs:
- `PureStepPreserved`: bundle of `AllocCallPreserved` and `VmPreserved`, with projection-based
  one-shot discharge `PureStepPreserved.of_proj_perm` and `A.pool` transport;
- `step_str8_perm`, `step_str64_perm`, `step_stp64_perm` (and scoped `wp_str8` / `wp_str64` /
  `wp_stp64` tactics) preserving `m'.perm = s.mem.perm` across stores;
- `adrpAddPair` for relocation-patched `ADRP + ADD` (or `ld.lld`-relaxed `NOP + ADR`) pairs and
  `hasInstrs_prefix` for reachable-prefix code loading;
- `fsStateAt` (`8` 64-bit cells = `64` B), `fsKeys256At` (`15` `fsStateAt` blocks = `960` B),
  `blocks4Bytes`, `bytesAt` splitting, and `SepLoad8.of_bytesAt` byte-load extraction.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon

open Arm64 ProofLib
open ProofLib.StdStartup (adrpOff hasInstrs)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved VmPreserved FdsHiFrame)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 FsKeys256)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)

/-! ## 1. Pure-Step State Preservation (`PureStepPreserved`) -/

/-- Non-memory-content process and virtual-memory state preserved across pure CPU instructions,
    `memset`, and `memcpy`: `AllocCallPreserved s0 sf ∧ VmPreserved s0 sf`. -/
@[expose] def PureStepPreserved (s0 sf : State) : Prop :=
  AllocCallPreserved s0 sf ∧ VmPreserved s0 sf

theorem PureStepPreserved.refl (s : State) : PureStepPreserved s s :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, VmPreserved.refl s⟩

theorem PureStepPreserved.trans {s0 s1 s2 : State}
    (h01 : PureStepPreserved s0 s1) (h12 : PureStepPreserved s1 s2) :
    PureStepPreserved s0 s2 :=
  ⟨⟨h12.1.1.trans h01.1.1, h12.1.2.1.trans h01.1.2.1, h12.1.2.2.1.trans h01.1.2.2.1,
    h12.1.2.2.2.1.trans h01.1.2.2.2.1, h12.1.2.2.2.2.1.trans h01.1.2.2.2.2.1,
    h12.1.2.2.2.2.2.1.trans h01.1.2.2.2.2.2.1, h12.1.2.2.2.2.2.2.trans h01.1.2.2.2.2.2.2⟩,
   h01.2.trans h12.2⟩

theorem PureStepPreserved.allocCallPreserved {s0 sf : State} (h : PureStepPreserved s0 sf) :
    AllocCallPreserved s0 sf := h.1

theorem PureStepPreserved.vmPreserved {s0 sf : State} (h : PureStepPreserved s0 sf) :
    VmPreserved s0 sf := h.2

theorem PureStepPreserved.fs_eq {s0 sf : State} (h : PureStepPreserved s0 sf) :
    sf.fs = s0.fs := h.1.1

theorem PureStepPreserved.trace_eq {s0 sf : State} (h : PureStepPreserved s0 sf) :
    sf.trace = s0.trace := h.1.2.1

theorem PureStepPreserved.pool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s0 sf : State} (h : PureStepPreserved s0 sf) :
    A.pool lim st sf = A.pool lim st s0 :=
  A.pool_transport lim st s0 sf h.2

/-- Tuple projection of all non-memory `State` fields tracked by `PureStepPreserved`. -/
@[expose] def pureStepProj (s : State) :=
  (s.fs, s.trace, s.sigActions, s.tpidrEl0, s.brkStart, s.brk, s.oracle, s.symtab, s.physMemAvail)

namespace Simp

@[scoped simp] theorem pureStepProj_setPC (s : State) (pc : BitVec 64) :
    pureStepProj (s.setPC pc) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_advancePC (s : State) :
    pureStepProj s.advancePC = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    pureStepProj (s.writeReg64 r v) = pureStepProj s := by cases s; cases r <;> rfl
@[scoped simp] theorem pureStepProj_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    pureStepProj (s.writeReg32 r v) = pureStepProj s := pureStepProj_writeReg64 s r _
@[scoped simp] theorem pureStepProj_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    pureStepProj (s.writeReg w r v) = pureStepProj s := pureStepProj_writeReg64 s r _
@[scoped simp] theorem pureStepProj_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    pureStepProj (s.writeVReg128 r v) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_writeVReg64 (s : State) (r : BitVec 5) (v : BitVec 64) :
    pureStepProj (s.writeVReg64 r v) = pureStepProj s := pureStepProj_writeVReg128 s r _
@[scoped simp] theorem pureStepProj_writeVReg32 (s : State) (r : BitVec 5) (v : BitVec 32) :
    pureStepProj (s.writeVReg32 r v) = pureStepProj s := pureStepProj_writeVReg128 s r _
@[scoped simp] theorem pureStepProj_setPState (s : State) (p : PState) :
    pureStepProj (s.setPState p) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_setFpsr (s : State) (f : BitVec 32) :
    pureStepProj (s.setFpsr f) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_orFpsr (s : State) (f : BitVec 32) :
    pureStepProj (s.orFpsr f) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_setMem (s : State) (m : Memory) :
    pureStepProj (s.setMem m) = pureStepProj s := by cases s; rfl
@[scoped simp] theorem pureStepProj_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    pureStepProj (applyWriteback s wb) = pureStepProj s := by
  cases wb <;> simp [applyWriteback, pureStepProj_writeReg64]

@[scoped simp] theorem mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by
  cases s; rfl
@[scoped simp] theorem mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[scoped simp] theorem mem_advancePC_eq (s : State) : s.advancePC.mem = s.mem := by
  cases s; rfl
@[scoped simp] theorem mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[scoped simp] theorem mem_writeReg32_eq (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := mem_writeReg64_eq s r _
@[scoped simp] theorem mem_writeReg_eq (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := mem_writeReg64_eq s r _
@[scoped simp] theorem mem_writeVReg128_eq (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).mem = s.mem := by cases s; rfl
@[scoped simp] theorem mem_setPState_eq (s : State) (p : PState) :
    (s.setPState p).mem = s.mem := by cases s; rfl

end Simp

/-- Construct `PureStepPreserved s0 sf` from equality of `pureStepProj` and `mem.perm`. -/
theorem PureStepPreserved.of_proj_perm {s0 sf : State}
    (hp : pureStepProj sf = pureStepProj s0)
    (hm : sf.mem.perm = s0.mem.perm) :
    PureStepPreserved s0 sf := by
  dsimp only [pureStepProj] at hp
  injection hp with hfs hp1
  injection hp1 with htr hp2
  injection hp2 with hsig hp3
  injection hp3 with htp hp4
  injection hp4 with hbrkS hp5
  injection hp5 with hbrk hp6
  injection hp6 with hor hp7
  injection hp7 with hsym hphys
  exact ⟨⟨hfs, htr, hsig, htp, hbrkS, hor, hsym⟩,
    ⟨⟨hbrkS, hbrk, htp⟩, hphys, fun a => congrFun hm a, FdsHiFrame.of_fs_eq hfs⟩⟩

/-! ## 2. Permission-Preserving Store Step Rules (`step_str8_perm`, `step_str64_perm`, `step_stp64_perm`) -/

/-- 8-bit store (`STRB` / `STURB`) step rule preserving `m'.perm = s.mem.perm`. -/
theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 8}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 8 = val := by
    rw [← bitvec_truncate8_truncate32]; exact hval
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write8 s.mem ea val)) hm'

/-- 64-bit store (`STR` / `STUR`) step rule preserving `m'.perm = s.mem.perm`. -/
theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

/-- 64-bit pair store (`STP Xt1, Xt2, [addr]`) step rule preserving `m'.perm = s.mem.perm`. -/
theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

scoped macro "wp_str8 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str8_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

/-! ## 3. Relocation Pair & Code-Prefix Helpers -/

/-- Two-instruction `ADRP rd, target; ADD rd, rd, :lo12:target` (`relax = false`) or
    `ld.lld`-relaxed `NOP; ADR rd, target` (`relax = true`) pair at `adrpPc`. -/
@[expose] def adrpAddPair (rd : Reg) (adrpPc target : BitVec 64) (relax : Bool := false) :
    List Instr :=
  if relax then
    [ .nop, .adr false rd (target - (adrpPc + 4#64)) ]
  else
    [ .adr true rd (adrpOff adrpPc target),
      .addSubImm .W64 .ADD rd rd (target.truncate 12) false ]

theorem adrpAddPair_length (rd : Reg) (adrpPc target : BitVec 64) (relax : Bool) :
    (adrpAddPair rd adrpPc target relax).length = 2 := by
  cases relax <;> rfl

/-- Restrict `hasInstrs` from `xs ++ ys` to its prefix `xs`. -/
theorem hasInstrs_prefix {P : Program} {base : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P base (xs ++ ys)) :
    hasInstrs P base xs := by
  intro i hi
  have hi' : i < (xs ++ ys).length := by simp [List.length_append]; omega
  have hf := h i hi'
  rwa [List.getElem_append_left hi] at hf

/-! ## 4. `bytesAt` Splitting & `SepLoad8` Extraction -/

theorem bytesAt_append (ro : Bool) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    bytesAt ro a (xs ++ ys) =
      bytesAt ro a xs ∗ bytesAt ro (a + BitVec.ofNat 64 xs.length) ys := by
  cases ro
  · exact pointsToBytes_append a xs ys
  · exact pointsToBytesRO_append a xs ys

theorem SepLoad8.sep_left {a : BitVec 64} {P : SepProp} {v : BitVec 8}
    (h : SepLoad8 a P v) (Q : SepProp) :
    SepLoad8 a (P ∗ Q) v where
  load hm := h.load (by rwa [sepConj_assoc] at hm)
  readable hm := h.readable (by rwa [sepConj_assoc] at hm)

theorem SepLoad8.sep_right {a : BitVec 64} {Q : SepProp} {v : BitVec 8}
    (P : SepProp) (h : SepLoad8 a Q v) :
    SepLoad8 a (P ∗ Q) v where
  load hm := h.load (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)
  readable hm := h.readable (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)

/-- Extract `SepLoad8` at byte offset `off < bs.length` from `bytesAt ro base bs ∗ F`. -/
theorem SepLoad8.of_bytesAt {ro : Bool} {a base : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp}
    (h : P = bytesAt ro base bs ∗ F) (hoff : off < bs.length)
    (ha : base + BitVec.ofNat 64 off = a := by bv_omega) :
    SepLoad8 a P (bs.getD off 0#8) := by
  subst h ha
  have hsplit : bs = bs.take off ++ [bs.getD off 0#8] ++ bs.drop (off + 1) := by
    have h1 := (List.take_append_drop off bs).symm
    have h2 : bs.drop off = bs[off] :: bs.drop (off + 1) := List.drop_eq_getElem_cons hoff
    have hgd : bs.getD off 0#8 = bs[off] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hoff]; rfl
    rw [hgd, List.append_assoc, List.singleton_append, ← h2]; exact h1
  have hlen_take : (bs.take off).length = off := List.length_take_of_le (Nat.le_of_lt hoff)
  cases ro
  · dsimp only [bytesAt]
    have heq : (base ↦ₛ bs) ∗ F =
        ((base + BitVec.ofNat 64 off) ↦₈ bs.getD off 0#8) ∗
          ((base ↦ₛ bs.take off) ∗
           ((base + BitVec.ofNat 64 off + 1#64) ↦ₛ bs.drop (off + 1)) ∗ F) := by
      conv => lhs; rw [hsplit]
      rw [List.append_assoc, pointsToBytes_append, hlen_take,
          pointsToBytes_append, pointsToBytes_singleton]
      sep_ac_rfl
    exact SepLoad8.of_eq heq
  · dsimp only [bytesAt]
    have heq : (base ↦ᵣ bs) ∗ F =
        ((base + BitVec.ofNat 64 off) ↦₈ᵣ bs.getD off 0#8) ∗
          ((base ↦ᵣ bs.take off) ∗
           ((base + BitVec.ofNat 64 off + 1#64) ↦ᵣ bs.drop (off + 1)) ∗ F) := by
      conv => lhs; rw [hsplit]
      rw [List.append_assoc, pointsToBytesRO_append, hlen_take,
          pointsToBytesRO_append, pointsToBytesRO_singleton]
      sep_ac_rfl
    exact SepLoad8.of_ro_eq heq

/-! ## 5. Fixslice Memory Layouts (`fsStateAt`, `blocks4Bytes`, `fsKeys256At`) -/

/-- Eight contiguous 64-bit slice words `[u64; 8]` (`64` bytes) of `st : Model.FsState` at `ptr`. -/
@[expose] def fsStateAt (ptr : BitVec 64) (st : Model.FsState) : SepProp :=
  (ptr ↦₆₄ st.s0) ∗ ((ptr + 8#64) ↦₆₄ st.s1) ∗
  ((ptr + 16#64) ↦₆₄ st.s2) ∗ ((ptr + 24#64) ↦₆₄ st.s3) ∗
  ((ptr + 32#64) ↦₆₄ st.s4) ∗ ((ptr + 40#64) ↦₆₄ st.s5) ∗
  ((ptr + 48#64) ↦₆₄ st.s6) ∗ ((ptr + 56#64) ↦₆₄ st.s7)

/-- 64-byte little-endian byte representation of `st : Model.FsState`. -/
@[expose] def fsStateBytes (st : Model.FsState) : List (BitVec 8) :=
  unpack64 st.s0 ++ unpack64 st.s1 ++ unpack64 st.s2 ++ unpack64 st.s3 ++
  unpack64 st.s4 ++ unpack64 st.s5 ++ unpack64 st.s6 ++ unpack64 st.s7

theorem fsStateBytes_length (st : Model.FsState) : (fsStateBytes st).length = 64 := by
  simp [fsStateBytes, unpack64_length]

theorem fsStateAt_eq_pointsToBytes (ptr : BitVec 64) (st : Model.FsState) :
    fsStateAt ptr st = (ptr ↦ₛ fsStateBytes st) := by
  unfold fsStateAt fsStateBytes
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem fsStateAt_entails_memRegion (ptr : BitVec 64) (st : Model.FsState) :
    fsStateAt ptr st ⊢ memRegion ptr 64 := by
  rw [fsStateAt_eq_pointsToBytes, ← fsStateBytes_length st]
  exact pointsToBytes_entails_memRegion ptr (fsStateBytes st)

theorem memRegion64_eq_exists_fsStateAt (ptr : BitVec 64) :
    memRegion ptr 64 = ∃∗ st : Model.FsState, fsStateAt ptr st := by
  apply Entails.antisymm
  · have hsplit : memRegion ptr 64 =
        memRegion ptr 8 ∗ (memRegion (ptr + 8#64) 8 ∗
        (memRegion (ptr + 16#64) 8 ∗ (memRegion (ptr + 24#64) 8 ∗
        (memRegion (ptr + 32#64) 8 ∗ (memRegion (ptr + 40#64) 8 ∗
        (memRegion (ptr + 48#64) 8 ∗ memRegion (ptr + 56#64) 8)))))) := by
      calc memRegion ptr 64
        _ = memRegion ptr (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8))))))) := rfl
        _ = _ := by
          rw [memRegion_split ptr 8 _ (by decide),
              memRegion_split (ptr + 8#64) 8 _ (by decide),
              memRegion_split (ptr + 8#64 + 8#64) 8 _ (by decide),
              memRegion_split (ptr + 8#64 + 8#64 + 8#64) 8 _ (by decide),
              memRegion_split (ptr + 8#64 + 8#64 + 8#64 + 8#64) 8 _ (by decide),
              memRegion_split (ptr + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 _ (by decide),
              memRegion_split (ptr + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hsplit]
    simp only [memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun s0 => Entails.sepExists_elim fun s1 =>
      Entails.sepExists_elim fun s2 => Entails.sepExists_elim fun s3 =>
      Entails.sepExists_elim fun s4 => Entails.sepExists_elim fun s5 =>
      Entails.sepExists_elim fun s6 => Entails.sepExists_elim fun s7 => ?_
    refine Entails.sepExists_right ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩ ?_
    unfold fsStateAt
    exact Entails.refl _
  · exact Entails.sepExists_elim fun st => fsStateAt_entails_memRegion ptr st

theorem pointsToBytes_zero64_eq_fsStateAt (ptr : BitVec 64) :
    (ptr ↦ₛ List.replicate 64 0#8) = fsStateAt ptr Model.FsState.zero := by
  have hz : List.replicate 64 (0#8) = fsStateBytes Model.FsState.zero := by decide
  rw [hz, ← fsStateAt_eq_pointsToBytes]

/-- Contiguous 64-byte serialization of a 4-block batch `bs : Blocks4`. -/
@[expose] def blocks4Bytes (bs : Blocks4) : List (BitVec 8) :=
  bs.b0 ++ bs.b1 ++ bs.b2 ++ bs.b3

theorem blocks4Bytes_length {bs : Blocks4} (hwf : Blocks4.Wf bs) :
    (blocks4Bytes bs).length = 64 := by
  rcases hwf with ⟨h0, h1, h2, h3⟩
  simp [blocks4Bytes, h0, h1, h2, h3]

theorem bytesAt_blocks4_split (ro : Bool) (ptr : BitVec 64) {bs : Blocks4}
    (hwf : Blocks4.Wf bs) :
    bytesAt ro ptr (blocks4Bytes bs) =
      bytesAt ro ptr bs.b0 ∗
      bytesAt ro (ptr + 16#64) bs.b1 ∗
      bytesAt ro (ptr + 32#64) bs.b2 ∗
      bytesAt ro (ptr + 48#64) bs.b3 := by
  rcases hwf with ⟨h0, h1, h2, _⟩
  unfold blocks4Bytes
  simp only [List.append_assoc, bytesAt_append, h0, h1, h2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Fifteen contiguous `Model.FsState` round keys (`[u64; 120]`, `960` bytes) at `ptr`. -/
@[expose] def fsKeys256At (ptr : BitVec 64) (ks : FsKeys256) : SepProp :=
  fsStateAt ptr ks.rk0 ∗
  fsStateAt (ptr + 0x040#64) ks.rk1 ∗
  fsStateAt (ptr + 0x080#64) ks.rk2 ∗
  fsStateAt (ptr + 0x0c0#64) ks.rk3 ∗
  fsStateAt (ptr + 0x100#64) ks.rk4 ∗
  fsStateAt (ptr + 0x140#64) ks.rk5 ∗
  fsStateAt (ptr + 0x180#64) ks.rk6 ∗
  fsStateAt (ptr + 0x1c0#64) ks.rk7 ∗
  fsStateAt (ptr + 0x200#64) ks.rk8 ∗
  fsStateAt (ptr + 0x240#64) ks.rk9 ∗
  fsStateAt (ptr + 0x280#64) ks.rk10 ∗
  fsStateAt (ptr + 0x2c0#64) ks.rk11 ∗
  fsStateAt (ptr + 0x300#64) ks.rk12 ∗
  fsStateAt (ptr + 0x340#64) ks.rk13 ∗
  fsStateAt (ptr + 0x380#64) ks.rk14

/-- 960-byte little-endian byte representation of `ks : FsKeys256`. -/
@[expose] def fsKeys256Bytes (ks : FsKeys256) : List (BitVec 8) :=
  fsStateBytes ks.rk0 ++ fsStateBytes ks.rk1 ++ fsStateBytes ks.rk2 ++
  fsStateBytes ks.rk3 ++ fsStateBytes ks.rk4 ++ fsStateBytes ks.rk5 ++
  fsStateBytes ks.rk6 ++ fsStateBytes ks.rk7 ++ fsStateBytes ks.rk8 ++
  fsStateBytes ks.rk9 ++ fsStateBytes ks.rk10 ++ fsStateBytes ks.rk11 ++
  fsStateBytes ks.rk12 ++ fsStateBytes ks.rk13 ++ fsStateBytes ks.rk14

theorem fsKeys256Bytes_length (ks : FsKeys256) : (fsKeys256Bytes ks).length = 960 := by
  simp [fsKeys256Bytes, fsStateBytes_length]

theorem fsKeys256At_eq_pointsToBytes (ptr : BitVec 64) (ks : FsKeys256) :
    fsKeys256At ptr ks = (ptr ↦ₛ fsKeys256Bytes ks) := by
  unfold fsKeys256At fsKeys256Bytes
  simp only [List.append_assoc, pointsToBytes_append, fsStateBytes_length,
    ← fsStateAt_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem fsKeys256At_entails_memRegion (ptr : BitVec 64) (ks : FsKeys256) :
    fsKeys256At ptr ks ⊢ memRegion ptr 960 := by
  rw [fsKeys256At_eq_pointsToBytes, ← fsKeys256Bytes_length ks]
  exact pointsToBytes_entails_memRegion ptr (fsKeys256Bytes ks)

/-- Zero-initialized `FsKeys256`. -/
@[expose] def FsKeys256.zero : FsKeys256 :=
  ⟨Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero,
   Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero,
   Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero, Model.FsState.zero⟩

theorem pointsToBytes_zero960_eq_fsKeys256At (ptr : BitVec 64) :
    (ptr ↦ₛ List.replicate 960 0#8) = fsKeys256At ptr FsKeys256.zero := by
  have hz64 : List.replicate 64 (0#8) = fsStateBytes Model.FsState.zero := by decide
  have hz960 : List.replicate 960 (0#8) = fsKeys256Bytes FsKeys256.zero := by
    unfold fsKeys256Bytes FsKeys256.zero
    simp only [← hz64, ← List.replicate_add]
  rw [hz960, ← fsKeys256At_eq_pointsToBytes]

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
