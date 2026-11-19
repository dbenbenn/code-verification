/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import ProofLib.StdStartup.StdDetect
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model

/-!
# Internal Step Rules, Stack Layout & Prologue for `expand_key::<32, 15>` (`Armv8.KeyScheduleAux`)

Internal instruction word segments, 32-bit/branch `SepWP` step lemmas, `dup v1.4s` / `aese`
`armv8SubWord` reductions, `0x100`-byte stack frame split/merge lemmas, loop state invariant
`ExpandInv` with `Fin 52` index arithmetic, and `prologue_sepWP` for `Armv8.KeySchedule`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeyScheduleAux

open Arm64 ProofLib
open ProofLib.StdStartup (adrpOff decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconWords aesRconBytes u32OfBytesLE bytesToU32LE u32ToBytesLE
   u128ToBytesLE armv8SubWord roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (words60Bytes expandWords60At pointsTo128_eq_pointsToBytes roundKeys15At_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj adrpAddPair step_str64_perm step_stp64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

/-! ## 1. `expand_key::<32, 15>` Instruction Word Segments -/

@[expose] def expandKeySeg0Words : List (BitVec 32) :=
  [0xd10403ff#32, 0xa90f7bfd#32, 0x9103c3fd#32, 0xf9400029#32, 0x6f00e400#32,
   0xaa1f03e8#32, 0xf90003e9#32, 0x2941242a#32, 0xad0183e0#32, 0xad0283e0#32,
   0x290127ea#32, 0xb9401029#32, 0xb9401c2a#32, 0xad0383e0#32, 0xb90013e9#32,
   0xf8414029#32, 0xb9001fea#32]

@[expose] def expandKeyPrologueTailWords : List (BitVec 32) :=
  [0xf80143e9#32, 0x910003e9#32, 0xad0483e0#32, 0xad0583e0#32, 0xad0683e0#32,
   0x3d800be0#32, 0x1400000a#32]

@[expose] def expandKeyLoopJoinWords : List (BitVec 32) :=
  [0x4e040d81#32, 0x4e284801#32, 0x1e26002c#32, 0xb868792d#32, 0x91000508#32,
   0xf100d11f#32, 0x4a0c01ac#32, 0xb900216c#32, 0x54000220#32]

@[expose] def expandKeyLoopHdrWords : List (BitVec 32) :=
  [0x8b08092b#32, 0x9100210d#32, 0x924009ae#32, 0xb9401d6c#32, 0xf10011df#32,
   0x54fffe40#32, 0xb5fffe8e#32, 0xd343fdad#32, 0xb400036d#32, 0x4e040d81#32,
   0x8b0d094c#32, 0xb85fc18c#32, 0x4e284801#32, 0x1e26002d#32, 0x4acd218c#32,
   0x17ffffeb#32]

@[expose] def expandKeyEpilogueWords : List (BitVec 32) :=
  [0xad4607e0#32, 0x3dc03be2#32, 0x3d803802#32, 0xad060400#32, 0xad4407e0#32,
   0xad040400#32, 0xad450be0#32, 0xad050800#32, 0xad4203e1#32, 0xad020001#32,
   0xad430be0#32, 0xad030800#32, 0xad4003e1#32, 0xad000001#32, 0xad410be0#32,
   0xad010800#32, 0xa94f7bfd#32, 0x910403ff#32, 0xd65f03c0#32]

/-! ## 2. Step Rules (`step_str32_perm`, `step_stp32_perm`, `step_adrpAddPair_x10`) & Bit Lemmas -/

private theorem perm_write32 (m : Memory) (addr : BitVec 64) (val : BitVec 32) :
    (m.write32 addr val).perm = m.perm := by
  simp only [Memory.write32, Memory.perm_write8]

private theorem sepStore32_here_region {a a' : BitVec 64} {v' : BitVec 32} (ha : a' = a) :
    SepStore32 a v' (memRegion a' 4) (a' ↦₃₂ v') :=
  ha ▸ ⟨fun hm => (IsBlock.memRegion a' 4).write32 hm v',
        fun hm => (IsBlock.memRegion a' 4).canWrite (by decide) hm⟩

private theorem sepStore64_here_region {a a' : BitVec 64} {v' : BitVec 64} (ha : a' = a) :
    SepStore64 a v' (memRegion a' 8) (a' ↦₆₄ v') :=
  ha ▸ ⟨fun hm => (IsBlock.memRegion a' 8).write64 hm v',
        fun hm => (IsBlock.memRegion a' 8).canWrite (by decide) hm⟩

theorem step_str32_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 32}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.str .W32 rt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P') (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
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
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (perm_write32 s.mem ea val)) hm'

private theorem step_stp32_perm {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {v1 v2 : BitVec 32} {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
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
  let m1 := s.mem.write32 ea v1; let m2 := m1.write32 ea2 v2
  have ht1 : (s.readReg64 rt1).truncate 32 = v1 := hv1
  have ht2 : (s.readReg64 rt2).truncate 32 = v2 := hv2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 4 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 4 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (perm_write32 s.mem ea v1)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, ht1, ht2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((perm_write32 m1 ea2 v2).trans (perm_write32 s.mem ea v1))) hm2

local syntax "solve_store32" : tactic
local macro_rules
  | `(tactic| solve_store32) => `(tactic| first
      | ((with_reducible apply SepStore32.here); close_addr128)
      | ((with_reducible apply sepStore32_here_region); close_addr128)
      | ((with_reducible apply SepStore32.left); solve_store32)
      | ((with_reducible apply SepStore32.right); solve_store32))

local syntax "solve_store64" : tactic
local macro_rules
  | `(tactic| solve_store64) => `(tactic| first
      | ((with_reducible apply SepStore64.here); close_addr128)
      | ((with_reducible apply sepStore64_here_region); close_addr128)
      | ((with_reducible apply SepStore64.left); solve_store64)
      | ((with_reducible apply SepStore64.right); solve_store64))

local macro "wp_str32_reg " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str32_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store32)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp32_reg " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp32_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store32); (· solve_store32)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_str64_reg " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store64)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp64_reg " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store64); (· solve_store64)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

private theorem adrp_add_lo12_eq (pc target : BitVec 64) :
    (pc &&& 0xfffffffffffff000#64) + adrpOff pc target + (target.truncate 12).zeroExtend 64 =
      target := by
  unfold adrpOff; bv_bits

private theorem step_adrpAddPair_x10 {prog : Program} {target_pc adrpPc target : BitVec 64}
    {relax : Bool} {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs prog adrpPc (adrpAddPair (.gpr 10#5) adrpPc target relax))
    (hpc : s.pc = adrpPc) (hrun : s.status = .Running)
    (hnext : SepWP prog target_pc ((s.writeReg64 (.gpr 10#5) target).setPC (adrpPc + 8#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  have hadd := adrp_add_lo12_eq adrpPc target
  have hrel : adrpPc + 4#64 + (target - (adrpPc + 4#64)) = target := by bv_lin
  have hpc8 : adrpPc + 4#64 + 4#64 = adrpPc + 8#64 := by bv_lin
  cases relax <;> (dsimp only [adrpAddPair] at hc; have_instrs hc 0 2; wp_steps 2; convert hnext using 2)

theorem step_bCond {prog : Program} {target_pc pc off nextPc : BitVec 64}
    {cond : CondCode} {taken : Bool} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hfetch : prog.fetch pc = some (.bCond cond off)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hcond : ConditionHolds cond s.pstate = taken)
    (hnextPc : (if taken then pc + off else pc + 4#64) = nextPc)
    (hnext : SepWP prog target_pc (s.setPC nextPc) P post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_pure (s' := s.setPC nextPc) hpc hrun hfetch ?_ rfl hnext
  rw [← hnextPc]; cases s; cases taken <;>
    simp_all [Program.evalInst, execInstWithSvc, State.advancePC, State.setPC]

theorem step_cbz64 {prog : Program} {target_pc pc off nextPc : BitVec 64}
    {isNonZero : Bool} {rt : Reg} {taken : Bool} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hfetch : prog.fetch pc = some (.cbz .W64 isNonZero rt off))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hcond : (if isNonZero then (s.readReg64 rt == 0#64) != true else s.readReg64 rt == 0#64) = taken)
    (hnextPc : (if taken then pc + off else pc + 4#64) = nextPc)
    (hnext : SepWP prog target_pc (s.setPC nextPc) P post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_pure (s' := s.setPC nextPc) hpc hrun hfetch ?_ rfl hnext
  rw [← hnextPc]; cases s; cases isNonZero <;> cases taken <;>
    simp_all [Program.evalInst, execInstWithSvc, State.advancePC, State.setPC, State.readReg, State.readReg64]

private theorem pack32_eq_bytesToU32LE (bs : List (BitVec 8)) (off : Nat) :
    pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8) = bytesToU32LE bs off := rfl

private theorem pack64_eq_bytesToU32LE_pair (bs : List (BitVec 8)) (off : Nat) :
    pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
      (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8) (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) =
    bytesToU32LE bs (off + 4) ++ bytesToU32LE bs off := by
  dsimp only [pack64, bytesToU32LE, u32OfBytesLE]
  have h4 : off + 4 + 1 = off + 5 := by omega
  have h5 : off + 4 + 2 = off + 6 := by omega
  have h6 : off + 4 + 3 = off + 7 := by omega
  rw [h4, h5, h6]; bv_bits

theorem sepLoad32_of_bytesAt {ro : Bool} {a base : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp} (h : P = bytesAt ro base bs ∗ F) (hoff : off + 4 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad32 a P (bytesToU32LE bs off) := by
  rw [← pack32_eq_bytesToU32LE]
  cases ro
  · exact SepLoad32.of_pointsToBytes h hoff ha
  · exact SepLoad32.of_pointsToBytesRO h hoff ha

private theorem sepLoad64_of_bytesAt {ro : Bool} {a base : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp} (h : P = bytesAt ro base bs ∗ F) (hoff : off + 8 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = a) :
    SepLoad64 a P (bytesToU32LE bs (off + 4) ++ bytesToU32LE bs off) := by
  rw [← pack64_eq_bytesToU32LE_pair]
  cases ro
  · exact SepLoad64.of_pointsToBytes h hoff ha
  · exact SepLoad64.of_pointsToBytesRO h hoff ha

theorem dup4s_expanded_eq (w : BitVec 32) :
    (BitVec.setWidth 128 w &&& 4294967295#128 &&& 4294967295#128 |||
     (BitVec.setWidth 128 w &&& 4294967295#128 &&& 4294967295#128) <<< 32 |||
     (BitVec.setWidth 128 w &&& 4294967295#128 &&& 4294967295#128) <<< 64 |||
     (BitVec.setWidth 128 w &&& 4294967295#128 &&& 4294967295#128) <<< 96) =
    w ++ w ++ w ++ w := by
  have h0 : BitVec.setWidth 128 w &&& 4294967295#128 &&& 4294967295#128 = w.zeroExtend 128 := by bv_bits
  have h1 : (w.zeroExtend 128 ||| w.zeroExtend 128 <<< 32) = (w ++ w).zeroExtend 128 := by bv_bits
  have h2 : ∀ u : BitVec 64, u.zeroExtend 128 ||| w.zeroExtend 128 <<< 64 = (w ++ u).zeroExtend 128 :=
    fun _ => by bv_bits
  have h3 : ∀ u : BitVec 96, u.zeroExtend 128 ||| w.zeroExtend 128 <<< 96 = w ++ u :=
    fun _ => by bv_bits
  rw [h0, h1, h2 (w ++ w), h3 (w ++ (w ++ w))]; bv_bits

theorem truncate32_zeroExtend64 (w : BitVec 32) : (w.zeroExtend 64).truncate 32 = w := by bv_bits

theorem truncate32_aese_dup_eq_armv8SubWord (w : BitVec 32) :
    (evalAesOp .AESE (w ++ w ++ w ++ w) 0#128).truncate 32 = armv8SubWord w := by
  dsimp only [armv8SubWord]; bv_bits

/-! ## 3. Stack Frame Split/Merge & Initial 60-Word Equivalence -/

@[expose] def armv8InitWords (keyBytes : List (BitVec 8)) : Vector (BitVec 32) 60 :=
  Vector.ofFn fun j : Fin 60 =>
    if j.val < 8 then bytesToU32LE keyBytes (4 * j.val) else 0#32

private def stackZeroRegions13 (spLocal : BitVec 64) : SepProp :=
  memRegion (spLocal + 0x20#64) 16 ∗ memRegion (spLocal + 0x30#64) 16 ∗
  memRegion (spLocal + 0x40#64) 16 ∗ memRegion (spLocal + 0x50#64) 16 ∗
  memRegion (spLocal + 0x60#64) 16 ∗ memRegion (spLocal + 0x70#64) 16 ∗
  memRegion (spLocal + 0x80#64) 16 ∗ memRegion (spLocal + 0x90#64) 16 ∗
  memRegion (spLocal + 0xa0#64) 16 ∗ memRegion (spLocal + 0xb0#64) 16 ∗
  memRegion (spLocal + 0xc0#64) 16 ∗ memRegion (spLocal + 0xd0#64) 16 ∗
  memRegion (spLocal + 0xe0#64) 16

private def stackKeyRegions6 (spLocal : BitVec 64) : SepProp :=
  memRegion spLocal 8 ∗ memRegion (spLocal + 0x08#64) 4 ∗
  memRegion (spLocal + 0x0c#64) 4 ∗ memRegion (spLocal + 0x10#64) 4 ∗
  memRegion (spLocal + 0x14#64) 8 ∗ memRegion (spLocal + 0x1c#64) 4

private theorem stackFrameAt256_split (sp0 : BitVec 64) :
    stackFrameAt sp0 0x100 =
      stackKeyRegions6 (sp0 - 0x100#64) ∗ stackZeroRegions13 (sp0 - 0x100#64) ∗
      (memRegion (sp0 - 0x100#64 + 0xf0#64) 8 ∗ memRegion (sp0 - 0x100#64 + 0xf8#64) 8) := by
  rw [← stackAt_eq_stackFrameAt sp0 0x100]
  dsimp only [stackAt, stackKeyRegions6, stackZeroRegions13]
  generalize sp0 - 256#64 = b
  rw [show (256 : Nat) = 32 + (208 + 16) from rfl,
      memRegion_split b 32 (208 + 16) (by decide),
      memRegion_split (b + 32#64) 208 16 (by decide)]
  have hk : memRegion b 32 =
      memRegion b 8 ∗ memRegion (b + 0x08#64) 4 ∗ memRegion (b + 0x0c#64) 4 ∗
      memRegion (b + 0x10#64) 4 ∗ memRegion (b + 0x14#64) 8 ∗ memRegion (b + 0x1c#64) 4 := by
    rw [show (32 : Nat) = 8 + (4 + (4 + (4 + (8 + 4)))) from rfl,
        memRegion_split b 8 _ (by decide), memRegion_split _ 4 _ (by decide),
        memRegion_split _ 4 _ (by decide), memRegion_split _ 4 _ (by decide),
        memRegion_split _ 8 4 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hz : memRegion (b + 32#64) 208 =
      memRegion (b + 0x20#64) 16 ∗ memRegion (b + 0x30#64) 16 ∗ memRegion (b + 0x40#64) 16 ∗
      memRegion (b + 0x50#64) 16 ∗ memRegion (b + 0x60#64) 16 ∗ memRegion (b + 0x70#64) 16 ∗
      memRegion (b + 0x80#64) 16 ∗ memRegion (b + 0x90#64) 16 ∗ memRegion (b + 0xa0#64) 16 ∗
      memRegion (b + 0xb0#64) 16 ∗ memRegion (b + 0xc0#64) 16 ∗ memRegion (b + 0xd0#64) 16 ∗
      memRegion (b + 0xe0#64) 16 := by
    rw [show (208 : Nat) = 16 + (16 + (16 + (16 + (16 + (16 + (16 + (16 + (16 + (16 + (16 + (16 + 16))))))))))) from rfl]
    iterate 12 rw [memRegion_split _ 16 _ (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hf : memRegion (b + 32#64 + 208#64) 16 = memRegion (b + 0xf0#64) 8 ∗ memRegion (b + 0xf8#64) 8 := by
    rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split _ 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hk, hz, hf]

private theorem unpack64_pair_u32 (lo hi : BitVec 32) :
    unpack64 (hi ++ lo) = u32ToBytesLE lo ++ u32ToBytesLE hi := by
  simp only [unpack64, u32ToBytesLE, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem u32ToBytesLE_length (w : BitVec 32) : (u32ToBytesLE w).length = 4 := rfl

private theorem initWords_toList_eq (kb : List (BitVec 8)) :
    (armv8InitWords kb).toList =
      [bytesToU32LE kb 0, bytesToU32LE kb 4, bytesToU32LE kb 8, bytesToU32LE kb 12,
       bytesToU32LE kb 16, bytesToU32LE kb 20, bytesToU32LE kb 24, bytesToU32LE kb 28] ++
      List.replicate 52 0#32 := by
  apply List.ext_getElem (by simp [armv8InitWords]); intro i hi1 _
  have hi : i < 60 := by simp [armv8InitWords] at hi1; exact hi1
  interval_cases i <;> simp [armv8InitWords]

private theorem stack_key6_eq_bytes (b : BitVec 64) (kb : List (BitVec 8)) :
    (b ↦₆₄ (bytesToU32LE kb 4 ++ bytesToU32LE kb 0)) ∗
    ((b + 0x08#64) ↦₃₂ bytesToU32LE kb 8) ∗ ((b + 0x0c#64) ↦₃₂ bytesToU32LE kb 12) ∗
    ((b + 0x10#64) ↦₃₂ bytesToU32LE kb 16) ∗
    ((b + 0x14#64) ↦₆₄ (bytesToU32LE kb 24 ++ bytesToU32LE kb 20)) ∗
    ((b + 0x1c#64) ↦₃₂ bytesToU32LE kb 28) =
    b ↦ₛ ([bytesToU32LE kb 0, bytesToU32LE kb 4, bytesToU32LE kb 8, bytesToU32LE kb 12,
           bytesToU32LE kb 16, bytesToU32LE kb 20, bytesToU32LE kb 24, bytesToU32LE kb 28].map
          u32ToBytesLE).flatten := by
  have hu32 (w : BitVec 32) : unpack32 w = u32ToBytesLE w := rfl
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, unpack64_pair_u32, unpack64_pair_u32]
  simp only [pointsTo32_eq_pointsToBytes, hu32]
  iterate 9 rw [pointsToBytes_append]
  simp only [u32ToBytesLE_length, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem replicate_u32_zero_eq_u128_zero :
    ∀ n : Nat, (List.replicate (4 * n) (u32ToBytesLE 0#32)).flatten =
      (List.replicate n (u128ToBytesLE 0#128)).flatten
  | 0 => rfl
  | n + 1 => by
    have h4 : (List.replicate 4 (u32ToBytesLE 0#32)).flatten = u128ToBytesLE 0#128 := by decide
    rw [Nat.mul_succ, Nat.add_comm _ 4, List.replicate_add, List.flatten_append,
        h4, replicate_u32_zero_eq_u128_zero n, List.replicate_succ, List.flatten_cons]

private theorem stack_zero13_eq_bytes (b : BitVec 64) :
    ((b + 0x20#64) ↦₁₂₈ 0#128) ∗ ((b + 0x30#64) ↦₁₂₈ 0#128) ∗ ((b + 0x40#64) ↦₁₂₈ 0#128) ∗
    ((b + 0x50#64) ↦₁₂₈ 0#128) ∗ ((b + 0x60#64) ↦₁₂₈ 0#128) ∗ ((b + 0x70#64) ↦₁₂₈ 0#128) ∗
    ((b + 0x80#64) ↦₁₂₈ 0#128) ∗ ((b + 0x90#64) ↦₁₂₈ 0#128) ∗ ((b + 0xa0#64) ↦₁₂₈ 0#128) ∗
    ((b + 0xb0#64) ↦₁₂₈ 0#128) ∗ ((b + 0xc0#64) ↦₁₂₈ 0#128) ∗ ((b + 0xd0#64) ↦₁₂₈ 0#128) ∗
    ((b + 0xe0#64) ↦₁₂₈ 0#128) =
    (b + 0x20#64) ↦ₛ (List.replicate 52 (u32ToBytesLE 0#32)).flatten := by
  rw [show (52 : Nat) = 4 * 13 from rfl, replicate_u32_zero_eq_u128_zero 13]
  simp only [pointsTo128_eq_pointsToBytes]
  generalize hzv : u128ToBytesLE 0#128 = z16
  have hzlen : z16.length = 16 := by subst hzv; rfl
  simp only [List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  iterate 12 rw [pointsToBytes_append]
  simp only [hzlen, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stack_key_zero_eq_expandWords60At (b : BitVec 64) (kb : List (BitVec 8)) (R : SepProp) :
    (b ↦ₛ ([bytesToU32LE kb 0, bytesToU32LE kb 4, bytesToU32LE kb 8, bytesToU32LE kb 12,
            bytesToU32LE kb 16, bytesToU32LE kb 20, bytesToU32LE kb 24, bytesToU32LE kb 28].map
           u32ToBytesLE).flatten) ∗
    ((b + 0x20#64) ↦ₛ (List.replicate 52 (u32ToBytesLE 0#32)).flatten) ∗ R =
    expandWords60At b (armv8InitWords kb) ∗ R := by
  have hlen32 : ([bytesToU32LE kb 0, bytesToU32LE kb 4, bytesToU32LE kb 8, bytesToU32LE kb 12,
      bytesToU32LE kb 16, bytesToU32LE kb 20, bytesToU32LE kb 24, bytesToU32LE kb 28].map
      u32ToBytesLE).flatten.length = 32 := by simp [u32ToBytesLE_length]
  rw [expandWords60At, words60Bytes, initWords_toList_eq, List.map_append, List.map_replicate,
      List.flatten_append, pointsToBytes_append, hlen32, sepConj_assoc]

theorem epilogue_stack_entails_stackFrameAt256 (sp0 v29 v30 : BitVec 64) (rks : Vector (BitVec 128) 15) :
    roundKeys15At (sp0 - 0x100#64) rks ∗
      (((sp0 - 0x100#64 + 0xf0#64) ↦₆₄ v29) ∗ ((sp0 - 0x100#64 + 0xf8#64) ↦₆₄ v30)) ⊢
    stackFrameAt sp0 0x100 := by
  rw [← stackAt_eq_stackFrameAt sp0 0x100]; dsimp only [stackAt]
  generalize sp0 - 256#64 = b
  rw [show (256 : Nat) = 240 + (8 + 8) from rfl,
      memRegion_split b 240 (8 + 8) (by decide), memRegion_split (b + 240#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (roundKeys15At_entails_memRegion b rks)
    (sepConj_mono (pointsTo64_entails_memRegion _ v29) (pointsTo64_entails_memRegion _ v30))

/-! ## 4. State Invariant & Pure `Fin 52` Loop Arithmetic Lemmas -/

@[expose] def calleeSavedGprs19_28 (s : State) :=
  (s.readReg64 (.gpr 19#5), s.readReg64 (.gpr 20#5), s.readReg64 (.gpr 21#5),
   s.readReg64 (.gpr 22#5), s.readReg64 (.gpr 23#5), s.readReg64 (.gpr 24#5),
   s.readReg64 (.gpr 25#5), s.readReg64 (.gpr 26#5), s.readReg64 (.gpr 27#5),
   s.readReg64 (.gpr 28#5))

structure ExpandInv (s0 : State) (outPtr rconAddr : BitVec 64) (s : State) : Prop where
  pure : PureStepPreserved s0 s
  sp_eq : s.sp = s0.sp - 0x100#64
  sp0_al : (s0.sp &&& 15#64 == 0#64) = true
  sp_al : s.spAligned = true
  x0_eq : s.readReg64 .x0 = outPtr
  x9_eq : s.readReg64 (.gpr 9#5) = s0.sp - 0x100#64
  x10_eq : s.readReg64 (.gpr 10#5) = rconAddr
  v0_eq : s.readVReg128 0#5 = 0#128
  cs_gprs : calleeSavedGprs19_28 s = calleeSavedGprs19_28 s0
  cs_vregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem ExpandInv.step {s0 s1 s2 : State} {outPtr rconAddr : BitVec 64}
    (h1 : ExpandInv s0 outPtr rconAddr s1) (hp : pureStepProj s2 = pureStepProj s1)
    (hm : s2.mem.perm = s1.mem.perm) (hsp : s2.sp = s1.sp)
    (hx0 : s2.readReg64 .x0 = s1.readReg64 .x0)
    (hx9 : s2.readReg64 (.gpr 9#5) = s1.readReg64 (.gpr 9#5))
    (hx10 : s2.readReg64 (.gpr 10#5) = s1.readReg64 (.gpr 10#5))
    (hv0 : s2.readVReg128 0#5 = s1.readVReg128 0#5)
    (hg : calleeSavedGprs19_28 s2 = calleeSavedGprs19_28 s1)
    (hv : calleeSavedVRegs s2 = calleeSavedVRegs s1) :
    ExpandInv s0 outPtr rconAddr s2 :=
  ⟨h1.pure.trans (PureStepPreserved.of_proj_perm hp hm),
   hsp.trans h1.sp_eq, h1.sp0_al, by simp only [State.spAligned, hsp]; exact h1.sp_al,
   hx0.trans h1.x0_eq, hx9.trans h1.x9_eq, hx10.trans h1.x10_eq,
   hv0.trans h1.v0_eq, hg.trans h1.cs_gprs, hv.trans h1.cs_vregs⟩

theorem k_lsl2_eq (k : Fin 52) : (BitVec.ofNat 64 k.val <<< 2) = BitVec.ofNat 64 (4 * k.val) := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_prev_off_eq (k : Fin 52) : BitVec.ofNat 64 (4 * k.val) + 28#64 = BitVec.ofNat 64 (4 * (k.val + 7)) := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_out_off_eq (k : Fin 52) : BitVec.ofNat 64 (4 * k.val) + 32#64 = BitVec.ofNat 64 (4 * (k.val + 8)) := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_inc_eq (k : Fin 52) : BitVec.ofNat 64 k.val + 1#64 = BitVec.ofNat 64 (k.val + 1) := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_cmp52_iff (k : Fin 52) : BitVec.ofNat 64 (k.val + 1) = 52#64 ↔ k.val + 1 = 52 := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_mod8_eq4_iff (k : Fin 52) : (BitVec.ofNat 64 k.val + 8#64) &&& 7#64 = 4#64 ↔ k.val % 8 = 4 := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_mod8_eq0_iff (k : Fin 52) : (BitVec.ofNat 64 k.val + 8#64) &&& 7#64 = 0#64 ↔ k.val % 8 = 0 := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_div8_ne0 (k : Fin 52) : (BitVec.ofNat 64 k.val + 8#64) >>> 3 ≠ 0#64 := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_rcon_off_eq (k : Fin 52) :
    (((BitVec.ofNat 64 k.val + 8#64) >>> 3) <<< 2) + 0xfffffffffffffffc#64 =
      BitVec.ofNat 64 (4 * ((k.val + 8) / 8 - 1)) := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

theorem k_rcon_word_eq (k : Fin 52) :
    bytesToU32LE aesRconBytes (4 * (k.val / 8)) = aesRconWords.getD (k.val / 8) 0#32 := by
  have hk := k.isLt; generalize k.val = kv at hk ⊢; interval_cases kv <;> decide

/-! ## 5. Prologue `SepWP` Proof (`+0x00..+0x64` -> `+0x8c`) -/

set_option maxHeartbeats 400000 in
theorem prologue_sepWP {P : Program} {target_pc fnAddr outPtr keyPtr rconAddr : BitVec 64}
    {roKey relaxRcon : Bool} {keyBytes : List (BitVec 8)} {F : SepProp}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc0 : hasInstrs P fnAddr (decodeWords expandKeySeg0Words))
    (hcRcon : hasInstrs P (fnAddr + 0x44#64)
      (adrpAddPair (.gpr 10#5) (fnAddr + 0x44#64) rconAddr relaxRcon))
    (hcTail : hasInstrs P (fnAddr + 0x4c#64) (decodeWords expandKeyPrologueTailWords))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = outPtr) (hx1 : s0.readReg64 .x1 = keyPtr)
    (hklen : keyBytes.length = 32)
    (hnext : ∀ s1 : State, s1.pc = fnAddr + 0x8c#64 → s1.status = .Running →
      ExpandInv s0 outPtr rconAddr s1 → s1.readReg64 (.gpr 8#5) = 0#64 →
      SepWP P target_pc s1
        (expandWords60At (s0.sp - 0x100#64) (armv8InitWords keyBytes) ∗
         bytesAt roKey keyPtr keyBytes ∗
         (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗ F) post oom) :
    SepWP P target_pc s0 (bytesAt roKey keyPtr keyBytes ∗ stackFrameAt s0.sp 0x100 ∗ F) post oom := by
  have hsp0_al : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp
  have hspLocal : ((s0.sp - 0x100#64) &&& 15#64 == 0#64) = true := s0.spAligned_sub 0x100#64 hsp
  rw [stackFrameAt256_split s0.sp]
  dsimp only [stackKeyRegions6, stackZeroRegions13]
  have_instrs hc0 0 17
  wp_steps 1; wp_stp64_reg hf_1 m1 hm1; wp_steps 1
  apply SepWP.step_ldr64 (ea := keyPtr) (wb := none)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs) hf_3
    (by wp_focus_close wp_norm_lhs) (by simp [evalAddrMode, wp_norm, arm64_norm, hx1])
    (sepLoad64_of_bytesAt (off := 0) (F := _) rfl (by omega) (by bv_lin)) rfl
  try wp_norm_state
  wp_steps 2; wp_str64_reg hf_6 m2 hm2
  apply SepWP.step_ldp32 (ea := keyPtr + 8#64) (ea2 := keyPtr + 12#64) (wb := none)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs) hf_7
    (by wp_focus_close wp_norm_lhs) (by simp [evalAddrMode, wp_norm, arm64_norm, hx1]) (by bv_lin)
    (sepLoad32_of_bytesAt (off := 8) (F := _) rfl (by omega) (by bv_lin))
    (sepLoad32_of_bytesAt (off := 12) (F := _) rfl (by omega) (by bv_lin)) rfl
  try wp_norm_state
  wp_stp128 hf_8 m3 hm3; wp_stp128 hf_9 m4 hm4; wp_stp32_reg hf_10 m5 hm5
  apply SepWP.step_ldr32 (ea := keyPtr + 16#64) (wb := none)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs) hf_11
    (by wp_focus_close wp_norm_lhs) (by simp [evalAddrMode, wp_norm, arm64_norm, hx1])
    (sepLoad32_of_bytesAt (off := 16) (F := _) rfl (by omega) (by bv_lin)) rfl
  try wp_norm_state
  apply SepWP.step_ldr32 (ea := keyPtr + 28#64) (wb := none)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs) hf_12
    (by wp_focus_close wp_norm_lhs) (by simp [evalAddrMode, wp_norm, arm64_norm, hx1])
    (sepLoad32_of_bytesAt (off := 28) (F := _) rfl (by omega) (by bv_lin)) rfl
  try wp_norm_state
  wp_stp128 hf_13 m6 hm6; wp_str32_reg hf_14 m7 hm7
  apply SepWP.step_ldr64 (ea := keyPtr + 20#64) (wb := none)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs) hf_15
    (by wp_focus_close wp_norm_lhs) (by simp [evalAddrMode, wp_norm, arm64_norm, hx1])
    (sepLoad64_of_bytesAt (off := 20) (F := _) rfl (by omega) (by bv_lin)) rfl
  try wp_norm_state
  wp_str32_reg hf_16 m8 hm8
  apply step_adrpAddPair_x10 hcRcon (by simp [wp_norm, arm64_norm, *]; try bv_lin)
    (by wp_focus_close wp_norm_lhs)
  try wp_norm_state
  clear hf_0 hf_1 hf_2 hf_3 hf_4 hf_5 hf_6
  have_instrs hcTail 0 7
  wp_str64_reg hf_0 m9 hm9; wp_steps 1
  wp_stp128 hf_2 m10 hm10; wp_stp128 hf_3 m11 hm11; wp_stp128 hf_4 m12 hm12; wp_str128 hf_5 m13 hm13
  wp_steps 1
  rw [stack_key6_eq_bytes, stack_zero13_eq_bytes, stack_key_zero_eq_expandWords60At]
  have hreord :
      bytesAt roKey keyPtr keyBytes ∗
        (expandWords60At (s0.sp - 0x100#64) (armv8InitWords keyBytes) ∗
         (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr))) ∗ F =
      expandWords60At (s0.sp - 0x100#64) (armv8InitWords keyBytes) ∗
      bytesAt roKey keyPtr keyBytes ∗
      (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗ F := by sep_ac_rfl
  rw [hreord]
  refine hnext _ (by simp [wp_norm, arm64_norm, *]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun]) ?_ (by simp [wp_norm, arm64_norm])
  refine ⟨PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]),
    by simp [wp_norm, arm64_norm], hsp0_al,
    by simpa [State.spAligned, wp_norm, arm64_norm] using hspLocal,
    by simp [wp_norm, arm64_norm, hx0], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [calleeSavedGprs19_28, wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm, isCalleeSavedVReg]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeyScheduleAux
