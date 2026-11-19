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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
meta import ProofLib.StdStartup.StdDetect

/-!
# Key-Schedule Layout Helpers & `inv_expanded_keys::<15>` (`Armv8.InvExpand`)

Shared 128-bit `↦₁₂₈` SIMD step combinators, 240-byte `↦ₛ` / `memRegion` ↔ `roundKeys15At`
conversion lemmas, the 60-word `u32` stack layout `expandWords60At` for `expand_key::<32, 15>`,
and the placement-generic `subroutine_ok` verification of the 30-instruction position-independent
decryption key-schedule inversion routine `aes::armv8::expand::inv_expanded_keys::<15>`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (evalAesOp_aesimc_vd_irrel u32OfBytesLE bytesToU32LE u32ToBytesLE u128OfU32sLE
   bytesToU128LE u128ToBytesLE armv8PackRoundKeys armv8InvExpandedKeys
   roundKeys15Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

/-! ## 1. Direct 128-Bit `↦₁₂₈` SIMD Load/Store/Pair Step Combinators -/

structure SepLoad128 (a : BitVec 64) (P : SepProp) (v : BitVec 128) : Prop where
  load : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.read128 a = v
  readable : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.canRead a 16 = true

theorem SepLoad128.here {a a' : BitVec 64} {v : BitVec 128} (ha : a' = a) :
    SepLoad128 a (a' ↦₁₂₈ v) v :=
  ha ▸ ⟨fun hm => (IsBlock.pointsTo128 a' v).read hm,
        fun hm => (IsBlock.pointsTo128 a' v).canRead (by decide) hm⟩

theorem SepLoad128.left {a : BitVec 64} {v : BitVec 128} {P Q : SepProp}
    (h : SepLoad128 a P v) : SepLoad128 a (P ∗ Q) v :=
  ⟨fun hm => h.load (by rwa [sepConj_assoc] at hm),
   fun hm => h.readable (by rwa [sepConj_assoc] at hm)⟩

theorem SepLoad128.right {a : BitVec 64} {v : BitVec 128} {P Q : SepProp}
    (h : SepLoad128 a Q v) : SepLoad128 a (P ∗ Q) v :=
  ⟨fun hm => h.load (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm),
   fun hm => h.readable (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)⟩

structure SepStore128 (a : BitVec 64) (v' : BitVec 128) (P P' : SepProp) : Prop where
  store : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → (m.write128 a v' ⊨ P' ∗ R)
  writable : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.canWrite a 16 = true

theorem SepStore128.here {a a' : BitVec 64} {v v' : BitVec 128} (ha : a' = a) :
    SepStore128 a v' (a' ↦₁₂₈ v) (a' ↦₁₂₈ v') :=
  ha ▸ ⟨fun hm => (IsBlock.pointsTo128 a' v).write128 hm v',
        fun hm => (IsBlock.pointsTo128 a' v).canWrite (by decide) hm⟩

theorem SepStore128.here_region {a a' : BitVec 64} {v' : BitVec 128} (ha : a' = a) :
    SepStore128 a v' (memRegion a' 16) (a' ↦₁₂₈ v') :=
  ha ▸ ⟨fun hm => (IsBlock.memRegion a' 16).write128 hm v',
        fun hm => (IsBlock.memRegion a' 16).canWrite (by decide) hm⟩

theorem SepStore128.left {a : BitVec 64} {v' : BitVec 128} {P P' Q : SepProp}
    (h : SepStore128 a v' P P') : SepStore128 a v' (P ∗ Q) (P' ∗ Q) :=
  ⟨fun hm => by rw [sepConj_assoc] at hm ⊢; exact h.store hm,
   fun hm => h.writable (by rwa [sepConj_assoc] at hm)⟩

theorem SepStore128.right {a : BitVec 64} {v' : BitVec 128} {P Q Q' : SepProp}
    (h : SepStore128 a v' Q Q') : SepStore128 a v' (P ∗ Q) (P ∗ Q') :=
  ⟨fun hm => by
     rw [sepConj_comm P Q, sepConj_assoc] at hm
     rw [sepConj_comm P Q', sepConj_assoc]; exact h.store hm,
   fun hm => h.writable (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)⟩

theorem perm_write128 (m : Memory) (addr : BitVec 64) (val : BitVec 128) :
    (m.write128 addr val).perm = m.perm := by
  simp only [Memory.write128]
  exact (Memory.perm_write64 _ _ _).trans (Memory.perm_write64 _ _ _)

theorem step_ldrSimd128_128 {prog : Program} {target_pc pc ea : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v : BitVec 128}
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hload : SepLoad128 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read128 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 16 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .Q128 vt addr) s = s' := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hread, hcan, SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hm)

theorem step_ldpSimd128_128 {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 128}
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 16#64 = ea2)
    (hload1 : SepLoad128 ea P v1) (hload2 : SepLoad128 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 v1).writeVReg128 vt2 v2).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read128 ea = v1 := hload1.load hm
  have hread2 : s.mem.read128 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 16 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 16 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldpSimd .Q128 vt1 vt2 addr) s = s' := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hm)

theorem step_strSimd128_perm {prog : Program} {target_pc pc ea : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 128}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readVReg128 vt = val)
    (hstore : SepStore128 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write128 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 16 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = s'.setMem m' := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hval, hcan, SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (perm_write128 s.mem ea val)) hm'

theorem step_stpSimd128_perm {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 128}
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 16#64 = ea2)
    (hv1 : s.readVReg128 vt1 = v1) (hv2 : s.readVReg128 vt2 = v2)
    (hstore1 : SepStore128 ea v1 P P1) (hstore2 : SepStore128 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write128 ea v1; let m2 := m1.write128 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 16 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 16 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (perm_write128 s.mem ea v1)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((perm_write128 m1 ea2 v2).trans (perm_write128 s.mem ea v1))) hm2

scoped macro "close_addr128" : tactic => `(tactic| first | with_reducible rfl | bv_lin)

scoped syntax "solve_load128" : tactic
scoped macro_rules
  | `(tactic| solve_load128) => `(tactic| first
      | ((with_reducible apply SepLoad128.here); close_addr128)
      | ((with_reducible apply SepLoad128.left); solve_load128)
      | ((with_reducible apply SepLoad128.right); solve_load128))

scoped syntax "solve_store128" : tactic
scoped macro_rules
  | `(tactic| solve_store128) => `(tactic| first
      | ((with_reducible apply SepStore128.here); close_addr128)
      | ((with_reducible apply SepStore128.here_region); close_addr128)
      | ((with_reducible apply SepStore128.left); solve_store128)
      | ((with_reducible apply SepStore128.right); solve_store128))

scoped macro "wp_ldr128 " hf:term:max : tactic => `(tactic| (
  apply step_ldrSimd128_128 $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· solve_load128); (· wp_focus_close wp_norm_lhs); try wp_norm_state))

scoped macro "wp_ldp128 " hf:term:max : tactic => `(tactic| (
  apply step_ldpSimd128_128 $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | bv_lin))
  (· solve_load128); (· solve_load128); (· wp_focus_close wp_norm_lhs); try wp_norm_state))

scoped macro "wp_str128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_strSimd128_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store128)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

scoped macro "wp_stp128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stpSimd128_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs); (· solve_store128); (· solve_store128)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

/-! ## 2. 240-Byte `↦ₛ` / `memRegion` ↔ `roundKeys15At` & 60-Word Stack Bridges -/

private theorem unpack64_pair_eq_u128ToBytesLE (v : BitVec 128) :
    unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64) = u128ToBytesLE v := by
  simp only [unpack64, u128ToBytesLE, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits,
         by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem u128ToBytesLE_length (v : BitVec 128) : (u128ToBytesLE v).length = 16 := by simp [u128ToBytesLE]

theorem u128ToBytesLE_bytesToU128LE {bs : List (BitVec 8)} (h : bs.length = 16) :
    u128ToBytesLE (bytesToU128LE bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  simp only [u128ToBytesLE, bytesToU128LE, bytesToU32LE, u32OfBytesLE, u128OfU32sLE, List.ofFn_succ,
    List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ,
    List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits,
         by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem pointsTo128_eq_pointsToBytes (ptr : BitVec 64) (v : BitVec 128) :
    (ptr ↦₁₂₈ v) = (ptr ↦ₛ u128ToBytesLE v) := by
  rw [pointsTo128_split64, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      ← unpack64_pair_eq_u128ToBytesLE, pointsToBytes_append, unpack64_length]

/-- Decode 240 bytes into 15 little-endian 128-bit round keys. -/
@[expose] def bytesToRoundKeys15 (bs : List (BitVec 8)) : Vector (BitVec 128) 15 :=
  Vector.ofFn fun i : Fin 15 => bytesToU128LE ((bs.drop (16 * i.val)).take 16)

private theorem roundKeys15_toList_eq (rks : Vector (BitVec 128) 15) :
    rks.toList = [rks[0], rks[1], rks[2], rks[3], rks[4], rks[5], rks[6], rks[7],
      rks[8], rks[9], rks[10], rks[11], rks[12], rks[13], rks[14]] :=
  List.ext_getElem (by simp) fun i hi1 _ => by
    have hi : i < 15 := by simp at hi1; exact hi1
    interval_cases i <;> rfl

theorem roundKeys15Bytes_length (rks : Vector (BitVec 128) 15) :
    (roundKeys15Bytes rks).length = 240 := by
  simp [roundKeys15Bytes, roundKeys15_toList_eq, u128ToBytesLE_length]

theorem roundKeys15At_eq_pointsToBytes (ptr : BitVec 64) (rks : Vector (BitVec 128) 15) :
    roundKeys15At ptr rks = (ptr ↦ₛ roundKeys15Bytes rks) := by
  simp only [roundKeys15Bytes, roundKeys15_toList_eq, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  repeat rw [pointsToBytes_append, u128ToBytesLE_length]
  simp only [← pointsTo128_eq_pointsToBytes, BitVec.add_assoc]; rfl

theorem roundKeys15Bytes_bytesToRoundKeys15 {bs : List (BitVec 8)} (h : bs.length = 240) :
    roundKeys15Bytes (bytesToRoundKeys15 bs) = bs := by
  simp only [roundKeys15Bytes, bytesToRoundKeys15, roundKeys15_toList_eq, Vector.getElem_ofFn,
    Nat.reduceMul, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  have hc (k : Nat) (hk : 16 * k + 16 ≤ 240) :
      u128ToBytesLE (bytesToU128LE ((bs.drop (16 * k)).take 16)) = (bs.drop (16 * k)).take 16 :=
    u128ToBytesLE_bytesToU128LE (by simp [h]; omega)
  rw [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), hc 4 (by omega),
      hc 5 (by omega), hc 6 (by omega), hc 7 (by omega), hc 8 (by omega), hc 9 (by omega),
      hc 10 (by omega), hc 11 (by omega), hc 12 (by omega), hc 13 (by omega), hc 14 (by omega)]
  have hsplit (n : Nat) : (bs.drop n).take 16 ++ bs.drop (n + 16) = bs.drop n := by
    rw [← List.drop_drop, List.take_append_drop]
  have hd240 : bs.drop 240 = [] := List.drop_eq_nil_of_le (by omega)
  rw [← List.append_nil ((bs.drop 224).take 16), ← hd240]; simp only [hsplit]; rfl

theorem pointsToBytes240_eq_roundKeys15At {ptr : BitVec 64} {bs : List (BitVec 8)}
    (h : bs.length = 240) :
    (ptr ↦ₛ bs) = roundKeys15At ptr (bytesToRoundKeys15 bs) := by
  rw [roundKeys15At_eq_pointsToBytes, roundKeys15Bytes_bytesToRoundKeys15 h]

theorem roundKeys15At_entails_memRegion (ptr : BitVec 64) (rks : Vector (BitVec 128) 15) :
    roundKeys15At ptr rks ⊢ memRegion ptr 240 := by
  rw [roundKeys15At_eq_pointsToBytes, ← roundKeys15Bytes_length rks]
  exact pointsToBytes_entails_memRegion ptr (roundKeys15Bytes rks)

theorem memRegion240_eq_exists_roundKeys15At (ptr : BitVec 64) :
    memRegion ptr 240 = ∃∗ rks : Vector (BitVec 128) 15, roundKeys15At ptr rks := by
  have hb : ∀ rks : Vector (BitVec 128) 15,
      IsBlock (roundKeys15At ptr rks) ptr 240
        (fun m => 240 ≤ 2 ^ 64 ∧ m.readBytes ptr 240 = roundKeys15Bytes rks) := fun rks => by
    have hblk :=
      IsBlock.pointsToBytes_len (a := ptr) (bs := roundKeys15Bytes rks) (roundKeys15Bytes_length rks)
    rw [← roundKeys15At_eq_pointsToBytes] at hblk
    try rw [roundKeys15Bytes_length rks] at hblk
    exact hblk
  exact (IsBlock.memRegion ptr 240).eq (IsBlock.sepExists hb) fun m =>
    ⟨fun _ => ⟨bytesToRoundKeys15 (m.readBytes ptr 240), by decide,
      (roundKeys15Bytes_bytesToRoundKeys15 (Memory.readBytes_length m ptr 240)).symm⟩,
     fun _ => trivial⟩

/-- Byte representation of 60 little-endian `u32` words (`240` B). -/
@[expose] def words60Bytes (ws : Vector (BitVec 32) 60) : List (BitVec 8) :=
  (ws.toList.map u32ToBytesLE).flatten

/-- Flat 240-byte stack representation of the 60 `u32` words in `expand_key::<32, 15>`. -/
@[expose] def expandWords60At (base : BitVec 64) (ws : Vector (BitVec 32) 60) : SepProp :=
  base ↦ₛ words60Bytes ws

private theorem u32ToBytesLE_quad_eq (w0 w1 w2 w3 : BitVec 32) :
    u32ToBytesLE w0 ++ (u32ToBytesLE w1 ++ (u32ToBytesLE w2 ++ u32ToBytesLE w3)) =
      u128ToBytesLE (u128OfU32sLE w0 w1 w2 w3) := by
  simp only [u32ToBytesLE, u128ToBytesLE, u128OfU32sLE, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits,
         by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem words60_toList_chunks (ws : Vector (BitVec 32) 60) :
    (ws.toList.map u32ToBytesLE).flatten = roundKeys15Bytes (armv8PackRoundKeys ws) := by
  have h60 : ws.toList = List.ofFn (fun i : Fin 60 => ws[i.val]) :=
    List.ext_getElem (by simp) (fun i _ _ => by rw [List.getElem_ofFn]; rfl)
  rw [h60, roundKeys15Bytes, roundKeys15_toList_eq]
  simp only [armv8PackRoundKeys, Vector.getElem_ofFn, Nat.reduceMul, Nat.reduceAdd,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, ← u32ToBytesLE_quad_eq, List.append_assoc]

theorem expandWords60At_eq_roundKeys15At (base : BitVec 64) (ws : Vector (BitVec 32) 60) :
    expandWords60At base ws = roundKeys15At base (armv8PackRoundKeys ws) := by
  rw [expandWords60At, roundKeys15At_eq_pointsToBytes, words60Bytes, words60_toList_chunks]

private theorem map_u32ToBytesLE_flatten_len (xs : List (BitVec 32)) :
    (xs.map u32ToBytesLE).flatten.length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons w rest ih => simp [u32ToBytesLE, ih]; omega

private theorem expandWords60At_split_at (base : BitVec 64) (ws : Vector (BitVec 32) 60)
    {idx : Nat} (hidx : idx < 60) :
    expandWords60At base ws =
      (base ↦ₛ ((ws.toList.take idx).map u32ToBytesLE).flatten) ∗
      ((base + BitVec.ofNat 64 (4 * idx)) ↦₃₂ ws[idx]) ∗
      ((base + BitVec.ofNat 64 (4 * idx) + 4#64) ↦ₛ
        ((ws.toList.drop (idx + 1)).map u32ToBytesLE).flatten) := by
  have hlen : idx < ws.toList.length := by simpa using hidx
  have hsplit : ws.toList = ws.toList.take idx ++ (ws.toList[idx] :: ws.toList.drop (idx + 1)) := by
    conv => lhs; rw [← List.take_append_drop idx ws.toList]
    exact congrArg _ (List.drop_eq_getElem_cons hlen)
  have hget : ws.toList[idx] = ws[idx] := rfl
  have hu32 : u32ToBytesLE ws[idx] = unpack32 ws[idx] := rfl
  have hl4 : (u32ToBytesLE ws[idx]).length = 4 := rfl
  conv => lhs; rw [expandWords60At, words60Bytes, hsplit, hget, List.map_append, List.flatten_append,
    List.map_cons, List.flatten_cons, pointsToBytes_append, pointsToBytes_append,
    map_u32ToBytesLE_flatten_len, List.length_take_of_le (Nat.le_of_lt hlen),
    hl4, hu32, ← pointsTo32_eq_pointsToBytes]

theorem SepLoad32.of_expandWords60At {base ea : BitVec 64} {ws : Vector (BitVec 32) 60}
    {idx : Nat} {F : SepProp} (hidx : idx < 60)
    (hea : base + BitVec.ofNat 64 (4 * idx) = ea) :
    SepLoad32 ea (expandWords60At base ws ∗ F) ws[idx] := by
  subst hea
  let pre := base ↦ₛ ((ws.toList.take idx).map u32ToBytesLE).flatten
  let cell := (base + BitVec.ofNat 64 (4 * idx)) ↦₃₂ ws[idx]
  let suf := (base + BitVec.ofNat 64 (4 * idx) + 4#64) ↦ₛ
    ((ws.toList.drop (idx + 1)).map u32ToBytesLE).flatten
  have heq : expandWords60At base ws ∗ F = cell ∗ (pre ∗ suf ∗ F) := by
    rw [expandWords60At_split_at base ws hidx]
    change (pre ∗ cell ∗ suf) ∗ F = cell ∗ (pre ∗ suf ∗ F)
    sep_ac_rfl
  exact ⟨fun hm => (IsBlock.pointsTo32 _ _).read (by rwa [heq, sepConj_assoc] at hm),
    fun hm => (IsBlock.pointsTo32 _ _).canRead (by decide) (by rwa [heq, sepConj_assoc] at hm)⟩

theorem SepStore32.of_expandWords60At {base ea : BitVec 64} {ws : Vector (BitVec 32) 60}
    {idx : Nat} {v : BitVec 32} {F : SepProp} (hidx : idx < 60)
    (hea : base + BitVec.ofNat 64 (4 * idx) = ea) :
    SepStore32 ea v (expandWords60At base ws ∗ F)
      (expandWords60At base (ws.setIfInBounds idx v) ∗ F) := by
  subst hea
  let pre := base ↦ₛ ((ws.toList.take idx).map u32ToBytesLE).flatten
  let cell := (base + BitVec.ofNat 64 (4 * idx)) ↦₃₂ ws[idx]
  let cell' := (base + BitVec.ofNat 64 (4 * idx)) ↦₃₂ v
  let suf := (base + BitVec.ofNat 64 (4 * idx) + 4#64) ↦ₛ
    ((ws.toList.drop (idx + 1)).map u32ToBytesLE).flatten
  have heq1 : expandWords60At base ws ∗ F = cell ∗ (pre ∗ suf ∗ F) := by
    rw [expandWords60At_split_at base ws hidx]
    change (pre ∗ cell ∗ suf) ∗ F = cell ∗ (pre ∗ suf ∗ F)
    sep_ac_rfl
  have htake : (ws.setIfInBounds idx v).toList.take idx = ws.toList.take idx := by
    rw [Vector.toList_setIfInBounds, List.take_set_of_le (Nat.le_refl idx)]
  have hdrop : (ws.setIfInBounds idx v).toList.drop (idx + 1) = ws.toList.drop (idx + 1) := by
    rw [Vector.toList_setIfInBounds, List.drop_set_of_lt (Nat.lt_succ_self idx)]
  have hget : (ws.setIfInBounds idx v)[idx] = v := by simp
  have heq2 : expandWords60At base (ws.setIfInBounds idx v) ∗ F = cell' ∗ (pre ∗ suf ∗ F) := by
    rw [expandWords60At_split_at base (ws.setIfInBounds idx v) hidx, htake, hdrop, hget]
    change (pre ∗ cell' ∗ suf) ∗ F = cell' ∗ (pre ∗ suf ∗ F)
    sep_ac_rfl
  exact ⟨fun hm => by
      rw [heq1, sepConj_assoc] at hm
      rw [heq2, sepConj_assoc]
      exact (IsBlock.pointsTo32 _ _).write32 hm v,
    fun hm => (IsBlock.pointsTo32 _ _).canWrite (by decide) (by rwa [heq1, sepConj_assoc] at hm)⟩

/-! ## 3. Machine Code & Verification of `inv_expanded_keys::<15>` (30 Instructions) -/

/-- Exact 30 instruction words (`120` B) of `aes::armv8::expand::inv_expanded_keys::<15>`. -/
@[expose] def invExpandedKeys15Words : List (BitVec 32) :=
  [0xad460021#32, 0x3dc03822#32, 0xad450c24#32, 0x4e287800#32, 0x4e287821#32,
   0x4e287884#32, 0xad000002#32, 0x4e287862#32, 0xad440c25#32, 0xad010801#32,
   0x4e287860#32, 0xad430423#32, 0x4e2878a5#32, 0xad020004#32, 0x4e287860#32,
   0x4e287821#32, 0xad420823#32, 0xad030405#32, 0x4e287842#32, 0x4e287861#32,
   0xad411023#32, 0xad040800#32, 0xad401422#32, 0x4e287884#32, 0x4e287860#32,
   0x4e2878a3#32, 0x3d803802#32, 0xad051001#32, 0xad060c00#32, 0xd65f03c0#32]

/-- Decoded 30-instruction sequence of `aes::armv8::expand::inv_expanded_keys::<15>`. -/
@[expose] def invExpandedKeys15Instrs : List Instr := decodeWords invExpandedKeys15Words

theorem map_decode_eq_of_all_isSome : ∀ ws : List (BitVec 32),
    ws.all (fun w => (Arm64.decode w).isSome) = true →
    ws.map Arm64.decode = (decodeWords ws).map some
  | [], _ => rfl
  | w :: ws, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, decodeWords, decodeWord]
    cases hd : Arm64.decode w with
    | none => simp [hd] at h
    | some i => exact congrArg (some i :: ·) (map_decode_eq_of_all_isSome ws h.2)

theorem invExpandedKeys15Instrs_template_eq :
    invExpandedKeys15Words.map Arm64.decode = invExpandedKeys15Instrs.map some :=
  map_decode_eq_of_all_isSome _ (by decide)

/-- Hoare contract (`x0 = dkPtr`, `x1 = ekPtr`, disjoint `roundKeys15At` buffers) for
    `inv_expanded_keys::<15>`, preserving all GPRs (`sf.regs = s0.regs`), `sp`, `tpidrEl0`,
    and `PureStepPreserved s0 sf`. -/
@[expose] def invExpandedKeys15Spec :
    Spec (BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × Vector (BitVec 128) 15) where
  pre := fun (dkPtr, ekPtr, oldDk, ek) s0 =>
    ⌜s0.readReg64 .x0 = dkPtr ∧ s0.readReg64 .x1 = ekPtr⌝ ∗
    (roundKeys15At dkPtr oldDk ∗ roundKeys15At ekPtr ek)
  post := fun (dkPtr, ekPtr, _oldDk, ek) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
    (roundKeys15At dkPtr (armv8InvExpandedKeys ek) ∗ roundKeys15At ekPtr ek)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Region-destination Hoare contract (`memRegion dkPtr 240`) for `inv_expanded_keys::<15>`. -/
@[expose] def invExpandedKeys15RegionSpec :
    Spec (BitVec 64 × BitVec 64 × Vector (BitVec 128) 15) where
  pre := fun (dkPtr, ekPtr, ek) s0 =>
    ⌜s0.readReg64 .x0 = dkPtr ∧ s0.readReg64 .x1 = ekPtr⌝ ∗
    (memRegion dkPtr 240 ∗ roundKeys15At ekPtr ek)
  post := fun (dkPtr, ekPtr, ek) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
    (roundKeys15At dkPtr (armv8InvExpandedKeys ek) ∗ roundKeys15At ekPtr ek)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

namespace Simp
@[scoped simp] theorem regs_writeVReg128_eq (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).regs = s.regs := by cases s; rfl
@[scoped simp] theorem regs_setPC_eq (s : State) (pc : BitVec 64) :
    (s.setPC pc).regs = s.regs := by cases s; rfl
@[scoped simp] theorem regs_setMem_eq (s : State) (m : Memory) :
    (s.setMem m).regs = s.regs := by cases s; rfl
@[scoped simp] theorem mem_setMem_eq (s : State) (m : Memory) :
    (s.setMem m).mem = m := by cases s; rfl
end Simp
open scoped Simp

set_option maxHeartbeats 400000 in
private theorem invExpandedKeys15_sepWP {P : Program} {entry dkPtr ekPtr : BitVec 64}
    {oldDk ek : Vector (BitVec 128) 15} {R : SepProp} {s0 : State}
    (hc : hasInstrs P entry invExpandedKeys15Instrs)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dkPtr) (hx1 : s0.readReg64 .x1 = ekPtr) :
    SepWP P (s0.readReg64 Reg.lr) s0 (roundKeys15At dkPtr oldDk ∗ roundKeys15At ekPtr ek)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
            (roundKeys15At dkPtr (armv8InvExpandedKeys ek) ∗ roundKeys15At ekPtr ek)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  dsimp only [roundKeys15At]
  have_instrs hc 0 30
  wp_ldp128 hf_0; wp_ldr128 hf_1; wp_ldp128 hf_2
  wp_steps 3
  wp_stp128 hf_6 m1 hm1; wp_steps 1; wp_ldp128 hf_8; wp_stp128 hf_9 m2 hm2
  wp_steps 1; wp_ldp128 hf_11; wp_steps 1; wp_stp128 hf_13 m3 hm3
  wp_steps 2; wp_ldp128 hf_16; wp_stp128 hf_17 m4 hm4
  wp_steps 2; wp_ldp128 hf_20; wp_stp128 hf_21 m5 hm5; wp_ldp128 hf_22
  wp_steps 3; wp_str128 hf_26 m6 hm6; wp_stp128 hf_27 m7 hm7; wp_stp128 hf_28 m8 hm8
  wp_steps 1
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]),
      by simp [wp_norm, arm64_norm]⟩, ?_⟩
    simp only [Simp.mem_setMem_eq, evalAesOp_aesimc_vd_irrel] at hm ⊢
    dsimp only [roundKeys15At, armv8InvExpandedKeys]
    exact hm
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, *]

/-- Placement-generic `subroutine_ok` verification of `inv_expanded_keys::<15>`. -/
theorem invExpandedKeys15_subroutine_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invExpandedKeys15Instrs) :
    subroutine_ok P entry invExpandedKeys15Spec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dkPtr, ekPtr, oldDk, ek⟩ R s0 hpc hrun hpre _hsp
  dsimp only [invExpandedKeys15Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  exact ⟨_, hpre, invExpandedKeys15_sepWP hc hpc hrun hx0 hx1⟩

/-- Placement-generic `subroutine_ok` verification of `inv_expanded_keys::<15>` over
    `memRegion dkPtr 240`. -/
theorem invExpandedKeys15_region_subroutine_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry invExpandedKeys15Instrs) :
    subroutine_ok P entry invExpandedKeys15RegionSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dkPtr, ekPtr, ek⟩ R s0 hpc hrun hpre _hsp
  dsimp only [invExpandedKeys15RegionSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  refine ⟨memRegion dkPtr 240 ∗ roundKeys15At ekPtr ek, hpre, ?_⟩
  rw [memRegion240_eq_exists_roundKeys15At]
  exact SepWP.of_sepExists_left fun oldDk => invExpandedKeys15_sepWP hc hpc hrun hx0 hx1

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
