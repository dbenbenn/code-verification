/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.StdDetect
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.StdStartup.OutlineAtomics
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm

/-!
# Layout-Generic SPQR CPU-Feature Probe Proofs (`DEV-CLI10`)

Verifies the full SPQR lazy CPU-feature probe executed on unmodified ELF memory at the first
GF(2¹⁶) operation when `AT_HWCAP` has neither `HWCAP_AES` nor `HWCAP_PMULL` (`hwcap &&& 0x18 = 0`,
e.g. `0x3#64`):

1. `getauxval_found_ro_ok`: read-only-memory (`↦₆₄ᵣ`, `↦ᵣ`) contract for musl `getauxval`.
2. `getauxvalHwcap_ok`: `cpufeatures::aarch64::getauxval_hwcap` (`mov w0, #0x10; b getauxval`).
3. `spqrUseAcceleratedInit_ok`: `spqr::encoding::gf::check_accelerated::use_accelerated::init`
   transitioning `STORAGE.0` from `0xff#8` to `0#8`.
4. `spqrLazyLockClosure_wp`: SPQR `LazyLock` `call_once_force` closure taking `&TOKEN` from the
   caller's stack slot and tail-calling `use_accelerated::init`.
5. `onceCall198_incomplete_wp`: `rustc 1.98.1` `std::sys::sync::once::futex::Once::call` on the
   uncontended `INCOMPLETE` (`3#32` → `1#32` → `0#32`, `ignore_poisoning = true`) path using
   `cas4Acq_ok` and `swp4Rel_ok` with zero `futex` syscalls.
6. `spqrOnceCall_unprobed_ok`: end-to-end `subroutine_ok` contract for `Once::call` from any SPQR
   GF(2¹⁶) slow path.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.CpuProbe

open Arm64 Arm64.Obj ProofLib ProofLib.StdStartup

/-! ## 1. Read-Only `getauxval` Contract -/

/-- Read-only-memory contract for musl `getauxval(tag)` when `tag ≠ 0x17#64` (`AT_SECURE`) is
present in `entries` with non-zero tags. -/
@[expose] def stdGetauxvalRoSpec (L : StdBinaryLayout) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (tag, val, auxvAddr, entries) s0 =>
    ⌜s0.readReg64 (.gpr 0#5) = tag ∧ tag ≠ 0x17#64 ∧
      (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
      entries.find? (·.1 == tag) = some (tag, val)⌝ ∗
    (((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackFrameAt s0.sp 0x20)
  post := fun (_, val, auxvAddr, entries) s0 sf =>
    ⌜sf.readReg64 (.gpr 0#5) = val ∧ StdStatePreserved s0 sf⌝ ∗
    (((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackFrameAt s0.sp 0x20)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem pointsToBytesRO_encodeAuxvBytes_cons (ptr t v : BitVec 64)
    (rest : List (BitVec 64 × BitVec 64)) :
    (ptr ↦ᵣ encodeAuxvBytes ((t, v) :: rest)) =
      (ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ ((ptr + 16#64) ↦ᵣ encodeAuxvBytes rest) := by
  have heq : encodeAuxvBytes ((t, v) :: rest) =
      unpack64 t ++ (unpack64 v ++ encodeAuxvBytes rest) := by
    simp [encodeAuxvBytes_eq_flatMap_bytesLE]
    rfl
  rw [heq, pointsToBytesRO_append, pointsToBytesRO_append,
    ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
    unpack64_length, BitVec.add_assoc]
  rfl

private theorem step_str64_perm_cp {prog : Program} {target_pc pc ea val : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  let m' := s.mem.write64 ea val
  have hm' := hstore.store hm
  have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
        MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write64 s.mem ea val)
  unfold SepWP at hn
  exact hn R hm'

private theorem step_stp64_perm_cp {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm
  have hm2 := hstore2.store hm1
  have hcan1 := hstore1.writable hm
  have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2,
        hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))
  unfold SepWP at hn
  exact hn R hm2

private theorem step_str8_perm_cp {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP
  intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val
  have hm' := hstore.store hm
  have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;>
      simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
        State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
        MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write8 s.mem ea val)
  unfold SepWP at hn
  exact hn R hm'

section
arm64_proof_prelude

private theorem getauxval_scan_loop_ro (P : Program) (L : StdBinaryLayout)
    (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    {target_pc tag val : BitVec 64} {post : State → SepProp → Prop} {oom : State → SepProp}
    (entries : List (BitVec 64 × BitVec 64))
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hfind : entries.find? (·.1 == tag) = some (tag, val)) :
    ∀ (ptr : BitVec 64) (s : State) (F : SepProp),
      s.pc = L.getauxvalAddr + 0x1c#64 → s.status = .Running →
      s.readReg64 (.gpr 0#5) = tag → s.readReg64 (.gpr 1#5) = ptr →
      (∀ sf : State, sf.pc = L.getauxvalAddr + 0x54#64 → sf.status = .Running →
        sf.sp = s.sp → sf.readReg64 (.gpr 19#5) = val →
        CalleeSavedPreserved (s.writeReg64 (.gpr 19#5) val) sf → sf.mem = s.mem →
        ProcessFieldsPreserved s sf →
        SepWP P target_pc sf ((ptr ↦ᵣ encodeAuxvBytes entries) ∗ F) post oom) →
      SepWP P target_pc s ((ptr ↦ᵣ encodeAuxvBytes entries) ∗ F) post oom := by
  induction entries with
  | nil => intro _ _ _ _ _ _ _ _; simp at hfind
  | cons kv rest ih =>
    rcases kv with ⟨t, v⟩
    intro ptr s F hpc hrun hx0 hx1 hnext
    have ht0 : t ≠ 0#64 := hnonull t v (List.mem_cons_self ..)
    have_instrs hc 7 6
    have_instrs hc 16 2
    rw [pointsToBytesRO_encodeAuxvBytes_cons]
    wp_steps 3
    wp_if hcbz
    · exact absurd hcbz ht0
    · wp_step
      wp_if hbeq
      · subst hbeq
        simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hfind
        rcases hfind with ⟨_, rfl⟩
        wp_steps 2
        rw [← pointsToBytesRO_encodeAuxvBytes_cons]
        exact hnext _
          (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm])
          (ProcessFieldsPreserved.refl s)
      · simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hbeq] at hfind
        wp_steps 2
        have hassoc :
            (((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ ((ptr + 16#64) ↦ᵣ encodeAuxvBytes rest)) ∗ F) =
            ((ptr + 16#64) ↦ᵣ encodeAuxvBytes rest) ∗ ((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ F) := by
          apply Entails.antisymm <;> sep_entail
        rw [hassoc]
        refine ih (fun t' v' hm => hnonull t' v' (List.mem_cons_of_mem _ hm)) hfind
          (ptr + 16#64) _ _
          (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm, hx0])
          (by simp [wp_norm, arm64_norm])
          fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hmem_f hpf_f => ?_
        rw [← hassoc, ← pointsToBytesRO_encodeAuxvBytes_cons]
        exact hnext sf hpc_f hrun_f (by simpa [wp_norm, arm64_norm] using hsp_f) hx19_f
          (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
          (by simpa [wp_norm, arm64_norm] using hmem_f) hpf_f

/-- Read-only-memory counterpart of `ProofLib.StdStartup.getauxval_found_ok`. -/
theorem getauxval_found_ro_ok (P : Program) (L : StdBinaryLayout)
    (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L)) :
    subroutine_ok P L.getauxvalAddr (stdGetauxvalRoSpec L) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨tag, val, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [stdGetauxvalRoSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, htag17, hnonull, hfind⟩, hpre⟩
  refine ⟨((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x20 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [hsf]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have_instrs hc 0 7
  have_instrs hc 21 4
  refine step_stp64_perm_cp (ea2 := s0.sp - 24#64) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_steps 2
  refine step_str64_perm_cp (ea := s0.sp - 16#64) (wb := none)
    (val := s0.readReg64 (.gpr 19#5))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_3
    (by simp only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned,
      wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) fun m2 hm2 => ?_
  wp_step
  wp_if hbeq17
  · exact absurd (by simpa [wp_norm, arm64_norm, hx0] using hbeq17) htag17
  · wp_steps 2
    have hcomm : ∀ A B C : SepProp, (A ∗ B ∗ C) = (B ∗ A ∗ C) := fun A B C => by
      apply Entails.antisymm <;> sep_entail
    rw [hcomm]
    refine getauxval_scan_loop_ro P L hc entries hnonull hfind auxvAddr _ _
      (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hx0])
      (by simp [wp_norm, arm64_norm])
      fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hmem_f hpf_f => ?_
    rw [hcomm]
    have hsp_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hsp ⊢
      rw [hsp_f]
      simp only [wp_norm, arm64_norm] at *
      bv_bits
    wp_steps 4
    apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun_f])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      have hstd : StdStatePreserved s0 _ :=
        ⟨hpf_f.1, hpf_f.2.1, hpf_f.2.2.1, hpf_f.2.2.2.1, hpf_f.2.2.2.2.1, hpf_f.2.2.2.2.2.1,
          hpf_f.2.2.2.2.2.2.1,
          fun a => (hpf_f.2.2.2.2.2.2.2 a).trans ((congrFun hm2 a).trans (congrFun hm1 a))⟩
      refine ⟨⟨by simp [wp_norm, arm64_norm], hstd⟩, Satisfies.mono (sepConj_mono_left ?_) hm⟩
      rw [hsf]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
        (Entails.sepExists_right (s0.readReg64 (.gpr 30#5))
          (Entails.sepExists_right (s0.readReg64 (.gpr 19#5))
            (Entails.sepExists_right w3 (by sep_entail))))
    · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with
        ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
      simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
      rw [CalleeSavedPreserved.iff_regs]
      simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

/-! ## 2. `cpufeatures::aarch64::getauxval_hwcap` (2 insns) -/

/-- Parametric 2-instruction template for `cpufeatures::aarch64::getauxval_hwcap` at `addr`. -/
@[expose] def getauxvalHwcapInstrs (L : StdBinaryLayout) (addr : BitVec 64) : List Instr :=
  [ .moveWide .W32 .MOVZ (.gpr 0#5) 0x10#16 0,
    .b (L.getauxvalAddr - (addr + 4#64)) ]

/-- Contract for `cpufeatures::aarch64::getauxval_hwcap` returning `AT_HWCAP` (`tag = 16#64`)
from the read-only auxiliary vector. -/
@[expose] def getauxvalHwcapSpec (L : StdBinaryLayout) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, auxvAddr, entries) s0 =>
    ⌜(∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
      entries.find? (·.1 == 16#64) = some (16#64, hwcap)⌝ ∗
    (((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackFrameAt s0.sp 0x20)
  post := fun (hwcap, auxvAddr, entries) s0 sf =>
    ⌜sf.readReg64 (.gpr 0#5) = hwcap ∧ StdStatePreserved s0 sf⌝ ∗
    (((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackFrameAt s0.sp 0x20)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem getauxvalHwcap_ok (P : Program) (L : StdBinaryLayout) (addr : BitVec 64)
    (hc : hasInstrs P addr (getauxvalHwcapInstrs L addr))
    (hget : subroutine_ok P L.getauxvalAddr (stdGetauxvalRoSpec L)) :
    subroutine_ok P addr (getauxvalHwcapSpec L) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [getauxvalHwcapSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hnonull, hfind⟩, hpre⟩
  refine ⟨((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have_instrs hc 0 2
  wp_steps 2
  have hpc_get : (addr + 4#64) + (L.getauxvalAddr - (addr + 4#64)) = L.getauxvalAddr := by bv_lin
  refine SepWP.call_subroutine_frame (ret_pc := s0.readReg64 .lr) hget
    (x := (16#64, hwcap, auxvAddr, entries)) (F := emp)
    (by simp [wp_norm, arm64_norm, hpc_get])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp)
    (by simp [wp_norm, arm64_norm])
    ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf hpc_f hrun_f hsp_f hcs_f => ?_
  · intro R' hm
    dsimp only [stdGetauxvalRoSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by decide, hnonull, hfind⟩, ?_⟩
    exact Satisfies.mono (by sep_entail) hm
  · dsimp only [stdGetauxvalRoSpec]
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0_f, hstd_f⟩
    apply SepWP.done hpc_f hrun_f
    refine ⟨fun hm => ?_, by simpa [wp_norm, arm64_norm] using hsp_f, ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_f, hstd_f⟩, Satisfies.mono (by sep_entail) hm⟩
    · exact CalleeSavedPreserved.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f

/-! ## 3. `spqr::encoding::gf::check_accelerated::use_accelerated::init` (17 insns) -/

/-- Parametric 17-instruction template for `spqr::encoding::gf::check_accelerated::use_accelerated::init`
at `initAddr`, reading/writing `storageAddr` (`STORAGE.0`) and calling `hwcapAddr`. -/
@[expose] def spqrUseAcceleratedInitInstrs (initAddr storageAddr hwcapAddr : BitVec 64) :
    List Instr :=
  decodeWords [0xa9be7bfd#32, 0xf9000bf3#32, 0x910003fd#32] ++
  [ .adr true (.gpr 19#5) (adrpOff (initAddr + 0x0c#64) storageAddr),
    .ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 storageAddr)) ] ++
  decodeWords [0x7103fd1f#32, 0x54000080#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32] ++
  [ .bl (hwcapAddr - (initAddr + 0x28#64)) ] ++
  decodeWords [0xf27d041f#32, 0x1a9f07e8#32] ++
  [ .str .B8 (.gpr 8#5) (.Offset (.gpr 19#5) (pageLo12 storageAddr)) ] ++
  decodeWords [0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32]

/-- Byte written to `use_accelerated::STORAGE.0` by `use_accelerated::init` for `AT_HWCAP = hwcap`:
`1#8` when either `HWCAP_AES` (`bit 3`) or `HWCAP_PMULL` (`bit 4`) is set, else `0#8`. -/
@[expose] def spqrStorageOfHwcap (hwcap : BitVec 64) : BitVec 8 :=
  if (hwcap &&& 0x18#64) == 0#64 then 0#8 else 1#8

/-- Contract for `use_accelerated::init` on unprobed `STORAGE.0 = 0xff#8`: stores
`spqrStorageOfHwcap hwcap` (`1#8` when `AT_HWCAP` has `HWCAP_AES` or `HWCAP_PMULL`, else `0#8`)
into `STORAGE.0`. -/
@[expose] def spqrUseAcceleratedInitSpec (L : StdBinaryLayout) (storageAddr : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (hwcap, auxvAddr, entries) s0 =>
    ⌜(∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
      entries.find? (·.1 == 16#64) = some (16#64, hwcap)⌝ ∗
    ((storageAddr ↦₈ 0xff#8) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40)
  post := fun (hwcap, auxvAddr, entries) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    ((storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem stackAt_64_eq_20_20 (sp : BitVec 64) :
    stackAt sp 0x40 =
      stackFrameAt (sp - 0x20#64) 0x20 ∗ stackFrameAt sp 0x20 := by
  rw [← stackAt_eq_stackFrameAt sp 0x20, ← stackAt_eq_stackFrameAt (sp - 0x20#64) 0x20]
  have hs := stackAt_split_bottom sp 0x20 0x20 (by decide)
  simpa [stackAt, BitVec.sub_sub] using hs

private theorem adrp_pageLo12_cp (pc tgt : BitVec 64) :
    ((pc &&& ~~~4095#64) + adrpOff pc tgt) + pageLo12 tgt = tgt := by
  unfold adrpOff pageLo12
  bv_bits

theorem spqrUseAcceleratedInit_ok (P : Program) (L : StdBinaryLayout)
    (initAddr storageAddr hwcapAddr : BitVec 64)
    (hc : hasInstrs P initAddr (spqrUseAcceleratedInitInstrs initAddr storageAddr hwcapAddr))
    (hhw : subroutine_ok P hwcapAddr (getauxvalHwcapSpec L)) :
    subroutine_ok P initAddr (spqrUseAcceleratedInitSpec L storageAddr) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [spqrUseAcceleratedInitSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hnonull, hfind⟩, hpre⟩
  refine ⟨(storageAddr ↦₈ 0xff#8) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0x40, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x20 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [stackAt_64_eq_20_20, hsf]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have_instrs hc 0 7
  have_instrs hc 10 7
  refine step_stp64_perm_cp (ea2 := s0.sp - 24#64) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  refine step_str64_perm_cp (ea := s0.sp - 16#64) (wb := none)
    (val := s0.readReg64 (.gpr 19#5))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf_1
    (by simp only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned,
      wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) fun m2 hm2 => ?_
  wp_steps 6
  have hpc_hw : (initAddr + 40#64) + (hwcapAddr - (initAddr + 40#64)) = hwcapAddr := by bv_lin
  refine SepWP.call_subroutine_frame (ret_pc := initAddr + 44#64) hhw
    (x := (hwcap, auxvAddr, entries))
    (F := (storageAddr ↦₈ 0xff#8) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3))
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [getauxvalHwcapSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hnonull, hfind⟩, ?_⟩
      simp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (by sep_entail)) hm)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun s1 hpc1 hrun1 hsp1 hcs1 => ?_
  dsimp only [getauxvalHwcapSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hx0_1, hstd1⟩
  have hx19_1 : s1.readReg64 (.gpr 19#5) =
      ((initAddr + 12#64) &&& ~~~4095#64) + adrpOff (initAddr + 12#64) storageAddr := by
    rw [hcs1.readReg64_x19]
    simp [wp_norm, arm64_norm]
  have hsp1_eq : s1.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm] using hsp1
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]
    exact s0.spAligned_sub 32#64 hsp
  wp_steps 2
  refine step_str8_perm_cp (ea := storageAddr) (wb := none) (val := spqrStorageOfHwcap hwcap)
    (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
    hf_13 rfl
    (by simp [evalAddrMode, wp_norm, arm64_norm, hx19_1])
    (by simp only [spqrStorageOfHwcap, wp_norm, arm64_norm])
    (by wp_sep_access) fun m3 hm3 => ?_
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hstd1.1, hstd1.2.1, hstd1.2.2.1, hstd1.2.2.2.1, hstd1.2.2.2.2.1, hstd1.2.2.2.2.2.1,
      hstd1.2.2.2.2.2.2.1,
      fun a => (congrFun hm3 a).trans ((hstd1.2.2.2.2.2.2.2 a).trans
        ((congrFun hm2 a).trans (congrFun hm1 a)))⟩, ?_⟩
    rw [stackAt_64_eq_20_20, hsf]
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
    refine Entails.trans
      (Q := (storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
        (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackFrameAt (s0.sp - 32#64) 32 ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3)))
      (by sep_entail) ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
    exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
      (Entails.sepExists_right (s0.readReg64 (.gpr 30#5))
        (Entails.sepExists_right (s0.readReg64 (.gpr 19#5))
          (Entails.sepExists_right w3 (by sep_entail))))
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with
      ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]
    simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

/-! ## 4. SPQR `LazyLock` Closure (`0x00..0x2c`, 12 position-independent words) -/

/-- Exact 12-instruction hot path of SPQR's `LazyLock::force` `call_once_force` closure. -/
@[expose] def spqrLazyLockClosureWords : List (BitVec 32) :=
  [ 0xa9bf7bfd#32, 0x910003fd#32, 0xf9400009#32, 0xf9400128#32,
    0xf900013f#32, 0xb40000e8#32, 0x39401029#32, 0x7100053f#32,
    0x540000e0#32, 0xf9400100#32, 0xa8c17bfd#32, 0xd61f0000#32 ]

theorem spqrLazyLockClosure_wp {P : Program} {L : StdBinaryLayout}
    {closureAddr initAddr storageAddr target_pc ret_pc dataPtr slotPtr tokenAddr finishPtr : BitVec 64}
    {hwcap auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcode : P.hasWords closureAddr spqrLazyLockClosureWords)
    (hinit : subroutine_ok P initAddr (spqrUseAcceleratedInitSpec L storageAddr))
    (hpc : s.pc = closureAddr) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = dataPtr)
    (hx1 : s.readReg64 .x1 = finishPtr) (htok_nz : tokenAddr ≠ 0#64)
    (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hfind : entries.find? (·.1 == 16#64) = some (16#64, hwcap))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf
        ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ 0#64) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
          ((finishPtr + 4#64) ↦₈ 0#8) ∗ (storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗
          ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗ (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
          stackAt s.sp 0x40 ∗ F) post oom) :
    SepWP P target_pc s
      ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
        ((finishPtr + 4#64) ↦₈ 0#8) ∗ (storageAddr ↦₈ 0xff#8) ∗
        ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗ (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
        stackAt s.sp 0x40 ∗ F) post oom := by
  have hcode' : P.hasCode closureAddr spqrLazyLockClosureWords := hcode
  have hstk_split : stackAt s.sp 0x40 =
      stackAt (s.sp - 0x10#64) 0x30 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((s.sp - 0x10#64) ↦₆₄ w0) ∗ ((s.sp - 0x08#64) ↦₆₄ w1)) := by
    have h1 := stackAt_split_bottom s.sp 0x10 0x30 (by decide)
    have h2 : stackAt s.sp 0x10 =
        (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
          ((s.sp - 0x10#64) ↦₆₄ w0) ∗ ((s.sp - 0x08#64) ↦₆₄ w1)) := by
      rw [stackAt_eq_stackFrameAt s.sp 0x10]
      simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
    simpa [stackAt, BitVec.sub_sub, h2] using h1
  wp_conv_pre => rw [hstk_split]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  wp_steps 12
  have hstk_back :
      (stackAt (s.sp - 0x10#64) 0x30 ∗
        ((s.sp - 0x10#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
        ((s.sp - 0x08#64) ↦₆₄ ret_pc)) ⊢ stackAt s.sp 0x40 := by
    rw [hstk_split]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right (s.readReg64 (.gpr 29#5))
      (Entails.sepExists_right ret_pc (Entails.refl _))
  refine SepWP.call_subroutine_frame (ret_pc := ret_pc) hinit
    (x := (hwcap, auxvAddr, entries))
    (F := (dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ 0#64) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((finishPtr + 4#64) ↦₈ 0#8) ∗ F)
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_al)
    (by simp [wp_norm, arm64_norm])
    (fun _ hm => by
      dsimp only [spqrUseAcceleratedInitSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hnonull, hfind⟩, ?_⟩
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right hstk_back))))
      simp only [wp_norm, arm64_norm, bv_lin_norm]
      sep_entail)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf hpc_f hrun_f hsp_f hcs_f => ?_
  dsimp only [spqrUseAcceleratedInitSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hstd_f
  refine SepWP.weaken_pre (by simp only [wp_norm, arm64_norm, bv_lin_norm]; sep_entail)
    (hnext sf hpc_f hrun_f (by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_f)
      (CalleeSavedPreserved.trans (by simp [CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
      (StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm]) hstd_f.toFields))

/-! ## 5. `rustc 1.98.1` `std::sys::sync::once::futex::Once::call` (`w1 = 1`, `3 → 1 → 0`) -/

/-- Entry words (`+0x00..+0x5c`, 24 insns) of `rustc 1.98.1` `futex::Once::call`. -/
@[expose] def onceCall198EntryWords : List (BitVec 32) :=
  [ 0xd10183ff#32, 0xa9027bfd#32, 0xa9035ff8#32, 0xa90457f6#32,
    0xa9054ff4#32, 0x910083fd#32, 0x910023e8#32, 0x88dffc16#32,
    0xaa0303f5#32, 0xaa0203f4#32, 0xaa0003f3#32, 0x91002118#32,
    0x37000081#32, 0xaa0403f7#32, 0x14000049#32, 0x88dffe76#32,
    0x120006d7#32, 0x51000ae8#32, 0x7100091f#32, 0x121e02c8#32,
    0x540001a2#32, 0x32000101#32, 0x2a1603e0#32, 0xaa1303e2#32 ]

/-- Parametric code chunks for the uncontended `INCOMPLETE` (`w1 = 1`) path of `rustc 1.98.1`
`std::sys::sync::once::futex::Once::call`. -/
@[expose] def onceCall198Chunks (onceCallAddr cas4AcqAddr swp4RelAddr : BitVec 64) :
    List CodeChunk :=
  [ .words onceCallAddr onceCall198EntryWords,
    .instrs onceCallAddr 0x60 [.bl (cas4AcqAddr - (onceCallAddr + 0x60#64))],
    .words (onceCallAddr + 0x64#64) [0x6b16001f#32, 0x540004a0#32],
    .words (onceCallAddr + 0xfc#64)
      [ 0x71000aff#32, 0x1a9f17e8#32, 0xf94012a9#32, 0xb9000bff#32,
        0x390033e8#32, 0x910023e1#32, 0xaa1403e0#32, 0xd63f0120#32,
        0xb9400be0#32, 0xaa1303e1#32 ],
    .instrs onceCallAddr 0x124 [.bl (swp4RelAddr - (onceCallAddr + 0x124#64))],
    .words (onceCallAddr + 0x128#64) [0x361000c0#32],
    .words (onceCallAddr + 0x140#64)
      [ 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32,
        0x910183ff#32, 0xd65f03c0#32 ] ]

/-- Code-chunk predicate for `rustc 1.98.1` `futex::Once::call`. -/
@[expose] def OnceCall198Code (P : Program) (onceCallAddr cas4AcqAddr swp4RelAddr : BitVec 64) :
    Prop :=
  CodeChunks P (onceCall198Chunks onceCallAddr cas4AcqAddr swp4RelAddr)

private theorem step_ldar32_words_cp {prog : Program} {target_pc : BitVec 64}
    (addr : BitVec 64) (words : List (BitVec 32))
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w : BitVec 32} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (i : Nat) (next_pc : BitVec 64) (halign : MemWidth.isAligned .W32 ea = true)
    (rt' : Reg) (hw : prog.hasCode addr words)
    (hget : words[i]? = some w := by rfl)
    (hdec : decode w = some (.ldarStlr .W32 true rn rt) := by rfl)
    (hrt : rt = rt' := by decide) (hrn : rn ≠ .sp := by decide)
    (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by
      simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (haddr : s.readReg64 rn = ea := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hload : SepLoad32 ea P v := by wp_sep_access_fast)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt' (v.zeroExtend 64)).setPC next_pc) P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hrt hpc_next
  have hsp : checkRegSPAligned s rn = true := by cases rn <;> simp_all [checkRegSPAligned]
  apply SepWP.weaken_pre_frame (P' := ⌜s.mem.read32 ea = v ∧ s.mem.canRead ea 4 = true⌝ ∗ P)
  · intro R hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hload.load hm, hload.readable hm⟩, hm⟩
  · apply SepWP.pure_elim
    rintro ⟨hread, hcan⟩
    refine SepWP.step_pure
      (s' := (s.writeReg64 rt (v.zeroExtend 64)).setPC (addr + BitVec.ofNat 64 (4 * (i + 1))))
      hpc hrun (Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec) ?_ rfl hnext
    have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by
      cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
    have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
    rw [hs_eq]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

private theorem pointsTo8_combine32_sub_cp (sp o0 o1 o2 o3 : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl)
    (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R =
      ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3
  simpa only [sepConj_assoc,
    show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin,
    show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin,
    show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin] using
    congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)

private theorem pointsTo32_split8_sub_cp (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32)
    (R : SepProp) (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl)
    (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R =
      ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗
        ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [pointsTo8_combine32_sub_cp sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3,
    show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by
      bv_bits]

private theorem combine_cell_byte4_sat_cp (sp o8 o4 o3 o2 o1 : BitVec 64) {lo : BitVec 32}
    {b0 b1 b2 b3 : BitVec 8} {m : Memory} {P R : SepProp} (hm : m ⊨ P)
    (hf : P = (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
      ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) ∗ R := by sep_focus)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl)
    (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) :
    m ⊨ (((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) ∗ R) := by
  rwa [hf, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    pointsTo8_combine32_sub_cp sp o4 o3 o2 o1 b0 b1 b2 b3 R h1 h2 h3,
    pointsTo32_combine64_sub sp o8 o4 lo _ R h4] at hm

/-- Uncontended `INCOMPLETE` (`3#32` → `1#32` → `0#32`) `SepWP` contract for `rustc 1.98.1`
`std::sys::sync::once::futex::Once::call` with `ignore_poisoning = true` (`w1 = 1#32`). -/
theorem onceCall198_incomplete_wp {P : Program}
    {onceCallAddr cas4AcqAddr swp4RelAddr haveLseAddr target_pc ret_pc sp0
      onceAddr dataPtr vtableAddr closureAddr : BitVec 64}
    {haveLse : BitVec 8} {s : State} {Pre Post F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : OnceCall198Code P onceCallAddr cas4AcqAddr swp4RelAddr)
    (hcas : subroutine_ok P cas4AcqAddr (stdCas4Spec haveLseAddr))
    (hswp : subroutine_ok P swp4RelAddr (stdSwp4Spec haveLseAddr))
    (hpc : s.pc = onceCallAddr) (hrun : s.status = .Running) (hsp : s.sp = sp0)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = onceAddr) (hx1 : (s.readReg64 .x1).truncate 32 = 1#32)
    (hx2 : s.readReg64 .x2 = dataPtr) (hx3 : s.readReg64 .x3 = vtableAddr)
    (halign : MemWidth.isAligned .W32 onceAddr = true)
    (hclosure : ∀ sc : State, ∀ G : SepProp,
      sc.pc = closureAddr → sc.status = .Running → sc.sp = sp0 - 0x60#64 →
      sc.spAligned = true → sc.readReg64 Reg.lr = onceCallAddr + 0x11c#64 →
      sc.readReg64 .x0 = dataPtr → sc.readReg64 .x1 = sp0 - 0x58#64 →
      StdFieldsPreserved s sc →
      (∀ sr : State, sr.pc = onceCallAddr + 0x11c#64 → sr.status = .Running →
        sr.sp = sc.sp → CalleeSavedPreserved sc sr → StdFieldsPreserved sc sr →
        SepWP P target_pc sr
          ((haveLseAddr ↦₈ᵣ haveLse) ∗ ((sp0 - 0x58#64) ↦₃₂ 0#32) ∗
            ((sp0 - 0x54#64) ↦₈ 0#8) ∗ Post ∗ G) post oom) →
      SepWP P target_pc sc
        ((haveLseAddr ↦₈ᵣ haveLse) ∗ ((sp0 - 0x58#64) ↦₃₂ 0#32) ∗
          ((sp0 - 0x54#64) ↦₈ 0#8) ∗ Pre ∗ G) post oom)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s sf → StdFieldsPreserved s sf →
      SepWP P target_pc sf
        ((onceAddr ↦₃₂ 0#32) ∗ (haveLseAddr ↦₈ᵣ haveLse) ∗
          ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗ stackAt sp0 0x60 ∗ Post ∗ F) post oom) :
    SepWP P target_pc s
      ((onceAddr ↦₃₂ 3#32) ∗ (haveLseAddr ↦₈ᵣ haveLse) ∗
        ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗ stackAt sp0 0x60 ∗ Pre ∗ F) post oom := by
  subst hsp
  dsimp only [OnceCall198Code, onceCall198Chunks, CodeChunks, CodeChunk.holds] at hc
  rcases hc with ⟨hw_entry, hi_cas, hw_mid, hw_call, hi_swp, hw_tbz, hw_epi⟩
  have hcode_entry : P.hasCode onceCallAddr onceCall198EntryWords := hw_entry
  have hf_cas : P.fetch (onceCallAddr + 0x60#64) =
      some (.bl (cas4AcqAddr - (onceCallAddr + 0x60#64))) := by
    simpa using hi_cas.fetch_at_zero
  have hcode_mid : P.hasCode (onceCallAddr + 0x64#64) [0x6b16001f#32, 0x540004a0#32] := hw_mid
  have hcode_call : P.hasCode (onceCallAddr + 0xfc#64)
      [ 0x71000aff#32, 0x1a9f17e8#32, 0xf94012a9#32, 0xb9000bff#32,
        0x390033e8#32, 0x910023e1#32, 0xaa1403e0#32, 0xd63f0120#32,
        0xb9400be0#32, 0xaa1303e1#32 ] := hw_call
  have hf_swp : P.fetch (onceCallAddr + 0x124#64) =
      some (.bl (swp4RelAddr - (onceCallAddr + 0x124#64))) := by
    simpa using hi_swp.fetch_at_zero
  have hcode_tbz : P.hasCode (onceCallAddr + 0x128#64) [0x361000c0#32] := hw_tbz
  have hcode_epi : P.hasCode (onceCallAddr + 0x140#64)
      [ 0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32,
        0x910183ff#32, 0xd65f03c0#32 ] := hw_epi
  rw [stackAt_eq_cells s.sp 12]
  simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 12 (apply SepWP.exists_left; intro _)
  rw [pointsTo64_split32_sub s.sp 88#64 84#64, pointsTo32_split8_sub_cp s.sp 84#64 83#64 82#64 81#64]
  wp_steps 7
  refine step_ldar32_words_cp onceCallAddr onceCall198EntryWords 7 (onceCallAddr + 0x20#64)
    halign (.gpr 22#5) hcode_entry (hnext := ?_)
  have hx1_bit0 : (s.readReg64 .x1).getLsbD 0 = true := by
    have h0 := congrArg (fun x : BitVec 32 => x.getLsbD 0) hx1
    simpa [BitVec.truncate, BitVec.getLsbD_setWidth] using h0
  wp_steps; wp_steps
  refine call_stdCas4 hcas (haveLse := haveLse) (ptr := onceAddr) (v0 := 3#32) (exp := 3#32)
    (new := 1#32) (ret_pc := onceCallAddr + 0x64#64) (F := ?_) (by sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm])
    (hsp_align := by
      simp only [State.spAligned, wp_norm, arm64_norm]
      simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x60#64 hsp_align)
    (halign := halign)
  simp only [beq_self_eq_true, ↓reduceIte]
  have hx19_1 : s1.readReg64 .x19 = onceAddr := by
    rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hx20_1 : s1.readReg64 .x20 = dataPtr := by
    rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
  have hx21_1 : s1.readReg64 .x21 = vtableAddr := by
    rw [hcs1.readReg64_x21]; simp [wp_norm, arm64_norm]
  have hx22_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 := by
    have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this
  have hx23_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 := by
    have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this
  have hsp1_eq : s1.sp = s.sp - 0x60#64 := by rw [hsp1]; simp [wp_norm, arm64_norm, bv_lin_norm]
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  have hstd_s1 : StdFieldsPreserved s s1 :=
    StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm]) hstd1.toFields
  wp_steps; wp_steps
  refine SepWP.weaken_pre
    (P' := (haveLseAddr ↦₈ᵣ haveLse) ∗ ((s.sp - 0x58#64) ↦₃₂ 0#32) ∗
      ((s.sp - 0x54#64) ↦₈ 0#8) ∗ Pre ∗ ?G) (by sep_frame)
    (hclosure _ ?G
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1_eq])
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (StdFieldsPreserved.trans hstd_s1 (by simp [StdFieldsPreserved, wp_norm, arm64_norm]))
      fun s2 hpc2 hrun2 hsp2 hcs2 hstd2 => ?_)
  have hx19_2 : s2.readReg64 .x19 = onceAddr := by
    rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
  have hsp2_eq : s2.sp = s.sp - 0x60#64 := by
    rw [hsp2]; simp [wp_norm, arm64_norm, hsp1_eq]
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  wp_steps
  refine call_stdSwp4 hswp (haveLse := haveLse) (ptr := onceAddr) (v0 := 1#32) (new := 0#32)
    (ret_pc := onceCallAddr + 0x128#64) (F := ?_) (by sep_frame)
    (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_)
    (hpc := by simp [wp_norm, arm64_norm, bv_lin_norm])
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
    (halign := halign)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := by simpa [Reg.x0] using hx0_3
  have hsp3_eq : s3.sp = s.sp - 0x60#64 := by
    rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by
    simp only [State.spAligned, hsp3_eq]; exact s.spAligned_sub 0x60#64 hsp_align
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame (fun _ hm => ?_)
    (hnext _ (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun3])
      (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by
        rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with
          ⟨_, _, _, _, _, _, g25_1, g26_1, g27_1, g28_1, _, gv_1⟩
        rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with
          ⟨_, _, _, _, _, _, g25_2, g26_2, g27_2, g28_2, _, gv_2⟩
        rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with
          ⟨_, _, _, _, _, _, g25_3, g26_3, g27_3, g28_3, _, gv_3⟩
        simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm,
          g25_1, g26_1, g27_1, g28_1, gv_1,
          g25_2, g26_2, g27_2, g28_2, gv_2,
          g25_3, g26_3, g27_3, g28_3, gv_3])
      (StdFieldsPreserved.trans hstd_s1
        (StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm])
          (StdFieldsPreserved.trans hstd2
            (StdFieldsPreserved.trans (by simp [StdFieldsPreserved, wp_norm, arm64_norm])
              (StdFieldsPreserved.trans hstd3.toFields
                (by simp [StdFieldsPreserved, wp_norm, arm64_norm])))))))
  replace hm := combine_cell_byte4_sat_cp s.sp 88#64 84#64 83#64 82#64 81#64 hm
  rw [stackAt_eq_cells s.sp 12]
  simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail

/-! ## 6. End-to-End SPQR CPU-Probe Contract (`Once::call` from any SPQR slow path) -/

/-- Code bundle for the complete SPQR CPU-feature probe chain (`Once::call`, `__aarch64_cas4_acq`,
`__aarch64_swp4_rel`, SPQR `LazyLock` closure, `use_accelerated::init`, `getauxval_hwcap`, and
musl `getauxval`). -/
structure SpqrCpuProbeCode (P : Program) (L : StdBinaryLayout)
    (onceCallAddr closureAddr initAddr storageAddr hwcapAddr : BitVec 64) : Prop where
  onceCall : OnceCall198Code P onceCallAddr L.cas4AcqAddr L.swp4RelAddr
  cas4Acq : hasInstrs P L.cas4AcqAddr (cas4AcqInstrs L)
  swp4Rel : hasInstrs P L.swp4RelAddr (swp4RelInstrs L)
  closure : P.hasWords closureAddr spqrLazyLockClosureWords
  useAccelInit : hasInstrs P initAddr (spqrUseAcceleratedInitInstrs initAddr storageAddr hwcapAddr)
  hwcap : hasInstrs P hwcapAddr (getauxvalHwcapInstrs L hwcapAddr)
  getauxval : hasInstrs P L.getauxvalAddr (getauxvalInstrs L)

/-- End-to-end `subroutine_ok` specification for `Once::call` called from any of SPQR's 14
GF(2¹⁶) slow paths when unprobed (`STORAGE.0 = 0xff#8`, `TOKEN + 8 = 3#32`): probes `AT_HWCAP`
from the auxiliary vector and sets `STORAGE.0` to `spqrStorageOfHwcap hwcap` (`1#8` when `HWCAP_AES`
or `HWCAP_PMULL` is set, else `0#8`) and `TOKEN + 8` to `0#32`. -/
@[expose] def spqrOnceCallUnprobedSpec (L : StdBinaryLayout)
    (storageAddr tokenAddr vtableAddr closureAddr initAddr : BitVec 64) :
    Spec (BitVec 8 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64)) where
  pre := fun (haveLse, dataPtr, slotPtr, hwcap, auxvAddr, entries) s0 =>
    ⌜s0.readReg64 .x0 = tokenAddr + 8#64 ∧
      (s0.readReg64 .x1).truncate 32 = 1#32 ∧
      s0.readReg64 .x2 = dataPtr ∧
      s0.readReg64 .x3 = vtableAddr ∧
      MemWidth.isAligned .W32 (tokenAddr + 8#64) = true ∧
      tokenAddr ≠ 0#64 ∧
      (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
      entries.find? (·.1 == 16#64) = some (16#64, hwcap)⌝ ∗
    ((storageAddr ↦₈ 0xff#8) ∗
      ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗
      (dataPtr ↦₆₄ slotPtr) ∗
      (slotPtr ↦₆₄ tokenAddr) ∗
      (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗
      (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0xa0)
  post := fun (haveLse, dataPtr, slotPtr, hwcap, auxvAddr, entries) s0 sf =>
    ⌜StdFieldsPreserved s0 sf⌝ ∗
    ((storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗
      ((tokenAddr + 8#64) ↦₃₂ 0#32) ∗
      (dataPtr ↦₆₄ slotPtr) ∗
      (slotPtr ↦₆₄ 0#64) ∗
      (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗
      (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0xa0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem stackAt_a0_eq_60_40 (sp : BitVec 64) :
    stackAt sp 0xa0 = stackAt (sp - 0x60#64) 0x40 ∗ stackAt sp 0x60 := by
  have hs := stackAt_split_bottom sp 0x60 0x40 (by decide)
  simpa [stackAt, BitVec.sub_sub] using hs

theorem spqrOnceCall_unprobed_ok (P : Program) (L : StdBinaryLayout)
    (onceCallAddr closureAddr initAddr storageAddr tokenAddr vtableAddr hwcapAddr : BitVec 64)
    (hc : SpqrCpuProbeCode P L onceCallAddr closureAddr initAddr storageAddr hwcapAddr) :
    subroutine_ok P onceCallAddr
      (spqrOnceCallUnprobedSpec L storageAddr tokenAddr vtableAddr closureAddr initAddr) := by
  have hget := getauxval_found_ro_ok P L hc.getauxval
  have hhw := getauxvalHwcap_ok P L hwcapAddr hc.hwcap hget
  have hinit := spqrUseAcceleratedInit_ok P L initAddr storageAddr hwcapAddr hc.useAccelInit hhw
  have hcas := cas4Acq_ok P L hc.cas4Acq
  have hswp := swp4Rel_ok P L hc.swp4Rel
  apply subroutine_ok_of_sepWP_init
  rintro ⟨haveLse, dataPtr, slotPtr, hwcap, auxvAddr, entries⟩ R s0 hpc hrun hpre hsp
  dsimp only [spqrOnceCallUnprobedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hx0, hx1, hx2, hx3, halign, htok_nz, hnonull, hfind⟩, hpre⟩
  refine ⟨(storageAddr ↦₈ 0xff#8) ∗ ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗
      (dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
      ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗ (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
      stackAt s0.sp 0xa0, hpre, ?_⟩
  refine SepWP.weaken_pre
    (P' := ((tokenAddr + 8#64) ↦₃₂ 3#32) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      ((vtableAddr + 0x20#64) ↦₆₄ᵣ closureAddr) ∗ stackAt s0.sp 0x60 ∗
      ((dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
        (storageAddr ↦₈ 0xff#8) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
        (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackAt (s0.sp - 0x60#64) 0x40) ∗ emp)
    (by rw [stackAt_a0_eq_60_40]; sep_entail) ?_
  refine onceCall198_incomplete_wp hc.onceCall hcas hswp hpc hrun rfl hsp rfl hx0 hx1 hx2 hx3 halign
    (Post := (dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ 0#64) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
      (storageAddr ↦₈ spqrStorageOfHwcap hwcap) ∗ ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
      (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗ stackAt (s0.sp - 0x60#64) 0x40)
    (fun sc G hpc_c hrun_c hsp_c hsp_alc hlr_c hx0_c hx1_c _ hret_c => ?_)
    (fun sf hpc_f hrun_f hsp_f hcs_f hstd_f => ?_)
  · have hfin4 : (s0.sp - 0x58#64) + 4#64 = s0.sp - 0x54#64 := by bv_lin
    refine SepWP.weaken_pre
      (P' := (dataPtr ↦₆₄ slotPtr) ∗ (slotPtr ↦₆₄ tokenAddr) ∗ (tokenAddr ↦₆₄ᵣ initAddr) ∗
        (((s0.sp - 0x58#64) + 4#64) ↦₈ 0#8) ∗ (storageAddr ↦₈ 0xff#8) ∗
        ((L.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗ (auxvAddr ↦ᵣ encodeAuxvBytes entries) ∗
        stackAt sc.sp 0x40 ∗
        ((L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ ((s0.sp - 0x58#64) ↦₃₂ 0#32) ∗ G))
      (by rw [hfin4, hsp_c]; sep_entail) ?_
    refine spqrLazyLockClosure_wp hc.closure hinit hpc_c hrun_c hsp_alc hlr_c hx0_c hx1_c
      htok_nz hnonull hfind
      fun sr hpc_r hrun_r hsp_r hcs_r hstd_r => ?_
    refine SepWP.weaken_pre (by rw [hfin4, hsp_c]; sep_entail)
      (hret_c sr hpc_r hrun_r hsp_r hcs_r hstd_r)
  · apply SepWP.done hpc_f hrun_f
    refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hstd_f, Satisfies.mono ?_ hm⟩
    rw [stackAt_a0_eq_60_40]
    sep_entail

end

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.CpuProbe
