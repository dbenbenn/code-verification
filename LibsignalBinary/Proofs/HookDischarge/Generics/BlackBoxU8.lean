/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop -- proof-setup: allow-public-import

/-!
# Byte-Exact `subtle::black_box::<u8>` Discharge (`LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8`)

Real-bytes discharge of the honest (`16`-byte stack) contracts for `subtle::black_box::<u8>`
(`blackBoxU8Words` / `blackBoxU8Instrs`, `5` 32-bit instruction words = `20` bytes:
`sub sp, sp, #0x10; strb w0, [sp, #0xc]; ldrb w0, [sp, #0xc]; add sp, sp, #0x10; ret`, emitted by
pinned `rustc 1.98.1` `--target aarch64-unknown-linux-musl` in `curve25519-dalek`; matches
`arm64-semantics/CaseStudies/Curve25519NeonEquiv/Proofs/Serial/Code.lean` `blackBoxU8Words`
word-for-word). The process-preserving `hasWords` contract (`blackBoxU8_16_processSpec_ok`) carries
`h_no_ext : ∀ pc, P.externAt? pc = none` for hook-free sub-programs, reaching full programs via
ghost / `linkedCallHook` transfer (`BlackBoxCode.lean`, `BlackBoxGhost.lean`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8

open Arm64 ProofLib
open ProofLib.StdStartup (hasInstrs)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (blackBoxSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack
  subroutine_ok_drop_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (hasInstrs_of_hasWords)

/-! ## 1. Instruction Words, Decoded `Instr` List, and Spec Mirrors -/

/-- Exact `5`-word (`20`-byte, `16`-byte stack frame) machine code for `subtle::black_box::<u8>`
    from `libcurve25519_dalek` (`rustc 1.98.1` `aarch64-unknown-linux-musl`). -/
@[expose] def blackBoxU8Words : List (BitVec 32) :=
  [ 0xd10043ff#32, 0x390033e0#32, 0x394033e0#32, 0x910043ff#32, 0xd65f03c0#32 ]

/-- Exact `5`-instruction (`20`-byte, `16`-byte stack frame) sequence decoded from
    `blackBoxU8Words`:
    `sub sp, sp, #0x10; strb w0, [sp, #0xc]; ldrb w0, [sp, #0xc]; add sp, sp, #0x10; ret`. -/
@[expose] def blackBoxU8Instrs : List Instr :=
  [ -- [0] +0x00: 0xd10043ff  sub  sp, sp, #0x10
    .addSubImm .W64 .SUB .sp .sp 0x10#12 false,
    -- [1] +0x04: 0x390033e0  strb w0, [sp, #0xc]
    .str .B8 .x0 (.Offset .sp 0xc#64),
    -- [2] +0x08: 0x394033e0  ldrb w0, [sp, #0xc]
    .ldr .W32 .B8 false .x0 (.Offset .sp 0xc#64),
    -- [3] +0x0c: 0x910043ff  add  sp, sp, #0x10
    .addSubImm .W64 .ADD .sp .sp 0x10#12 false,
    -- [4] +0x10: 0xd65f03c0  ret
    .ret .lr ]

/-- Stack-parameterized `CliExt.blackBoxSpec`; definitionally (`rfl`) equal to
    `CliExt.blackBoxSpec` at `hookStack = extHookStack` (`16384`). -/
@[expose] def cliBlackBoxSpec (hookStack : Nat := extHookStack) : Spec (BitVec 64) :=
  withStack
    { pre := fun v s => ⌜s.readReg64 .x0 = v⌝
      post := fun v s0 sf =>
        ⌜(sf.readReg64 .x0).setWidth 32 = (v.setWidth 8).zeroExtend 32 ∧ sf.trace = s0.trace⌝ }
    hookStack

/-- Low-byte `subtle::black_box::<u8>` contract used by the Curve25519 / X25519 block proofs. -/
@[expose] def blackBoxU8Spec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧ sf.trace = s0.trace⌝

/-- `cliBlackBoxSpec extHookStack` is definitionally `CliExt.blackBoxSpec`. -/
theorem cliBlackBoxSpec_extHookStack : cliBlackBoxSpec extHookStack = blackBoxSpec := rfl

private theorem pureWordsProg_hasWords_blackBoxU8 (entry : BitVec 64) :
    (pureWordsProg entry blackBoxU8Words).hasWords entry blackBoxU8Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range blackBoxU8Words.length).all fun i =>
      (pureWordsProg 0#64 blackBoxU8Words).readWordOff (4 * i) == blackBoxU8Words[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_blackBoxU8 (entry : BitVec 64) :
    (pureWordsProg entry blackBoxU8Words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 blackBoxU8Words) rfl (by prove_all_instrs)

private theorem pureWordsProg_hasInstrs_blackBoxU8 (entry : BitVec 64) :
    hasInstrs (pureWordsProg entry blackBoxU8Words) entry blackBoxU8Instrs :=
  hasInstrs_of_hasWords (pureWordsProg_hasWords_blackBoxU8 entry)

private theorem fetch_at {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  exact hf

private theorem fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  simpa using fetch_at 0 h hi rfl

private def FsTracePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace

private theorem FsTracePreserved.rfl (s : State) : FsTracePreserved s s :=
  ⟨Eq.refl _, Eq.refl _⟩

@[local simp] private theorem FsTracePreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    FsTracePreserved s0 (s.writeReg64 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    FsTracePreserved s0 (s.writeReg32 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_setPState (s0 s : State) (p : PState) :
    FsTracePreserved s0 (s.setPState p) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_advancePC (s0 s : State) :
    FsTracePreserved s0 s.advancePC ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setPC (s0 s : State) (pc : BitVec 64) :
    FsTracePreserved s0 (s.setPC pc) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setMem (s0 s : State) (m : Memory) :
    FsTracePreserved s0 (s.setMem m) ↔ FsTracePreserved s0 s := by
  cases s; rfl

private theorem fs_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.fs = s0.fs := h.1

private theorem trace_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.trace = s0.trace := h.2

/-! ## 2. Exact `16`-Byte Stack Stepping Proof & Forward-Simulation Lifts -/

/-- Minimal honest `16`-byte stack `keepsFs` bridge: `blackBoxU8Instrs` at `addr` satisfies
    `keepsFs (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)`. -/
theorem blackBoxU8_16_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr blackBoxU8Instrs) :
    subroutine_ok P addr
      (keepsFs (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) := by
  apply subroutine_ok_of_sepWP_init
  intro v R s0 hpc hrun hpre _hsp
  dsimp only [keepsFs, withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hpre⟩ := hpre
  have hst : stackAt s0.sp 16 =
      ((∃∗ b0 : BitVec 8, (s0.sp - 4#64) ↦₈ b0) ∗
        (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3)) := by
    change memRegion (s0.sp - 16#64) 16 = _
    rw [memRegion_split3 (s0.sp - 16#64) 16 12 1 (by decide) (by decide), memRegion_one]
    have h1 : s0.sp - 16#64 + 12#64 = s0.sp - 4#64 := by bv_arith
    have h2 : s0.sp - 16#64 + 13#64 = s0.sp - 3#64 := by bv_arith
    rw [h1, h2]
  rw [hst, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨b0, hpre⟩ := hpre
  refine ⟨((s0.sp - 4#64) ↦₈ b0) ∗ (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3),
    by rwa [← sepConj_assoc] at hpre, ?_⟩
  have hf0 := fetch_at0 hcode
  have hf1 := fetch_at 1 (off := 0x04#64) hcode
  have hf2 := fetch_at 2 (off := 0x08#64) hcode
  have hf3 := fetch_at 3 (off := 0x0c#64) hcode
  have hf4 := fetch_at 4 (off := 0x10#64) hcode
  wp_steps 5
  apply SepWP.done
  · simp [wp_norm, arm64_norm]
  · exact hrun
  · refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · have hstk_post :
          (((s0.sp - 4#64) ↦₈ BitVec.zeroExtend 8 v) ∗
            (memRegion (s0.sp - 16#64) 12 ∗ memRegion (s0.sp - 3#64) 3)) ⊢
          stackAt s0.sp 16 := by
        rw [hst]
        exact sepConj_mono_left (Entails.sepExists_right (BitVec.zeroExtend 8 v) (Entails.refl _))
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨fs_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨?_, trace_eq_of_preserved (by simp [FsTracePreserved.rfl])⟩,
        Satisfies.mono (sepConj_mono_left hstk_post) hm⟩
      simp [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]
      rw [CalleeSavedPreserved_writeReg64_caller _ _ Reg.sp _,
          CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 0#5) _]
      exact CalleeSavedPreserved.rfl s0

/-- Minimal honest `16`-byte stack bridge: `blackBoxU8Instrs` at `addr` satisfies
    `withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16`. -/
theorem blackBoxU8_16_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr blackBoxU8Instrs) :
    subroutine_ok P addr
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16) :=
  subroutine_ok_drop_keepsFs (blackBoxU8_16_keepsFs_ok hcode)

/-- Full `ProcessFieldsPreserved` minimal `16`-byte stack bridge for `blackBoxU8Words` at `addr`
    on any hook-free program `P`. -/
theorem blackBoxU8_16_processSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr blackBoxU8Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16 with
        post := fun x s0 sf =>
          ⌜ProcessFieldsPreserved s0 sf⌝ ∗
            (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16).post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (blackBoxU8_16_ok (pureWordsProg_hasInstrs_blackBoxU8 addr))
    (pureWordsProg_noSvcMsr_blackBoxU8 addr) hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

end LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8
