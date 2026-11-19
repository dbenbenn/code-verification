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
import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop

/-!
# Byte-Exact ML-KEM-768 `pk1` & `pk2` Hook Discharges (`LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk`)

Real-bytes discharge of the SPQR V1 incremental ML-KEM-768 compressed-keypair projection contracts
(`LibsignalBinary/Specifications/LibsignalSpqrV1/Hooks.lean:234-250`,
`LibsignalBinary/Heap/SpecBudget.lean:380-405`, and
`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean:214-217`):

1. **`<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1`**
   (`_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1`):
   `mlkemPk1Words` / `mlkemPk1Instrs` (`2` words = `8` bytes, `0` B stack, `0` memory accesses:
   `add x0, x0, #0x900; ret`, returning `kpA + 2304#64`).
2. **`<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2`**
   (`_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2`):
   `mlkemPk2Words` / `mlkemPk2Instrs` (`2` words = `8` bytes, `0` B stack, `0` memory accesses:
   `add x0, x0, #0x480; ret`, returning `kpA + 1152#64`).

Both implementations are emitted by pinned `rustc 1.98.1` (`aarch64-unknown-linux-musl` release
profile, `libcrux-ml-kem` `0.0.10`). Because neither routine reads or writes memory or stack, both
satisfy minimal `0`-byte-stack, `0`-memory-footprint register contracts (`mlkemPk1RegSpec`,
`mlkemPk2RegSpec`), unstacked `MlkemKpRefCall` contracts (`mlkemPk1UnstackedSpec`,
`mlkemPk2UnstackedSpec`), and the exact trusted consumer specs `mlkemPk1Spec` and `mlkemPk2Spec`
(plus `keepsFs`, `withVmPreserved`, `withFsPred`, `withStack`, `.inImage`, and
`ProcessFieldsPreserved` forms).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk

open Arm64 ProofLib
open ProofLib.StdStartup (hasInstrs)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (MlkemKpRefCall pk1Off pk2Off mlkemPk1Spec mlkemPk2Spec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack
  subroutine_ok_drop_keepsFs subroutine_ok_withStack
  subroutine_ok_withStack_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred
  subroutine_ok_withFsPred_of_keepsFs)

/-! ## 1. Shared Hook-Discharge Combinators -/

/-- Decode `P.hasWords addr words` into `hasInstrs P addr instrs` whenever `words` decodes
    elementwise to `instrs`. -/
theorem hasInstrs_of_hasWords {P : Program} {addr : BitVec 64}
    {words : List (BitVec 32)} {instrs : List Instr}
    (hw : P.hasWords addr words)
    (hdec : (List.range instrs.length).all
      (fun i => Program.decodeWordAt words i == instrs[i]?) = true := by decide) :
    hasInstrs P addr instrs := by
  intro i hi
  have hall := List.all_eq_true.mp hdec i (List.mem_range.mpr hi)
  simp only [beq_iff_eq, List.getElem?_eq_getElem hi] at hall
  exact Program.fetch_of_hasWords_decodeAt i hw rfl hall

/-- Lift `subroutine_ok (pureWordsProg addr words) addr spec` to `keepsFs (withVmPreserved spec)`
    on any hook-free program `P` containing `words` at `addr`. -/
theorem subroutine_ok_keepsFs_withVmPreserved_of_pureWords {α : Type}
    {P : Program} {addr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (hpure : subroutine_ok (pureWordsProg addr words) addr spec)
    (hall : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (hc : P.hasWords addr words)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_panic : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (h_oom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_ne : words ≠ [] := by decide)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok P addr (keepsFs (withVmPreserved spec)) := by
  have hlift := subroutine_ok_lift_pureWords_process hpure hall hc h_no_ext
    h_panic h_exit h_oom h_ne h_pre_mem h_post_mem
  refine subroutine_ok_map hlift
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by rw [h_panic] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by rw [h_exit] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by rw [h_oom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [keepsFs, withVmPreserved] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.1.toVmPreserved, hpost.2⟩

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

@[local simp] private theorem FsTracePreserved_advancePC (s0 s : State) :
    FsTracePreserved s0 s.advancePC ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setPC (s0 s : State) (pc : BitVec 64) :
    FsTracePreserved s0 (s.setPC pc) ↔ FsTracePreserved s0 s := by
  cases s; rfl

private theorem fs_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.fs = s0.fs := h.1

private theorem trace_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.trace = s0.trace := h.2

/-! ## 2. Instruction Words, Decoded `Instr` Lists, and Minimal Register Contracts -/

/-- Exact `2`-word (`8`-byte, `0`-byte stack) machine code for
    `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1` (`rustc 1.98.1`
    `aarch64-unknown-linux-musl`): `add x0, x0, #0x900; ret`. -/
@[expose] def mlkemPk1Words : List (BitVec 32) :=
  [ 0x91240000#32, 0xd65f03c0#32 ]

/-- Exact `2`-instruction sequence decoded from `mlkemPk1Words`. -/
@[expose] def mlkemPk1Instrs : List Instr :=
  [ -- [0] +0x00: 0x91240000  add x0, x0, #0x900
    .addSubImm .W64 .ADD .x0 .x0 0x900#12 false,
    -- [1] +0x04: 0xd65f03c0  ret
    .ret .lr ]

/-- Exact `2`-word (`8`-byte, `0`-byte stack) machine code for
    `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2` (`rustc 1.98.1`
    `aarch64-unknown-linux-musl`): `add x0, x0, #0x480; ret`. -/
@[expose] def mlkemPk2Words : List (BitVec 32) :=
  [ 0x91120000#32, 0xd65f03c0#32 ]

/-- Exact `2`-instruction sequence decoded from `mlkemPk2Words`. -/
@[expose] def mlkemPk2Instrs : List Instr :=
  [ -- [0] +0x00: 0x91120000  add x0, x0, #0x480
    .addSubImm .W64 .ADD .x0 .x0 0x480#12 false,
    -- [1] +0x04: 0xd65f03c0  ret
    .ret .lr ]

/-- Minimal `0`-stack, `0`-memory-footprint register contract for `pk1`: adds `pk1Off` (`2304`) to
    `x0` and preserves `trace`. -/
@[expose] def mlkemPk1RegSpec : Spec (BitVec 64) where
  pre := fun kpA s => ⌜s.readReg64 .x0 = kpA⌝
  post := fun kpA s0 sf => ⌜sf.readReg64 .x0 = kpA + BitVec.ofNat 64 pk1Off ∧ sf.trace = s0.trace⌝

/-- Minimal `0`-stack, `0`-memory-footprint register contract for `pk2`: adds `pk2Off` (`1152`) to
    `x0` and preserves `trace`. -/
@[expose] def mlkemPk2RegSpec : Spec (BitVec 64) where
  pre := fun kpA s => ⌜s.readReg64 .x0 = kpA⌝
  post := fun kpA s0 sf => ⌜sf.readReg64 .x0 = kpA + BitVec.ofNat 64 pk2Off ∧ sf.trace = s0.trace⌝

/-- Unstacked `MlkemKpRefCall` contract for `pk1` (`0` B stack). -/
@[expose] def mlkemPk1UnstackedSpec : Spec MlkemKpRefCall where
  pre := fun x s => ⌜s.readReg64 .x0 = x.kpA⌝ ∗ (x.kpA ↦ₛ x.kp.toList)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = x.kpA + BitVec.ofNat 64 pk1Off ∧ sf.trace = s0.trace⌝ ∗
      (x.kpA ↦ₛ x.kp.toList)

/-- Unstacked `MlkemKpRefCall` contract for `pk2` (`0` B stack). -/
@[expose] def mlkemPk2UnstackedSpec : Spec MlkemKpRefCall where
  pre := fun x s => ⌜s.readReg64 .x0 = x.kpA⌝ ∗ (x.kpA ↦ₛ x.kp.toList)
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = x.kpA + BitVec.ofNat 64 pk2Off ∧ sf.trace = s0.trace⌝ ∗
      (x.kpA ↦ₛ x.kp.toList)

/-- `withStack mlkemPk1UnstackedSpec extHookStack` equals `mlkemPk1Spec` up to `sepConj_assoc`. -/
theorem withStack_mlkemPk1UnstackedSpec_extHookStack :
    withStack mlkemPk1UnstackedSpec extHookStack = mlkemPk1Spec := by
  dsimp only [withStack, mlkemPk1UnstackedSpec, mlkemPk1Spec]
  congr 1
  · funext x s; exact sepConj_assoc _ _ _
  · funext x s0 sf; exact sepConj_assoc _ _ _

/-- `withStack mlkemPk2UnstackedSpec extHookStack` equals `mlkemPk2Spec` up to `sepConj_assoc`. -/
theorem withStack_mlkemPk2UnstackedSpec_extHookStack :
    withStack mlkemPk2UnstackedSpec extHookStack = mlkemPk2Spec := by
  dsimp only [withStack, mlkemPk2UnstackedSpec, mlkemPk2Spec]
  congr 1
  · funext x s; exact sepConj_assoc _ _ _
  · funext x s0 sf; exact sepConj_assoc _ _ _

/-! ## 3. Stepping Proofs and Forward-Simulation Lifts for `pk1` -/

private theorem pureWordsProg_hasWords_pk1 (entry : BitVec 64) :
    (pureWordsProg entry mlkemPk1Words).hasWords entry mlkemPk1Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range mlkemPk1Words.length).all fun i =>
      (pureWordsProg 0#64 mlkemPk1Words).readWordOff (4 * i) == mlkemPk1Words[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_pk1 (entry : BitVec 64) :
    (pureWordsProg entry mlkemPk1Words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 mlkemPk1Words) rfl (by prove_all_instrs)

private theorem pureWordsProg_hasInstrs_pk1 (entry : BitVec 64) :
    hasInstrs (pureWordsProg entry mlkemPk1Words) entry mlkemPk1Instrs :=
  hasInstrs_of_hasWords (pureWordsProg_hasWords_pk1 entry)

/-- Minimal `0`-stack, `0`-memory `keepsFs` proof for `pk1` (`add x0, x0, #0x900; ret`). -/
theorem mlkemPk1_regSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk1RegSpec) := by
  apply subroutine_ok_of_sepWP_init
  intro kpA R s0 hpc hrun hpre _hsp
  dsimp only [keepsFs, mlkemPk1RegSpec] at hpre ⊢
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hR⟩ := hpre
  refine ⟨emp, by rwa [emp_sepConj], ?_⟩
  have hf0 := fetch_at0 hcode
  have hf1 := fetch_at 1 (off := 0x04#64) hcode
  wp_steps 2
  apply SepWP.done
  · simp [wp_norm, arm64_norm]
  · exact hrun
  · refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · rw [emp_sepConj] at hm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨fs_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨?_, trace_eq_of_preserved (by simp [FsTracePreserved.rfl])⟩, hm⟩
      simp [wp_norm, arm64_norm, pk1Off]
    · simp only [wp_norm, arm64_norm]
      rw [CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 0#5) _]
      exact CalleeSavedPreserved.rfl s0

/-- Minimal `0`-stack, `0`-memory proof for `pk1`. -/
theorem mlkemPk1_regSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr mlkemPk1RegSpec :=
  subroutine_ok_drop_keepsFs (mlkemPk1_regSpec_keepsFs_ok hcode)

private theorem mlkemPk1Reg_simulates_unstacked :
    SpecSimulates (keepsFs mlkemPk1RegSpec) (keepsFs mlkemPk1UnstackedSpec) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ?_
  dsimp only [keepsFs, mlkemPk1UnstackedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hkpR⟩ := hpre
  refine ⟨x.kpA, (x.kpA ↦ₛ x.kp.toList) ∗ R, ?_, fun sf _hret _hcc hpost => ?_⟩
  · dsimp only [keepsFs, mlkemPk1RegSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨hx0, hkpR⟩
  · dsimp only [keepsFs, mlkemPk1RegSpec, mlkemPk1UnstackedSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hfs, hpost⟩ := hpost
    refine ⟨hfs, ?_⟩
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact hpost

/-- Unstacked (`0`-byte stack) `keepsFs` discharge for `pk1`. -/
theorem mlkemPk1_unstacked_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk1UnstackedSpec) :=
  mlkemPk1Reg_simulates_unstacked.subroutine_ok (mlkemPk1_regSpec_keepsFs_ok hcode)

/-- Unstacked (`0`-byte stack) discharge for `pk1`. -/
theorem mlkemPk1_unstacked_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr mlkemPk1UnstackedSpec :=
  subroutine_ok_drop_keepsFs (mlkemPk1_unstacked_keepsFs_ok hcode)

/-- Arbitrary-stack `keepsFs` discharge for `pk1`. -/
theorem mlkemPk1_withStack_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hookStack : Nat) (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr (keepsFs (withStack mlkemPk1UnstackedSpec hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (mlkemPk1_unstacked_keepsFs_ok hcode)

/-- Exact trusted `mlkemPk1Spec` (`Hooks.lean:234`) `keepsFs` discharge from `hasInstrs`. -/
theorem mlkemPk1_mlkemPk1Spec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk1Spec) := by
  rw [← withStack_mlkemPk1UnstackedSpec_extHookStack]
  exact mlkemPk1_withStack_keepsFs_ok extHookStack hcode

/-- Exact trusted `mlkemPk1Spec` (`Hooks.lean:234`) discharge from `hasInstrs`. -/
theorem mlkemPk1_mlkemPk1Spec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk1Instrs) :
    subroutine_ok P addr mlkemPk1Spec :=
  subroutine_ok_drop_keepsFs (mlkemPk1_mlkemPk1Spec_keepsFs_ok hcode)

/-- Exact trusted `mlkemPk1Spec` discharge from `P.hasWords addr mlkemPk1Words`. -/
theorem mlkemPk1_mlkemPk1Spec_words_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk1Words) :
    subroutine_ok P addr mlkemPk1Spec :=
  mlkemPk1_mlkemPk1Spec_ok (hasInstrs_of_hasWords hc)

/-- Full `ProcessFieldsPreserved` discharge for `mlkemPk1Words` on a hook-free program `P`. -/
theorem mlkemPk1_mlkemPk1ProcessSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk1Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { mlkemPk1Spec with
        post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ mlkemPk1Spec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (mlkemPk1_mlkemPk1Spec_ok (pureWordsProg_hasInstrs_pk1 addr))
    (pureWordsProg_noSvcMsr_pk1 addr) hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

/-- Process- and VM-preserving `keepsFs` bridge (`keepsFs (withVmPreserved mlkemPk1Spec)`) on a
    hook-free program `P`. -/
theorem mlkemPk1_mlkemPk1BudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk1Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved mlkemPk1Spec)) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (mlkemPk1_mlkemPk1Spec_ok (pureWordsProg_hasInstrs_pk1 addr))
    (pureWordsProg_noSvcMsr_pk1 addr) hc h_no_ext

/-- Exact SPQR budget consumer contract (`SpqrHooksBudget.pk1`: `withVmPreserved mlkemPk1Spec` in
    `SpecBudget.lean:383`) discharged from `mlkemPk1Words` on a hook-free program `P`. -/
theorem mlkemPk1_mlkemPk1BudgetSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk1Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved mlkemPk1Spec) :=
  subroutine_ok_drop_keepsFs (mlkemPk1_mlkemPk1BudgetSpec_keepsFs_ok hc h_no_ext)

/-- `withFsPred Pfs (withVmPreserved mlkemPk1Spec)` bridge on a hook-free program `P`. -/
theorem mlkemPk1_mlkemPk1BudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop)
    (hc : P.hasWords addr mlkemPk1Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withFsPred Pfs (withVmPreserved mlkemPk1Spec)) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs (mlkemPk1_mlkemPk1BudgetSpec_keepsFs_ok hc h_no_ext)

/-! ## 4. Stepping Proofs and Forward-Simulation Lifts for `pk2` -/

private theorem pureWordsProg_hasWords_pk2 (entry : BitVec 64) :
    (pureWordsProg entry mlkemPk2Words).hasWords entry mlkemPk2Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range mlkemPk2Words.length).all fun i =>
      (pureWordsProg 0#64 mlkemPk2Words).readWordOff (4 * i) == mlkemPk2Words[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_pk2 (entry : BitVec 64) :
    (pureWordsProg entry mlkemPk2Words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 mlkemPk2Words) rfl (by prove_all_instrs)

private theorem pureWordsProg_hasInstrs_pk2 (entry : BitVec 64) :
    hasInstrs (pureWordsProg entry mlkemPk2Words) entry mlkemPk2Instrs :=
  hasInstrs_of_hasWords (pureWordsProg_hasWords_pk2 entry)

/-- Minimal `0`-stack, `0`-memory `keepsFs` proof for `pk2` (`add x0, x0, #0x480; ret`). -/
theorem mlkemPk2_regSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk2RegSpec) := by
  apply subroutine_ok_of_sepWP_init
  intro kpA R s0 hpc hrun hpre _hsp
  dsimp only [keepsFs, mlkemPk2RegSpec] at hpre ⊢
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hR⟩ := hpre
  refine ⟨emp, by rwa [emp_sepConj], ?_⟩
  have hf0 := fetch_at0 hcode
  have hf1 := fetch_at 1 (off := 0x04#64) hcode
  wp_steps 2
  apply SepWP.done
  · simp [wp_norm, arm64_norm]
  · exact hrun
  · refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · rw [emp_sepConj] at hm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨fs_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨?_, trace_eq_of_preserved (by simp [FsTracePreserved.rfl])⟩, hm⟩
      simp [wp_norm, arm64_norm, pk2Off]
    · simp only [wp_norm, arm64_norm]
      rw [CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 0#5) _]
      exact CalleeSavedPreserved.rfl s0

/-- Minimal `0`-stack, `0`-memory proof for `pk2`. -/
theorem mlkemPk2_regSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr mlkemPk2RegSpec :=
  subroutine_ok_drop_keepsFs (mlkemPk2_regSpec_keepsFs_ok hcode)

private theorem mlkemPk2Reg_simulates_unstacked :
    SpecSimulates (keepsFs mlkemPk2RegSpec) (keepsFs mlkemPk2UnstackedSpec) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ?_
  dsimp only [keepsFs, mlkemPk2UnstackedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hkpR⟩ := hpre
  refine ⟨x.kpA, (x.kpA ↦ₛ x.kp.toList) ∗ R, ?_, fun sf _hret _hcc hpost => ?_⟩
  · dsimp only [keepsFs, mlkemPk2RegSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨hx0, hkpR⟩
  · dsimp only [keepsFs, mlkemPk2RegSpec, mlkemPk2UnstackedSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hfs, hpost⟩ := hpost
    refine ⟨hfs, ?_⟩
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact hpost

/-- Unstacked (`0`-byte stack) `keepsFs` discharge for `pk2`. -/
theorem mlkemPk2_unstacked_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk2UnstackedSpec) :=
  mlkemPk2Reg_simulates_unstacked.subroutine_ok (mlkemPk2_regSpec_keepsFs_ok hcode)

/-- Unstacked (`0`-byte stack) discharge for `pk2`. -/
theorem mlkemPk2_unstacked_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr mlkemPk2UnstackedSpec :=
  subroutine_ok_drop_keepsFs (mlkemPk2_unstacked_keepsFs_ok hcode)

/-- Arbitrary-stack `keepsFs` discharge for `pk2`. -/
theorem mlkemPk2_withStack_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hookStack : Nat) (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr (keepsFs (withStack mlkemPk2UnstackedSpec hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (mlkemPk2_unstacked_keepsFs_ok hcode)

/-- Exact trusted `mlkemPk2Spec` (`Hooks.lean:244`) `keepsFs` discharge from `hasInstrs`. -/
theorem mlkemPk2_mlkemPk2Spec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr (keepsFs mlkemPk2Spec) := by
  rw [← withStack_mlkemPk2UnstackedSpec_extHookStack]
  exact mlkemPk2_withStack_keepsFs_ok extHookStack hcode

/-- Exact trusted `mlkemPk2Spec` (`Hooks.lean:244`) discharge from `hasInstrs`. -/
theorem mlkemPk2_mlkemPk2Spec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr mlkemPk2Instrs) :
    subroutine_ok P addr mlkemPk2Spec :=
  subroutine_ok_drop_keepsFs (mlkemPk2_mlkemPk2Spec_keepsFs_ok hcode)

/-- Exact trusted `mlkemPk2Spec` discharge from `P.hasWords addr mlkemPk2Words`. -/
theorem mlkemPk2_mlkemPk2Spec_words_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk2Words) :
    subroutine_ok P addr mlkemPk2Spec :=
  mlkemPk2_mlkemPk2Spec_ok (hasInstrs_of_hasWords hc)

/-- Full `ProcessFieldsPreserved` discharge for `mlkemPk2Words` on a hook-free program `P`. -/
theorem mlkemPk2_mlkemPk2ProcessSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk2Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { mlkemPk2Spec with
        post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ mlkemPk2Spec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (mlkemPk2_mlkemPk2Spec_ok (pureWordsProg_hasInstrs_pk2 addr))
    (pureWordsProg_noSvcMsr_pk2 addr) hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

/-- Process- and VM-preserving `keepsFs` bridge (`keepsFs (withVmPreserved mlkemPk2Spec)`) on a
    hook-free program `P`. -/
theorem mlkemPk2_mlkemPk2BudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk2Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved mlkemPk2Spec)) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (mlkemPk2_mlkemPk2Spec_ok (pureWordsProg_hasInstrs_pk2 addr))
    (pureWordsProg_noSvcMsr_pk2 addr) hc h_no_ext

/-- Exact SPQR budget consumer contract (`SpqrHooksBudget.pk2`: `withVmPreserved mlkemPk2Spec` in
    `SpecBudget.lean:385`) discharged from `mlkemPk2Words` on a hook-free program `P`. -/
theorem mlkemPk2_mlkemPk2BudgetSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr mlkemPk2Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved mlkemPk2Spec) :=
  subroutine_ok_drop_keepsFs (mlkemPk2_mlkemPk2BudgetSpec_keepsFs_ok hc h_no_ext)

/-- `withFsPred Pfs (withVmPreserved mlkemPk2Spec)` bridge on a hook-free program `P`. -/
theorem mlkemPk2_mlkemPk2BudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop)
    (hc : P.hasWords addr mlkemPk2Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withFsPred Pfs (withVmPreserved mlkemPk2Spec)) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs (mlkemPk2_mlkemPk2BudgetSpec_keepsFs_ok hc h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
