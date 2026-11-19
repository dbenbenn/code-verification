/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Proofs.SpqrV1.GF.UnacceleratedMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.AcceleratedMul -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `spqr::encoding::gf::mul2_u16`

Proves fixed-offset (`0x63a0c`) and relocatable `[LibsignalPlacement]` (Block `381`) subroutine
contracts for `spqr::encoding::gf::mul2_u16` against `mul2U16`.
-/

public section

namespace CryptoVerification.SpqrV1.GF.Mul2U16

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

abbrev mul2U16Name : String := "spqr::encoding::gf::mul2_u16"

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
theorem step_ldar32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 true rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad32 ea P v)
    (hexec : (s.writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldarStlr .W32 true rn rt) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldarStlr .W32 true rn rt) s = s' := by
    rw [← hexec]
    simp [execInst, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    rfl
  apply hnext R
  rwa [hmem]

theorem stackAt_64_split (sp : BitVec 64) :
    stackAt sp 0x40 =
      memRegion (sp - 64#64) 16 ∗
      (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗
      (∃∗ s21 : BitVec 64, (sp - 32#64) ↦₆₄ s21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x40 = 64#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 16) (k := 48)
        (b' := sp - 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 16#64),
      memRegion_eight (sp - 8#64)]

theorem stackAt_64_merge (sp s29 s30 s21 s20 s19 : BitVec 64) :
    memRegion (sp - 64#64) 16 ∗
      ((sp - 48#64) ↦₆₄ s29) ∗
      ((sp - 40#64) ↦₆₄ s30) ∗
      ((sp - 32#64) ↦₆₄ s21) ∗
      memRegion (sp - 24#64) 8 ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp 0x40 := by
  rw [stackAt_64_split sp]
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s29) ?_)
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s21) ?_
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s20) ?_)
  exact Entails.sepExists_intro s19

abbrev mul2U16Stack : Nat := 0x100

theorem stackAt_256_split (sp : BitVec 64) :
    stackAt sp mul2U16Stack =
      memRegion (sp - 256#64) 32 ∗
      stackAt (sp - 64#64) 0xa0 ∗
      memRegion (sp - 64#64) 8 ∗
      (∃∗ vslot : BitVec 64, (sp - 56#64) ↦₆₄ vslot) ∗
      (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗
      (∃∗ s21 : BitVec 64, (sp - 32#64) ↦₆₄ s21) ∗
      (∃∗ vdata : BitVec 64, (sp - 24#64) ↦₆₄ vdata) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  simp only [stackAt, mul2U16Stack]
  rw [show BitVec.ofNat 64 0x100 = 256#64 from rfl,
      show BitVec.ofNat 64 0xa0 = 160#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 256#64) (n := 32) (k := 224)
        (b' := sp - 64#64 - 160#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64 - 160#64) (n := 160) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48)
        (b' := sp - 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 56#64), memRegion_eight (sp - 48#64),
      memRegion_eight (sp - 40#64), memRegion_eight (sp - 32#64),
      memRegion_eight (sp - 24#64), memRegion_eight (sp - 16#64),
      memRegion_eight (sp - 8#64)]

theorem stackAt_256_merge (sp vslot s29 s30 s21 vdata s20 s19 : BitVec 64) :
    memRegion (sp - 256#64) 32 ∗
      stackAt (sp - 64#64) 0xa0 ∗
      memRegion (sp - 64#64) 8 ∗
      ((sp - 56#64) ↦₆₄ vslot) ∗
      ((sp - 48#64) ↦₆₄ s29) ∗
      ((sp - 40#64) ↦₆₄ s30) ∗
      ((sp - 32#64) ↦₆₄ s21) ∗
      ((sp - 24#64) ↦₆₄ vdata) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp mul2U16Stack := by
  rw [stackAt_256_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_intro vslot) ?_
  refine sepConj_mono (Entails.sepExists_intro s29) ?_
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s21) ?_
  refine sepConj_mono (Entails.sepExists_intro vdata) ?_
  refine sepConj_mono (Entails.sepExists_intro s20) ?_
  exact Entails.sepExists_intro s19

@[local wp_norm]
theorem zeroExtend_16_truncate_32_64 (x : BitVec 64) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by
  bv_bits

@[local wp_norm]
private theorem mul2U16_fst (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).1 = unaccelerated.mul a b1 := rfl

@[local wp_norm]
private theorem mul2U16_snd (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).2 = unaccelerated.mul a b2 := rfl

/-- Symbol of `std::sys::sync::once::futex::Once::call` invoked on the unprobed SPQR slow paths. -/
abbrev spqrOnceCallSym : String :=
  "_RNvMs0_NtNtNtNtCsfr5T3GFabw_3std3sys4sync4once5futexNtB5_4Once4call"

/-- Read-only vtable symbol passed in `x3` at all SPQR `Once::call` slow-path call sites. -/
abbrev spqrLazyLockVtableSym : String :=
  "spqr:.rodata..Lanon.0"

/-- Caller return address inside `libsignalSessionLib` blocks `0 .. 623` outside the SPQR CPU-probe
callee blocks `321` (`LazyLock` closure) and `385` (`use_accelerated::init`). -/
@[expose] def LsRetAddrNoProbe [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  ∃ j < 624, j ≠ 321 ∧ j ≠ 385 ∧
    ∃ o < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j,
      lr = lsmpl.base j + BitVec.ofNat 64 o

@[wp_norm]
theorem lsRetAddrNoProbe_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (h321 : j ≠ 321) (h385 : j ≠ 385)
    (ho : off.toNat < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j) :
    LsRetAddrNoProbe (lsmpl.base j + off) :=
  ⟨j, hj, h321, h385, off.toNat, ho, by simp [BitVec.ofNat_toNat]⟩

@[wp_norm]
theorem lsRetAddrNoProbe_blockPlacement_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (h321 : j ≠ 321) (h385 : j ≠ 385)
    (ho : off.toNat < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j) :
    LsRetAddrNoProbe ((libsignalSessionLib.blockPlacement lsmpl j).base + off) :=
  lsRetAddrNoProbe_base_add j off hj h321 h385 ho

@[wp_norm]
theorem lsRetAddrNoProbe_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (h321 : j ≠ 321) (h385 : j ≠ 385)
    (ho : 0 < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j) :
    LsRetAddrNoProbe (lsmpl.base j) :=
  ⟨j, hj, h321, h385, 0, ho, by simp⟩

@[wp_norm]
theorem lsRetAddrNoProbe_blockPlacement_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (h321 : j ≠ 321) (h385 : j ≠ 385)
    (ho : 0 < LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen j) :
    LsRetAddrNoProbe ((libsignalSessionLib.blockPlacement lsmpl j).base) :=
  lsRetAddrNoProbe_base_zero j hj h321 h385 ho

/-- Read-only invariant environment read by SPQR's `Once::call` CPU-feature probe (`TOKEN[0..8)`
init-fn pointer, `.rodata` `LazyLock` vtable slot, `__aarch64_have_lse_atomics`, `__libc.auxv`, and
the initial stack auxiliary vector with `AT_HWCAP = 0x1b#64`). Kept opaque (`def` without
`@[expose]`) so `wp_simp_pre` treats it as an atomic frame token across SPQR callers. -/
def spqrProbeEnvAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  ∃∗ haveLse : BitVec 8,
    ∃∗ auxvAddr : BitVec 64,
      ∃∗ entries : List (BitVec 64 × BitVec 64),
        ⌜MemWidth.isAligned .W32 (mpl.ρ tokenName + 8#64) = true ∧
          mpl.ρ tokenName ≠ 0#64 ∧
          (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
          entries.find? (·.1 == 16#64) = some (16#64, 0x1b#64)⌝ ∗
        (mpl.ρ tokenName ↦₆₄ᵣ mpl.base 385) ∗
        ((mpl.ρ spqrLazyLockVtableSym + 0x20#64) ↦₆₄ᵣ mpl.base 321) ∗
        (LibsignalBinary.Heap.Fine.f3StdLayout.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        ((LibsignalBinary.Heap.Fine.f3StdLayout.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
        (auxvAddr ↦ᵣ ProofLib.encodeAuxvBytes entries)

theorem spqrProbeEnvAtMpl_eq (mpl : Obj.MultiPlacement) :
    spqrProbeEnvAtMpl mpl =
      ∃∗ haveLse : BitVec 8,
        ∃∗ auxvAddr : BitVec 64,
          ∃∗ entries : List (BitVec 64 × BitVec 64),
            ⌜MemWidth.isAligned .W32 (mpl.ρ tokenName + 8#64) = true ∧
              mpl.ρ tokenName ≠ 0#64 ∧
              (∀ t v, (t, v) ∈ entries → t ≠ 0#64) ∧
              entries.find? (·.1 == 16#64) = some (16#64, 0x1b#64)⌝ ∗
            (mpl.ρ tokenName ↦₆₄ᵣ mpl.base 385) ∗
            ((mpl.ρ spqrLazyLockVtableSym + 0x20#64) ↦₆₄ᵣ mpl.base 321) ∗
            (LibsignalBinary.Heap.Fine.f3StdLayout.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
            ((LibsignalBinary.Heap.Fine.f3StdLayout.libcAddr + 0x08#64) ↦₆₄ᵣ auxvAddr) ∗
            (auxvAddr ↦ᵣ ProofLib.encodeAuxvBytes entries) := by
  unfold spqrProbeEnvAtMpl
  rfl

abbrev spqrProbeEnvAt [LibsignalPlacement] : SepProp :=
  spqrProbeEnvAtMpl lsmpl

/-- Probed state of `use_accelerated::STORAGE.0` (`1`, PMULL accelerated),
`check_accelerated::TOKEN + 8` (`0`), and `spqrProbeEnvAt`. -/
@[expose] def tokenProbedPlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ tokenStorageName ↦₈ 1#8) ∗
  ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
  spqrProbeEnvAt

/-- Unprobed initial ELF state of `use_accelerated::STORAGE.0` (`0xff`),
`check_accelerated::TOKEN + 8` (`3`, `OnceState::INCOMPLETE`), and `spqrProbeEnvAt`. -/
@[expose] def tokenUnprobedPlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ tokenStorageName ↦₈ 0xff#8) ∗
  ((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗
  spqrProbeEnvAt

/-- Relocatable precondition on `check_accelerated::TOKEN` (`lsρ tokenName + 8#64`) and
`use_accelerated::STORAGE.0` (`lsρ tokenStorageName`): either already probed as PMULL-accelerated
(`(1#8, 0#32)`) or unprobed (`(0xff#8, 3#32)`), in which case the first GF(2¹⁶) operation calls
`Once::call` to probe and transition to `(1#8, 0#32)`. -/
@[expose] def tokenInitPlacedAt [LibsignalPlacement] : SepProp :=
  ∃∗ probed : Bool, if probed then tokenProbedPlacedAt else tokenUnprobedPlacedAt

/-- Explicit-`mpl` probed state of `use_accelerated::STORAGE.0` (`1`, PMULL accelerated),
`check_accelerated::TOKEN + 8` (`0`), and `spqrProbeEnvAtMpl mpl`. -/
@[expose] def tokenProbedPlacedAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  (mpl.ρ tokenStorageName ↦₈ 1#8) ∗
  ((mpl.ρ tokenName + 8#64) ↦₃₂ 0#32) ∗
  spqrProbeEnvAtMpl mpl

/-- Explicit-`mpl` unprobed initial ELF state of `use_accelerated::STORAGE.0` (`0xff`),
`check_accelerated::TOKEN + 8` (`3`, `OnceState::INCOMPLETE`), and `spqrProbeEnvAtMpl mpl`. -/
@[expose] def tokenUnprobedPlacedAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  (mpl.ρ tokenStorageName ↦₈ 0xff#8) ∗
  ((mpl.ρ tokenName + 8#64) ↦₃₂ 3#32) ∗
  spqrProbeEnvAtMpl mpl

/-- Explicit-`mpl` relocatable precondition on `check_accelerated::TOKEN` and
`use_accelerated::STORAGE.0` (either already probed as PMULL-accelerated or unprobed). -/
@[expose] def tokenInitPlacedAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  ∃∗ probed : Bool, if probed then tokenProbedPlacedAtMpl mpl else tokenUnprobedPlacedAtMpl mpl

theorem tokenInitPlacedAt_fold [LibsignalPlacement] :
    (lsρ tokenStorageName ↦₈ 1#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
    spqrProbeEnvAt ⊢
    tokenInitPlacedAt :=
  Entails.sepExists_intro (P := fun probed : Bool =>
    if probed then tokenProbedPlacedAt else tokenUnprobedPlacedAt) true

theorem tokenInitPlacedAt_fold_unprobed [LibsignalPlacement] :
    (lsρ tokenStorageName ↦₈ 0xff#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗
    spqrProbeEnvAt ⊢
    tokenInitPlacedAt :=
  Entails.sepExists_intro (P := fun probed : Bool =>
    if probed then tokenProbedPlacedAt else tokenUnprobedPlacedAt) false

theorem tokenProbedPlacedAt_fold [LibsignalPlacement] :
    (lsρ tokenStorageName ↦₈ 1#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
    spqrProbeEnvAt ⊢
    tokenProbedPlacedAt :=
  Entails.refl _

theorem tokenProbedPlacedAt_entails_init [LibsignalPlacement] :
    tokenProbedPlacedAt ⊢ tokenInitPlacedAt :=
  tokenInitPlacedAt_fold

/-- Ghost specification for `std::sys::sync::once::futex::Once::call` on the unprobed SPQR
CPU-feature probe slow path (`STORAGE.0 = 0xff#8, TOKEN + 8 = 3#32 → 1#8, 0#32`). -/
@[expose] def spqrOnceCallGhostSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64) where
  pre := fun (dataPtr, slotPtr) s0 =>
    ⌜LsRetAddrNoProbe (s0.readReg64 .lr) ∧
      s0.readReg64 .x0 = lsρ tokenName + 8#64 ∧
      (s0.readReg64 .x1).truncate 32 = 1#32 ∧
      s0.readReg64 .x2 = dataPtr ∧
      s0.readReg64 .x3 = lsρ spqrLazyLockVtableSym⌝ ∗
    (lsρ tokenStorageName ↦₈ 0xff#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗
    spqrProbeEnvAt ∗
    (dataPtr ↦₆₄ slotPtr) ∗
    (slotPtr ↦₆₄ lsρ tokenName) ∗
    stackAt s0.sp 0xa0
  post := fun (dataPtr, slotPtr) s0 sf =>
    ⌜LibsignalBinary.Heap.VmPreserved s0 sf ∧
      LibsignalBinary.Heap.AllocCallPreserved s0 sf ∧
      sf.trace = s0.trace⌝ ∗
    (lsρ tokenStorageName ↦₈ 1#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
    spqrProbeEnvAt ∗
    (dataPtr ↦₆₄ slotPtr) ∗
    (slotPtr ↦₆₄ 0#64) ∗
    stackAt s0.sp 0xa0
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- External hook assumption for `spqrOnceCallSym` together with address uniqueness of
`lsρ spqrOnceCallSym` among `libsignalSessionExterns`. -/
@[expose] def OnceCallHookOk [LibsignalPlacement]
    (H : String → Option (State → State)) : Prop :=
  HookSat H spqrOnceCallSym spqrOnceCallGhostSpec ∧
  ∀ e ∈ libsignalSessionExterns, lsρ e = lsρ spqrOnceCallSym → e = spqrOnceCallSym

private theorem spqrOnceCallSym_mem_externs :
    spqrOnceCallSym ∈ libsignalSessionExterns := by
  decide

private theorem findSome?_map_off_eq_none_of_none_once {es : List String} {f : String → Nat}
    {H : String → Option (State → State)} {k : Nat}
    (hall : ∀ e ∈ es, f e = k → H e = none) :
    (es.map (fun e => (e, f e))).findSome?
      (fun p => if (p.2 == k) = true then H p.1 else none) = none := by
  induction es with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.map_cons, List.findSome?_cons]
    by_cases hfb : f b = k
    · simp only [beq_iff_eq.mpr hfb, ↓reduceIte, hall b (.head _) hfb]
      exact ih (fun e he => hall e (.tail _ he))
    · simp only [beq_eq_false_iff_ne.mpr hfb, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun e he => hall e (.tail _ he))

private theorem findSome?_map_off_eq_some_once {es : List String} {f : String → Nat}
    {H : String → Option (State → State)} {sym : String}
    (hmem : sym ∈ es) (huniq : ∀ e ∈ es, f e = f sym → e = sym) :
    (es.map (fun e => (e, f e))).findSome?
      (fun p => if (p.2 == f sym) = true then H p.1 else none) = H sym := by
  induction es with
  | nil => cases hmem
  | cons a rest ih =>
    simp only [List.map_cons, List.findSome?_cons]
    by_cases hfa : f a = f sym
    · obtain rfl : a = sym := huniq a (.head _) hfa
      simp only [beq_self_eq_true, ↓reduceIte]
      cases hH : H a with
      | some g => rfl
      | none =>
        exact findSome?_map_off_eq_none_of_none_once fun e he hfe => by
          obtain rfl := huniq e (.tail _ he) hfe
          exact hH
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · exact absurd rfl hfa
      · simp only [beq_eq_false_iff_ne.mpr hfa, Bool.false_eq_true, ↓reduceIte]
        exact ih hrest (fun e he => huniq e (.tail _ he))

private theorem findSome?_const_none_once {α β : Type} (l : List α) :
    l.findSome? (fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem spqr_onceCall_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (hOnce : OnceCallHookOk H) :
    subroutine_ok prog (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec := by
  obtain ⟨⟨f, hf, hok⟩, huniq⟩ := hOnce
  have hextern : prog.externAt? (lsρ spqrOnceCallSym) = H spqrOnceCallSym := by
    rw [hprog.eq_blockProgram]
    have hext := hprog.externs_eq
    have hmem : spqrOnceCallSym ∈ libsignalSessionExterns := spqrOnceCallSym_mem_externs
    have hρ : (libsignalSessionLib.blockPlacement lsmpl i).ρ spqrOnceCallSym =
        lsρ spqrOnceCallSym :=
      ls_blockPlacement_ρ_extern hmem
    unfold Program.externAt? Program.hookAtOff?
    dsimp only [Arm64.Obj.MultiPlacedLib.blockProgram, Arm64.Obj.PlacedLib.program]
    simp only [hext, ← hρ, ite_self, findSome?_const_none_once, Option.or_none]
    refine findSome?_map_off_eq_some_once
      (f := fun e => ((libsignalSessionLib.blockPlacement lsmpl i).ρ e -
        (libsignalSessionLib.blockPlacement lsmpl i).base).toNat)
      (H := H) hmem fun e he hfe => ?_
    have hρe : (libsignalSessionLib.blockPlacement lsmpl i).ρ e = lsρ e :=
      ls_blockPlacement_ρ_extern he
    have hbveq :
        (libsignalSessionLib.blockPlacement lsmpl i).ρ e -
          (libsignalSessionLib.blockPlacement lsmpl i).base =
        (libsignalSessionLib.blockPlacement lsmpl i).ρ spqrOnceCallSym -
          (libsignalSessionLib.blockPlacement lsmpl i).base :=
      BitVec.eq_of_toNat_eq hfe
    have hρeq :
        (libsignalSessionLib.blockPlacement lsmpl i).ρ e =
          (libsignalSessionLib.blockPlacement lsmpl i).ρ spqrOnceCallSym := by
      bv_omega
    exact huniq e he (hρe.symm.trans (hρeq.trans hρ))
  exact subroutine_ok_of_hookOk (hextern.trans hf) hok

/-- Conjoin `⌜VmPreserved s0 sf⌝` onto `spec.post` (definitionally equal to
`LibsignalBinary.Heap.SpecBudget.withVmPreserved`). -/
abbrev addVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜LibsignalBinary.Heap.VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

theorem subroutine_ok_drop_vmPreserved [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addVmPreserved spec))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, addVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

private def vmCore (s : State) :=
  (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail,
    fun fd : { fd : Nat // 3 ≤ fd ∧ fd < 2 ^ 31 } => s.fs.fds (BitVec.ofNat 64 fd.1))

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmPreserved_iff_vmCore (s s' : State) :
    LibsignalBinary.Heap.VmPreserved s s' ↔ (vmCore s' = vmCore s ∧ s'.mem.perm = s.mem.perm) := by
  unfold vmCore LibsignalBinary.Heap.VmPreserved LibsignalBinary.Heap.PoolPreserved
    LibsignalBinary.Heap.FdsHiFrame
  simp only [Prod.mk.injEq, funext_iff, Subtype.forall, and_imp]
  exact ⟨fun ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩,
         fun ⟨⟨h1, h2, h3, h4, h6⟩, h5⟩ => ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setPC (s : State) (pc : BitVec 64) : vmCore (s.setPC pc) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_advancePC (s : State) : vmCore s.advancePC = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setPState (s : State) (ps : PState) : vmCore (s.setPState ps) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_setMem (s : State) (m : Memory) : vmCore (s.setMem m) = vmCore s := by
  unfold vmCore; cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg64 r v) = vmCore s := by
  unfold vmCore; cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmCore (s.writeReg32 r v) = vmCore s := vmCore_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg w r v) = vmCore s := by cases w <;> exact vmCore_writeReg64 s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem vmCore_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    vmCore (applyWriteback s wb) = vmCore s := by
  cases wb with
  | none => rfl
  | some p => exact vmCore_writeReg64 s p.1 p.2

attribute [local irreducible] vmCore

private theorem mem_perm_setMem_of_nsp {s s' : State} {m : Memory}
    (h : ProofLib.NonSyscallPreserved s (s'.setMem m)) :
    m.perm = s.mem.perm :=
  h.2.1

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setMem_loc (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setPC_loc (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_advancePC_loc (s : State) : s.advancePC.mem = s.mem := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_setPState_loc (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg64_loc (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg32_loc (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := mem_writeReg64_loc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_writeReg_loc (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by cases w <;> exact mem_writeReg64_loc s r _
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_applyWriteback_loc (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).mem = s.mem := by
  cases wb with
  | none => rfl
  | some p => exact mem_writeReg64_loc s p.1 p.2
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_perm_write8_loc (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm = m.perm := Memory.perm_write8 m a v
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_perm_write16_loc (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).perm = m.perm := Memory.perm_write16 m a v
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_perm_write32_loc (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).perm = m.perm := Memory.perm_write32 m a v
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_perm_write64_loc (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).perm = m.perm := Memory.perm_write64 m a v
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem mem_perm_writeBytes_loc (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).perm = m.perm := Memory.perm_writeBytes m a bs

private def lsDataAlign8 (sym : String) : Bool :=
  match lsroFind sym with
  | some d => decide (d.align = 8)
  | none => false

private theorem token_align8_mod [LibsignalPlacement] :
    (lsρ tokenName).toNat % 8 = 0 := by
  have hchk : lsDataAlign8 tokenName = true := by decide +kernel
  unfold lsDataAlign8 at hchk
  cases hf : lsroFind tokenName with
  | none => simp [hf] at hchk
  | some d =>
    simp only [hf, decide_eq_true_eq] at hchk
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hf
    have hd := (blkPlaceable_381.data_ok d hmem).2.2.1
    rw [hsym, hchk] at hd
    simpa using hd

private theorem mask3_add8_of_mask7 (x : BitVec 64) (hx : x &&& 7#64 = 0#64) :
    (x + 8#64) &&& 3#64 = 0#64 := by
  revert hx; bv_bits

theorem aligned_tokenOnce_placed [LibsignalPlacement] :
    MemWidth.isAligned .W32 (lsρ tokenName + 8#64) = true := by
  have hmod : (lsρ tokenName &&& 7#64).toNat = 0 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact token_align8_mod
  have hand : lsρ tokenName &&& 7#64 = 0#64 := BitVec.eq_of_toNat_eq hmod
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact mask3_add8_of_mask7 (lsρ tokenName) hand

@[local arm64_norm, local wp_norm]
private theorem polyReduce_asm_eq_trunc (a b_arg : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul a b_arg ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8) >>> 16))) ^^^
        (unaccelerated.polyMul a b_arg ^^^
          BitVec.zeroExtend 32
              (reduce.reduceByteEntry
                (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8).zeroExtend 64) =
      unaccelerated.mul a b_arg := by
  rw [← zeroExtend_16_truncate_32_64]
  exact polyReduce_asm_eq a b_arg

/-- Relocatable `spqr::encoding::gf::unaccelerated::mul` (Block `384`) meets
`addVmPreserved unacceleratedMulPlacedSpec` under `[LibsignalPlacement]`. -/
theorem unacceleratedMul_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (blkPl_384).base
      (addVmPreserved unacceleratedMulPlacedSpec) := by
  simp only [addVmPreserved, unacceleratedMulPlacedSpec]
  wp_init ab s0
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_done

/-- Probed-postcondition variant of `mul2U16PlacedSpec` (post guarantees `tokenProbedPlacedAt`). -/
@[expose] def mul2U16PlacedProbedSpec [LibsignalPlacement] :
    Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp mul2U16Stack
  post := fun (a, b1, b2) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
      BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
      sf.trace = s0.trace⌝ ∗
      tokenProbedPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp mul2U16Stack

/-- Relocatable specification of `spqr::encoding::gf::mul2_u16` (Block `381`) under
`tokenInitPlacedAt`. -/
@[expose] def mul2U16PlacedSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp mul2U16Stack
  post := fun (a, b1, b2) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
      BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
      sf.trace = s0.trace⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp mul2U16Stack

@[local arm64_norm, local wp_norm]
theorem polyReduce_setWidth16_eq (a b_arg : BitVec 16) :
    reduce.reduceByteEntry
      (BitVec.setWidth 8
        ((unaccelerated.polyMul a b_arg ^^^
            BitVec.setWidth 32
                (reduce.reduceByteEntry (BitVec.setWidth 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
              8) >>>
          16)) ^^^
    (BitVec.setWidth 16 (unaccelerated.polyMul a b_arg) ^^^
      reduce.reduceByteEntry (BitVec.setWidth 8 (unaccelerated.polyMul a b_arg >>> 24)) <<< 8) =
    unaccelerated.mul a b_arg := by
  simpa using polyReduce_asm_eq a b_arg

@[local arm64_norm, local wp_norm]
theorem polyReduce_setWidth16_comm_eq (a b_arg : BitVec 16) :
    (BitVec.setWidth 16 (unaccelerated.polyMul a b_arg) ^^^
      reduce.reduceByteEntry (BitVec.setWidth 8 (unaccelerated.polyMul a b_arg >>> 24)) <<< 8) ^^^
    reduce.reduceByteEntry
      (BitVec.setWidth 8
        ((unaccelerated.polyMul a b_arg ^^^
            BitVec.setWidth 32
                (reduce.reduceByteEntry (BitVec.setWidth 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
              8) >>>
          16)) =
    unaccelerated.mul a b_arg := by
  rw [BitVec.xor_comm]; exact polyReduce_setWidth16_eq a b_arg

attribute [local arm64_norm, local wp_norm] mul2UnreducedWord_truncate32

@[local arm64_norm, local wp_norm]
private theorem zext64_trunc32_shr32_mul2Unreduced (a b1 b2 : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32)) =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc32_shr32_mul2Unreduced (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32) =
      unaccelerated.polyMul a b1 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

private theorem mul2U16_tail_52 [LibsignalPlacement]
    (H : String → Option (State → State))
    (hmul : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (lsmpl.base 383)
      (withLsCl lsmpl (addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec)))
    (a b1 b2 : BitVec 16) (s0 s1 : State)
    (vslot vdata : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_381).base + 52#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 64#64)
    (hsp0_al : (s0.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hvm1 : LibsignalBinary.Heap.VmPreserved s0 s1)
    (hcs_v1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx22_1 : s1.readReg64 .x22 = s0.readReg64 .x22)
    (hx23_1 : s1.readReg64 .x23 = s0.readReg64 .x23)
    (hx24_1 : s1.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_1 : s1.readReg64 .x25 = s0.readReg64 .x25)
    (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27)
    (hx28_1 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hx0_1 : BitVec.truncate 16 (s1.readReg64 .x0) = a)
    (hx1_1 : BitVec.truncate 16 (s1.readReg64 .x1) = b1)
    (hx2_1 : BitVec.truncate 16 (s1.readReg64 .x2) = b2)
    {post : State → SepProp → Prop}
    (hpost : ∀ sf Q,
      (Q ⊢ ⌜LibsignalBinary.Heap.VmPreserved s0 sf⌝ ∗
        ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
          BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
          sf.trace = s0.trace⌝ ∗
        tokenProbedPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt s0.sp mul2U16Stack) →
      sf.sp = s0.sp → CallingConventionPreserved s0 sf → post sf Q) :
    SepWP ((blkPC_381).rebase (blkPl_381).base H) (s0.readReg64 .lr) s1
      (memRegion (s0.sp - 256#64) 32 ∗
        stackAt (s0.sp - 64#64) 0xa0 ∗
        memRegion (s0.sp - 64#64) 8 ∗
        ((s0.sp - 56#64) ↦₆₄ vslot) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ vdata) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        tokenProbedPlacedAt ∗
        reduceTablePlacedAt)
      post := by
  simp only [withLsCl, acceleratedMul2UnreducedPlacedSpec] at hmul
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by
    rw [hsp1]; revert hsp0_al; bv_bits
  wp_call hmul (a, b1, b2)
  wp_steps 5
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)),
        uxtx1_hi_idx1_nomask_eq a b1 b2]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtx1_hi_idx1_nomask_eq a b1 b2,
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24)),
        reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul a b2)]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul a b2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24))]
  wp_steps 4
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul a b1 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul a b1 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b1 >>> 24))) <<<
                  8) >>>
              16)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul a b2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul a b2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_steps
  apply SepWP.fold
    (stackAt_256_merge s0.sp vslot
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 21#5))
      vdata
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine hpost _ _ ?_ (by wp_norm_lhs) ?_
  · refine Entails.pure_right (by simp_all [vmPreserved_iff_vmCore]) ?_
    refine Entails.pure_right (by simp_all [wp_norm, mul2U16, polyReduce_setWidth16_eq]) ?_
    exact Entails.of_eq (by ac_rfl)
  · simp_all [CallingConventionPreserved, CalleeSavedPreserved, wp_norm]

/-- Relocatable `spqr::encoding::gf::mul2_u16` (Block `381`, calling Block `383` and optionally
`Once::call` when unprobed) meets `withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedProbedSpec)`. -/
theorem mul2U16_vm_probed_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (blkPl_381).base
      (withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedProbedSpec)) := by
  have hmul0 : subroutine_ok ((blkPC_383).rebase (blkPl_383).base H) (lsmpl.base 383)
      (addVmPreservedAcc acceleratedMul2UnreducedPlacedSpec) :=
    acceleratedMul2Unreduced_vm_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_381).rebase (blkPl_381).base H) hmul0
  have honce : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H)
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  simp only [withLsCodeLoaded, mul2U16PlacedProbedSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_256_split, tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`): `ldar` returns `3#32` → `bl Once::call` → `(1#8, 0#32)`
    wp_simp_pre [tokenUnprobedPlacedAt]
    apply sepWP_seq_lscl h (mid := (blkPl_381).base + 52#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_381).rebase (blkPl_381).base (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
      blkLib_eq_381 (mid := (blkPl_381).base + 196#64)
    intro _m_strip
    wp_steps 6
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 16
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm0 := mem_perm_setMem_of_nsp _hnsp
    wp_call honce
    wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (mul2U16_tail_52 H hmul args.1 args.2.1 args.2.2 s0 _ 0#64 (s0.sp - 56#64) hcl1
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hsp_align (by simp_all [wp_norm])
        (by simp_all [vmPreserved_iff_vmCore]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (by simp_all [wp_norm])
        (fun sf Q hent hsp_f hcc_f =>
          ⟨fun hm => Satisfies.of_entails hm
            (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by simp only [sepConj_assoc]))),
           hsp_f, hcc_f.2⟩))
  · -- Probed fast path (`probed = true`): `ldar` returns `0#32` → `ldrb` returns `1#8`
    wp_simp_pre [tokenProbedPlacedAt]
    apply sepWP_seq_lscl h (mid := (blkPl_381).base + 52#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_381).rebase (blkPl_381).base (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H))
      blkLib_eq_381 (mid := (blkPl_381).base + 52#64)
    intro _m_strip
    wp_steps 6
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign
    · wp_sep_access
    · wp_norm_lhs
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hperm0 := mem_perm_setMem_of_nsp _hnsp
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    apply SepWP.fold tokenProbedPlacedAt_fold (by sep_focus)
    refine SepWP.weaken_pre (by sep_focus)
      (mul2U16_tail_52 H hmul args.1 args.2.1 args.2.2 s0 _ _ _ hcl1
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
        (by simp [vmPreserved_iff_vmCore, hperm0]) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp_all [wp_norm]) (by simp_all [wp_norm]) (by simp_all [wp_norm])
        (fun sf Q hent hsp_f hcc_f =>
          ⟨fun hm => Satisfies.of_entails hm
            (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by simp only [sepConj_assoc]))),
           hsp_f, hcc_f.2⟩))

/-- Relocatable `spqr::encoding::gf::mul2_u16` (Block `381`) meets
`withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedSpec)`. -/
theorem mul2U16_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (blkPl_381).base
      (withLsCodeLoaded lsmpl (addVmPreserved mul2U16PlacedSpec)) := by
  refine subroutine_ok_mono (mul2U16_vm_probed_placed_ok H hOnce)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, addVmPreserved, mul2U16PlacedProbedSpec, mul2U16PlacedSpec] at hq ⊢
  exact Satisfies.of_entails hq (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left tokenProbedPlacedAt_entails_init))))

/-- Relocatable `spqr::encoding::gf::mul2_u16` (Block `381`, calling Block `384`) meets
`withLsCodeLoaded lsmpl mul2U16PlacedSpec` under `[LibsignalPlacement]`. -/
theorem mul2U16_placed_ok [LibsignalPlacement] (H : String → Option (State → State))
    (hOnce : OnceCallHookOk H) :
    subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (blkPl_381).base
      (withLsCodeLoaded lsmpl mul2U16PlacedSpec) :=
  subroutine_ok_drop_vmPreserved (mul2U16_vm_placed_ok H hOnce)

end CryptoVerification.SpqrV1.GF.Mul2U16
