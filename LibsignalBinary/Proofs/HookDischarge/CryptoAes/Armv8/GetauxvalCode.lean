/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.Stack
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.StdDetect
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
meta import ProofLib.StdStartup.StdDetect
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model

/-!
# Placement-Generic `getauxval_hwcap` and `features_aes::init_inner` Machine-Code Proofs

Verifies `cpufeatures`'s AArch64 AES hardware-detection one-shot initializer (`init_inner`) and its
`musl` helpers (`getauxval_hwcap`, `getauxval`, `__errno_location`) with zero ELF layout literals.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup
  (adrpOff checkInstrsAt decodeWord decodeWords hasInstrs hasInstrs_of_wordTree pageLo12)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj step_str8_perm step_str64_perm step_stp64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. Placement-Generic Instruction Lists and `WordTree` Bundle -/

/-- Exact 3-word A64 encoding of `musl`'s `__errno_location` (`mrs x0, TPIDR_EL0; sub x0, x0, #0xa4; ret`). -/
@[expose] def errnoLocationWords : List (BitVec 32) := [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]

/-- Decoded instruction list for `__errno_location`. -/
@[expose] def errnoLocationInstrs : List Instr := decodeWords errnoLocationWords

/-- Placement-generic 25-instruction list for `musl`'s `getauxval` at `getauxvalAddr` referencing
    `__libc` at `libcAddr` (`auxv` at `+0x08`, `secure` at `+0x02`) and `__errno_location`. -/
@[expose] def getauxvalInstrsAt (getauxvalAddr libcAddr errnoLocationAddr : BitVec 64) : List Instr :=
  decodeWords [0xa9be7bfd#32, 0xf1005c1f#32, 0x910003fd#32, 0xf9000bf3#32, 0x54000120#32] ++
  [ .adr true (.gpr 1#5) (adrpOff (getauxvalAddr + 0x14#64) (libcAddr + 0x08#64)),
    .ldr .W64 .X64 false (.gpr 1#5) (.Offset (.gpr 1#5) (pageLo12 (libcAddr + 0x08#64))) ] ++
  decodeWords [0xf9400033#32, 0xeb00027f#32, 0xb4000133#32, 0x540000c0#32, 0x91004021#32, 0x17fffffb#32] ++
  [ .adr true (.gpr 0#5) (adrpOff (getauxvalAddr + 0x34#64) (libcAddr + 0x02#64)),
    .ldr .W32 .B8 false (.gpr 19#5) (.Offset (.gpr 0#5) (pageLo12 (libcAddr + 0x02#64))) ] ++
  decodeWords [0x14000006#32, 0xf9400433#32, 0x14000004#32] ++
  [ .bl (errnoLocationAddr - (getauxvalAddr + 0x48#64)) ] ++
  decodeWords [0x52800041#32, 0xb9000001#32, 0xaa1303e0#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32]

/-- Placement-generic 2-instruction list for `cpufeatures::aarch64::getauxval_hwcap`. -/
@[expose] def getauxvalHwcapInstrs (getauxvalHwcapAddr getauxvalAddr : BitVec 64) : List Instr :=
  [decodeWord 0x52800200#32, .b (getauxvalAddr - (getauxvalHwcapAddr + 4#64))]

/-- Placement-generic 9-instruction list for `features_aes::init_get::init_inner`. -/
@[expose] def aesInitInnerInstrs (initInnerAddr getauxvalHwcapAddr storageAddr : BitVec 64) : List Instr :=
  decodeWords [0xa9bf7bfd#32, 0x910003fd#32] ++
  [ .bl (getauxvalHwcapAddr - (initInnerAddr + 0x08#64)), decodeWord 0xf27d041f#32,
    .adr true (.gpr 8#5) (adrpOff (initInnerAddr + 0x10#64) storageAddr), decodeWord 0x1a9f07e0#32,
    .str .B8 (.gpr 0#5) (.Offset (.gpr 8#5) (pageLo12 storageAddr)) ] ++
  decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]

/-- Code-loading bundle for `features_aes::init_inner` and its transitive callees. -/
structure AesInitInnerCode (P : Program)
    (initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr
     libcAddr storageAddr : BitVec 64) : Prop where
  initInner_code : hasInstrs P initInnerAddr (aesInitInnerInstrs initInnerAddr getauxvalHwcapAddr storageAddr)
  getauxvalHwcap_code : hasInstrs P getauxvalHwcapAddr (getauxvalHwcapInstrs getauxvalHwcapAddr getauxvalAddr)
  getauxval_code : hasInstrs P getauxvalAddr (getauxvalInstrsAt getauxvalAddr libcAddr errnoLocationAddr)
  errnoLocation_code : hasInstrs P errnoLocationAddr errnoLocationInstrs

/-- Construct `AesInitInnerCode` from `WordTree` decidable `checkInstrsAt` checks. -/
theorem AesInitInnerCode.of_wordTree {P : Program} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr
     libcAddr storageAddr : BitVec 64}
    {initOff hwcapOff auxvOff errnoOff : Nat}
    (hInitBase : P.base + BitVec.ofNat 64 initOff = initInnerAddr)
    (hHwcapBase : P.base + BitVec.ofNat 64 hwcapOff = getauxvalHwcapAddr)
    (hAuxvBase : P.base + BitVec.ofNat 64 auxvOff = getauxvalAddr)
    (hErrnoBase : P.base + BitVec.ofNat 64 errnoOff = errnoLocationAddr)
    (hInitBnd : initOff + 36 < 2 ^ 64) (hHwcapBnd : hwcapOff + 8 < 2 ^ 64)
    (hAuxvBnd : auxvOff + 100 < 2 ^ 64) (hErrnoBnd : errnoOff + 12 < 2 ^ 64)
    (h_ext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (h_ovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hInitOk : checkInstrsAt t initOff (aesInitInnerInstrs initInnerAddr getauxvalHwcapAddr storageAddr) = true)
    (hHwcapOk : checkInstrsAt t hwcapOff (getauxvalHwcapInstrs getauxvalHwcapAddr getauxvalAddr) = true)
    (hAuxvOk : checkInstrsAt t auxvOff (getauxvalInstrsAt getauxvalAddr libcAddr errnoLocationAddr) = true)
    (hErrnoOk : checkInstrsAt t errnoOff errnoLocationInstrs = true) :
    AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr libcAddr storageAddr where
  initInner_code := hasInstrs_of_wordTree n hcode hwf hInitBase (by simpa [aesInitInnerInstrs, decodeWords] using hInitBnd) h_ext h_ovr hInitOk
  getauxvalHwcap_code := hasInstrs_of_wordTree n hcode hwf hHwcapBase (by simpa [getauxvalHwcapInstrs] using hHwcapBnd) h_ext h_ovr hHwcapOk
  getauxval_code := hasInstrs_of_wordTree n hcode hwf hAuxvBase (by simpa [getauxvalInstrsAt, decodeWords] using hAuxvBnd) h_ext h_ovr hAuxvOk
  errnoLocation_code := hasInstrs_of_wordTree n hcode hwf hErrnoBase (by simpa [errnoLocationInstrs, errnoLocationWords, decodeWords] using hErrnoBnd) h_ext h_ovr hErrnoOk

/-! ## 2. Auxiliary-Vector Lookup and Hardware-AES Feature Byte -/

/-- Flatten `(tag, val)` `auxv` entries terminated by `(0, nullVal)` into 64-bit words. -/
@[expose] def auxvEntryWords
    (entries : List (BitVec 64 × BitVec 64)) (nullVal : BitVec 64) : List (BitVec 64) :=
  (entries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v]

/-- Result returned by `getauxval(tag)` when scanning `entries` before `(0, nullVal)`. -/
@[expose] def auxvLookupVal
    (tag : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) : BitVec 64 :=
  match entries.find? (·.1 == tag) with
  | some (_, v) => v
  | none => 0#64

/-- Post-call TLS `errno` value after `getauxval(tag)` (`errno0` if found, `ENOENT = 2` if absent). -/
@[expose] def auxvLookupErrno
    (tag : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) (errno0 : BitVec 32) : BitVec 32 :=
  match entries.find? (·.1 == tag) with
  | some _ => errno0
  | none => 2#32

/-- `cpufeatures` `features_aes` flag byte (`1` iff `(hwcap &&& 0x18) != 0`, else `0`). -/
@[expose] def aesHwcapDetectByte (hwcap : BitVec 64) : BitVec 8 :=
  if (hwcap &&& 0x18#64) != 0#64 then 1#8 else 0#8

theorem aesHwcapDetectByte_mem (hwcap : BitVec 64) :
    aesHwcapDetectByte hwcap = 0#8 ∨ aesHwcapDetectByte hwcap = 1#8 := by
  unfold aesHwcapDetectByte; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## 3. 32-Bit Permission-Preserving Store Step and Subroutine Specifications -/

/-- Permission-preserving 32-bit store step (`STR Wt`) carrying `m'.perm = s.mem.perm`. -/
theorem step_str32_perm {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 32}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val
  have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .W32 rt addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  have hn := hnext m' (Memory.perm_write32 s.mem ea val)
  unfold SepWP at hn; exact hn R hm'

/-- Total-correctness contract for `musl`'s `__errno_location`. -/
@[expose] def errnoLocationSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.tpidrEl0 - 0xa4#64 ∧ sf.mem = s0.mem ∧ PureStepPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Total-correctness contract for `getauxval(tag)` on any `tag ≠ 0x17#64` (`AT_SECURE`). -/
@[expose] def getauxvalNonSecureSpec (libcAddr : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 64 × BitVec 64) × BitVec 64 × BitVec 32) where
  pre := fun (tag, auxvPtr, entries, nullVal, errno0) s0 =>
    ⌜s0.readReg64 .x0 = tag ∧ tag ≠ 0x17#64 ∧ ∀ e ∈ entries, e.1 ≠ 0#64⌝ ∗
      (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ stackFrameAt s0.sp 0x20)
  post := fun (tag, auxvPtr, entries, nullVal, errno0) s0 sf =>
    ⌜sf.readReg64 .x0 = auxvLookupVal tag entries ∧ PureStepPreserved s0 sf⌝ ∗
      (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno tag entries errno0) ∗ stackFrameAt s0.sp 0x20)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Total-correctness contract for `cpufeatures::aarch64::getauxval_hwcap` (`tag = 16 = AT_HWCAP`). -/
@[expose] def getauxvalHwcapRawSpec (libcAddr : BitVec 64) :
    Spec (BitVec 64 × List (BitVec 64 × BitVec 64) × BitVec 64 × BitVec 32) where
  pre := fun (auxvPtr, entries, nullVal, errno0) s0 =>
    ⌜∀ e ∈ entries, e.1 ≠ 0#64⌝ ∗
      (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ stackFrameAt s0.sp 0x20)
  post := fun (auxvPtr, entries, nullVal, errno0) s0 sf =>
    ⌜sf.readReg64 .x0 = auxvLookupVal 16#64 entries ∧ PureStepPreserved s0 sf⌝ ∗
      (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno 16#64 entries errno0) ∗ stackFrameAt s0.sp 0x20)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Raw separation-logic contract for `features_aes::init_get::init_inner`. -/
@[expose] def aesInitInnerRawSpec (libcAddr storageAddr : BitVec 64) :
    Spec (BitVec 8 × BitVec 64 × List (BitVec 64 × BitVec 64) × BitVec 64 × BitVec 32) where
  pre := fun (oldVal, auxvPtr, entries, nullVal, errno0) s0 =>
    ⌜∀ e ∈ entries, e.1 ≠ 0#64⌝ ∗
      ((storageAddr ↦₈ oldVal) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗
       (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ stackFrameAt s0.sp 0x30)
  post := fun (_, auxvPtr, entries, nullVal, errno0) s0 sf =>
    let b := aesHwcapDetectByte (auxvLookupVal 16#64 entries)
    ⌜(b = 0#8 ∨ b = 1#8) ∧ sf.readReg64 .x0 = b.zeroExtend 64 ∧ PureStepPreserved s0 sf⌝ ∗
      ((storageAddr ↦₈ b) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗
       (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
       ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno 16#64 entries errno0) ∗ stackFrameAt s0.sp 0x30)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. Machine-Code Verification Proofs -/

private theorem pointsToWords64_auxv_nil (ptr nullVal : BitVec 64) :
    (ptr ↦₆₄ᵣ* auxvEntryWords [] nullVal) = (ptr ↦₆₄ᵣ 0#64) ∗ ((ptr + 8#64) ↦₆₄ᵣ nullVal) := by
  simp [auxvEntryWords]

private theorem pointsToWords64_auxv_cons
    (ptr t v nullVal : BitVec 64) (rest : List (BitVec 64 × BitVec 64)) :
    (ptr ↦₆₄ᵣ* auxvEntryWords ((t, v) :: rest) nullVal) =
      (ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ ((ptr + 16#64) ↦₆₄ᵣ* auxvEntryWords rest nullVal) := by
  simp only [auxvEntryWords, List.cons_append, List.flatMap_cons, List.nil_append,
    pointsToWords64RO_cons, BitVec.add_assoc]
  rw [show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl]

section
arm64_proof_prelude

/-- Verify `__errno_location` (`3` instructions). -/
theorem errnoLocation_ok {P : Program} {errnoLocationAddr : BitVec 64}
    (hc : hasInstrs P errnoLocationAddr errnoLocationInstrs) :
    subroutine_ok P errnoLocationAddr errnoLocationSpec := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _
  dsimp only [errnoLocationSpec] at hpre ⊢
  refine ⟨emp, hpre, ?_⟩
  have_instrs hc 0 3
  wp_steps 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm],
    by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])⟩, by simpa [emp_sepConj] using hm⟩

/-- Loop invariant for `getauxval`'s `(tag, val)` scan from `+0x1c` to `+0x54`, covering both
    the tag-found exit (`+0x40 -> +0x54`) and the `AT_NULL` (`0#64`) exit (`+0x48 -> __errno_location -> +0x54`). -/
private theorem getauxval_scan_loop {P : Program}
    {getauxvalAddr libcAddr errnoLocationAddr : BitVec 64}
    (hc : hasInstrs P getauxvalAddr (getauxvalInstrsAt getauxvalAddr libcAddr errnoLocationAddr))
    (hErrno : subroutine_ok P errnoLocationAddr errnoLocationSpec)
    {target_pc tag nullVal : BitVec 64} {errno0 : BitVec 32}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (entries : List (BitVec 64 × BitVec 64)) (hnonull : ∀ e ∈ entries, e.1 ≠ 0#64) :
    ∀ (ptr : BitVec 64) (s : State) (F : SepProp),
      s.pc = getauxvalAddr + 0x1c#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x0 = tag → s.readReg64 .x1 = ptr →
      (∀ sf : State,
        sf.pc = getauxvalAddr + 0x54#64 → sf.status = .Running → sf.sp = s.sp →
        sf.readReg64 (.gpr 19#5) = auxvLookupVal tag entries →
        CalleeSavedPreserved (s.writeReg64 (.gpr 19#5) (auxvLookupVal tag entries)) sf →
        PureStepPreserved s sf →
        SepWP P target_pc sf
          (((ptr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
            ((s.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno tag entries errno0)) ∗ F) post oom) →
      SepWP P target_pc s
        (((ptr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
          ((s.tpidrEl0 - 0xa4#64) ↦₃₂ errno0)) ∗ F) post oom := by
  induction entries with
  | nil =>
    intro ptr s F hpc hrun hsp hx0 hx1 hnext
    have_instrs hc 7 3; have_instrs hc 18 3
    rw [pointsToWords64_auxv_nil]; wp_steps 4
    refine SepWP.call_subroutine_frame hErrno (x := ())
      (F := ((ptr ↦₆₄ᵣ 0#64) ∗ ((ptr + 8#64) ↦₆₄ᵣ nullVal)) ∗
        ((s.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ F)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; exact hsp)
      (show _ = getauxvalAddr + 0x4c#64 by simp [wp_norm, arm64_norm, bv_lin_norm])
      (fun R hm => by dsimp only [errnoLocationSpec]; exact Satisfies.mono (by sep_entail) hm)
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by wp_close_oom_default)
    dsimp only [errnoLocationSpec]; apply SepWP.pure_elim; rintro ⟨hx0_1, _, hpure1⟩
    simp only [wp_norm, arm64_norm] at hsp1 hx0_1
    have hx19_1 : sf1.readReg64 (.gpr 19#5) = 0#64 := by
      simpa [wp_norm, arm64_norm] using ((CalleeSavedPreserved.iff_regs _ _).mp hcs1).1
    have hpure01 : PureStepPreserved s sf1 :=
      (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])).trans hpure1
    wp_step
    refine step_str32_perm (ea := s.tpidrEl0 - 0xa4#64) (wb := none) (val := 2#32)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      hf_20 rfl (by simp [evalAddrMode, wp_norm, arm64_norm, hx0_1])
      (by simp [wp_norm, arm64_norm]) (by wp_sep_access) fun m2 hm2 => ?_
    have hpost_frame :
        ((((ptr ↦₆₄ᵣ 0#64) ∗ ((ptr + 8#64) ↦₆₄ᵣ nullVal)) ∗
          ((s.tpidrEl0 - 0xa4#64) ↦₃₂ 2#32) ∗ F) =
        (((ptr ↦₆₄ᵣ* auxvEntryWords [] nullVal) ∗
          ((s.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno tag [] errno0)) ∗ F)) := by
      rw [pointsToWords64_auxv_nil]; dsimp only [auxvLookupErrno, List.find?]
      apply Entails.antisymm <;> sep_entail
    rw [hpost_frame]
    refine hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (by simp [auxvLookupVal, wp_norm, arm64_norm, hx19_1]) ?_
      (hpure01.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) hm2))
    dsimp only [auxvLookupVal, List.find?]
    exact CalleeSavedPreserved.trans
      (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs1)
      (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
  | cons kv rest ih =>
    rcases kv with ⟨t, v⟩
    intro ptr s F hpc hrun hsp hx0 hx1 hnext
    have ht0 : t ≠ 0#64 := hnonull (t, v) (List.mem_cons_self ..)
    have_instrs hc 7 6; have_instrs hc 16 2
    rw [pointsToWords64_auxv_cons]; wp_steps 3
    wp_if hcbz
    · exact absurd hcbz ht0
    · wp_step
      wp_if hbeq
      · subst hbeq; wp_steps 2
        have hpost_eq :
            ((((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗
               ((ptr + 16#64) ↦₆₄ᵣ* auxvEntryWords rest nullVal)) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ errno0)) ∗ F) =
            (((ptr ↦₆₄ᵣ* auxvEntryWords ((t, v) :: rest) nullVal) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno t ((t, v) :: rest) errno0)) ∗ F) := by
          rw [pointsToWords64_auxv_cons]; simp [auxvLookupErrno]
        rw [hpost_eq]
        exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm])
          (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
          (by simp [auxvLookupVal, wp_norm, arm64_norm])
          (by simp [auxvLookupVal, Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
          (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]))
      · have hfind_val : auxvLookupVal tag ((t, v) :: rest) = auxvLookupVal tag rest := by
          simp [auxvLookupVal, beq_eq_false_iff_ne.mpr hbeq]
        have hfind_err :
            auxvLookupErrno tag ((t, v) :: rest) errno0 = auxvLookupErrno tag rest errno0 := by
          simp [auxvLookupErrno, beq_eq_false_iff_ne.mpr hbeq]
        wp_steps 2
        have hassoc :
            ((((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗
               ((ptr + 16#64) ↦₆₄ᵣ* auxvEntryWords rest nullVal)) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ errno0)) ∗ F) =
            ((((ptr + 16#64) ↦₆₄ᵣ* auxvEntryWords rest nullVal) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ errno0)) ∗
             ((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ F)) := by
          apply Entails.antisymm <;> sep_entail
        rw [hassoc]
        refine ih (fun e hm => hnonull e (List.mem_cons_of_mem _ hm))
          (ptr + 16#64) _ ((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ F)
          (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; exact hsp)
          (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm])
          fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hpure_f => ?_
        simp only [wp_norm, arm64_norm] at hsp_f hcs_f
        have hassoc_post :
            ((((ptr + 16#64) ↦₆₄ᵣ* auxvEntryWords rest nullVal) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno tag rest errno0)) ∗
             ((ptr ↦₆₄ᵣ t) ∗ ((ptr + 8#64) ↦₆₄ᵣ v) ∗ F)) =
            (((ptr ↦₆₄ᵣ* auxvEntryWords ((t, v) :: rest) nullVal) ∗
              ((s.tpidrEl0 - 0xa4#64) ↦₃₂ auxvLookupErrno tag ((t, v) :: rest) errno0)) ∗ F) := by
          rw [pointsToWords64_auxv_cons, hfind_err]; apply Entails.antisymm <;> sep_entail
        dsimp only [State.writeReg64, State.setPState, State.setPC]
        rw [hassoc_post]
        refine hnext sf hpc_f hrun_f hsp_f (by rwa [hfind_val]) ?_
          ((PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])).trans hpure_f)
        rw [hfind_val]
        exact CalleeSavedPreserved.trans
          (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f

/-- Verify `getauxval` for any `tag ≠ 0x17#64`, covering both found and `AT_NULL` (`ENOENT`) paths. -/
theorem getauxval_nonSecure_ok {P : Program}
    {getauxvalAddr libcAddr errnoLocationAddr : BitVec 64}
    (hc : hasInstrs P getauxvalAddr (getauxvalInstrsAt getauxvalAddr libcAddr errnoLocationAddr))
    (hErrno : subroutine_ok P errnoLocationAddr errnoLocationSpec) :
    subroutine_ok P getauxvalAddr (getauxvalNonSecureSpec libcAddr) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨tag, auxvPtr, entries, nullVal, errno0⟩ R s0 hpc hrun hpre hsp
  dsimp only [getauxvalNonSecureSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, htag17, hnonull⟩, hpre⟩
  refine ⟨((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
    ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have hsf : stackFrameAt s0.sp 0x20 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]
  wp_conv_pre => rw [hsf]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  have_instrs hc 0 7; have_instrs hc 21 4
  refine step_stp64_perm (ea2 := s0.sp - 24#64) hf_0 hpc hrun
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-32#64)) = (s0.sp - 32#64, some (.sp, s0.sp - 32#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) rfl fun m1 hm1 => ?_
  wp_steps 2
  refine step_str64_perm (ea := s0.sp - 16#64) (wb := none) (val := s0.readReg64 (.gpr 19#5)) hf_3
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned,
      wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) rfl fun m2 hm2 => ?_
  wp_step
  wp_if hbeq17
  · exact absurd (by simpa [wp_norm, arm64_norm, hx0] using hbeq17) htag17
  · wp_steps 2
    have hrearr_in :
        (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
         ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗
         (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 8#64) ↦₆₄ w3))) =
        (((auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗ ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0)) ∗
         (((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 8#64) ↦₆₄ w3))) := by
      apply Entails.antisymm <;> sep_entail
    rw [hrearr_in]
    refine getauxval_scan_loop hc hErrno (tag := tag) entries hnonull auxvPtr _ _
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; bv_bits)
      (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm])
      fun sf hpc_f hrun_f hsp_f hx19_f hcs_f hpure_f => ?_
    have hsp_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hsp ⊢; rw [hsp_f]; simp only [wp_norm, arm64_norm] at *; bv_bits
    have hpure_pre : PureStepPreserved s0 sf :=
      (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (hm2.trans hm1)).trans hpure_f
    wp_steps 4
    apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun_f])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm],
        hpure_pre.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]))⟩, Satisfies.mono (sepConj_mono_left ?_) hm⟩
      rw [hsf]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
            (Entails.sepExists_right (s0.readReg64 (.gpr 30#5))
              (Entails.sepExists_right (s0.readReg64 (.gpr 19#5))
                (Entails.sepExists_right w3 (Entails.refl _))))))))
      sep_entail
    · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with
        ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
      simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
      rw [CalleeSavedPreserved.iff_regs]
      simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

/-- Verify `cpufeatures::aarch64::getauxval_hwcap` (`mov w0, #0x10; b getauxvalAddr`). -/
theorem getauxvalHwcap_ok {P : Program}
    {getauxvalHwcapAddr getauxvalAddr libcAddr errnoLocationAddr : BitVec 64}
    (hHwcap : hasInstrs P getauxvalHwcapAddr (getauxvalHwcapInstrs getauxvalHwcapAddr getauxvalAddr))
    (hAuxv : hasInstrs P getauxvalAddr (getauxvalInstrsAt getauxvalAddr libcAddr errnoLocationAddr))
    (hErrno : subroutine_ok P errnoLocationAddr errnoLocationSpec) :
    subroutine_ok P getauxvalHwcapAddr (getauxvalHwcapRawSpec libcAddr) := by
  have hSub := getauxval_nonSecure_ok hAuxv hErrno
  apply subroutine_ok_of_sepWP_init
  rintro ⟨auxvPtr, entries, nullVal, errno0⟩ R s0 hpc hrun hpre hsp
  dsimp only [getauxvalHwcapRawSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hnonull, hpre⟩
  refine ⟨((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗
    ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗ stackFrameAt s0.sp 0x20, hpre, ?_⟩
  have_instrs hHwcap 0 2; wp_steps 2
  refine SepWP.call_subroutine_frame hSub (x := (16#64, auxvPtr, entries, nullVal, errno0))
    (F := emp) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; exact hsp)
    (show _ = s0.readReg64 .lr by simp [wp_norm, arm64_norm])
    (fun R' hm => by
      dsimp only [getauxvalNonSecureSpec] at hm ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], by decide, hnonull⟩, Satisfies.mono (by sep_entail) hm⟩)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_) (by wp_close_oom_default)
  dsimp only [getauxvalNonSecureSpec]; rw [sepConj_assoc]; apply SepWP.pure_elim
  rintro ⟨hx0_f, hpure_f⟩; simp only [wp_norm, arm64_norm] at hsp_f
  apply SepWP.done hpc_f hrun_f
  refine ⟨fun hm => ?_, hsp_f,
    CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])).trans hpure_f⟩, Satisfies.mono (by sep_entail) hm⟩

private theorem tst_cset_aes_eq (hwcap : BitVec 64) :
    (if (hwcap &&& 24#64 == 0#64) = true then (0#64 : BitVec 64) else 1#64) =
      (aesHwcapDetectByte hwcap).zeroExtend 64 := by
  unfold aesHwcapDetectByte; by_cases h : (hwcap &&& 24#64) = 0#64 <;> simp [h]

/-- Verify `features_aes::init_get::init_inner` (`9` instructions) over explicit `auxv` and `errno`. -/
theorem aesInitInnerRaw_ok {P : Program}
    {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr
     libcAddr storageAddr : BitVec 64}
    (hCode : AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr
      errnoLocationAddr libcAddr storageAddr) :
    subroutine_ok P initInnerAddr (aesInitInnerRawSpec libcAddr storageAddr) := by
  have hHwcapSub := getauxvalHwcap_ok hCode.getauxvalHwcap_code
    hCode.getauxval_code (errnoLocation_ok hCode.errnoLocation_code)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨oldVal, auxvPtr, entries, nullVal, errno0⟩ R s0 hpc hrun hpre hsp
  dsimp only [aesInitInnerRawSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hnonull, hpre⟩
  refine ⟨(storageAddr ↦₈ oldVal) ∗ ((libcAddr + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗
    (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗ ((s0.tpidrEl0 - 0xa4#64) ↦₃₂ errno0) ∗
    stackFrameAt s0.sp 0x30, hpre, ?_⟩
  have hsf30 : stackFrameAt s0.sp 0x30 =
      stackFrameAt (s0.sp - 16#64) 0x20 ∗
        (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
          ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)) := by
    rw [← stackAt_eq_stackFrameAt s0.sp 0x30, stackAt_frame s0.sp 0x30 2 (by decide),
      stackAt_eq_stackFrameAt (s0.sp - 16#64) 0x20]; cells_unfold
  wp_conv_pre => rw [hsf30]; simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  have_instrs hCode.initInner_code 0 9
  refine step_stp64_perm (ea2 := s0.sp - 8#64) hf_0 hpc hrun
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp])
    (show evalAddrMode s0 (.PreIndex .sp (-16#64)) = (s0.sp - 16#64, some (.sp, s0.sp - 16#64)) by
      simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) rfl fun m1 hm1 => ?_
  wp_steps 2
  have htp_c : (((((s0.writeReg64 .sp (s0.sp - 16#64)).writeReg64 (.gpr 29#5) (s0.sp - 16#64)).writeReg64
        (.gpr 30#5) (initInnerAddr + 12#64)).setPC
      (initInnerAddr + 8#64 + (getauxvalHwcapAddr - (initInnerAddr + 8#64)))).setMem m1).tpidrEl0 =
        s0.tpidrEl0 := by simp [wp_norm, arm64_norm]
  have hsp_c : (((((s0.writeReg64 .sp (s0.sp - 16#64)).writeReg64 (.gpr 29#5) (s0.sp - 16#64)).writeReg64
        (.gpr 30#5) (initInnerAddr + 12#64)).setPC
      (initInnerAddr + 8#64 + (getauxvalHwcapAddr - (initInnerAddr + 8#64)))).setMem m1).sp =
        s0.sp - 16#64 := by simp [wp_norm, arm64_norm]
  refine SepWP.call_subroutine_frame hHwcapSub (x := (auxvPtr, entries, nullVal, errno0))
    (F := (storageAddr ↦₈ oldVal) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm] at hsp ⊢; bv_bits)
    (show _ = initInnerAddr + 0x0c#64 by simp [wp_norm, arm64_norm, bv_lin_norm])
    (fun R' hm => by
      dsimp only [getauxvalHwcapRawSpec] at hm ⊢
      rw [htp_c, hsp_c, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hnonull, Satisfies.mono (by sep_entail) hm⟩)
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_) (by wp_close_oom_default)
  dsimp only [getauxvalHwcapRawSpec]; rw [htp_c, hsp_c, sepConj_assoc]; apply SepWP.pure_elim
  rintro ⟨hx0_1, hpure1⟩; simp only [wp_norm, arm64_norm] at hsp1
  have hpure01 : PureStepPreserved s0 sf1 :=
    (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) hm1).trans hpure1
  let b := aesHwcapDetectByte (auxvLookupVal 16#64 entries)
  wp_steps 3
  refine step_str8_perm (ea := storageAddr) (wb := none) (val := b) hf_6
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    rfl (by simp [evalAddrMode, wp_norm, arm64_norm])
    (by dsimp only [b, aesHwcapDetectByte]
        simp only [wp_norm, arm64_norm]
        by_cases h : (auxvLookupVal 16#64 entries &&& 24#64) = 0#64 <;> simp [h])
    (by wp_sep_access) rfl fun m2 hm2 => ?_
  have hsp_sf1 : sf1.spAligned = true := by simp only [State.spAligned] at hsp ⊢; rw [hsp1]; bv_bits
  wp_steps 2
  apply SepWP.done (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, bv_lin_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨aesHwcapDetectByte_mem _, ?_,
      hpure01.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hm2))⟩,
      Satisfies.mono (sepConj_mono_left ?_) hm⟩
    · simp only [wp_norm, arm64_norm]
      exact tst_cset_aes_eq (auxvLookupVal 16#64 entries)
    · rw [hsf30]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (Entails.sepExists_right (s0.readReg64 (.gpr 29#5))
            (Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) (Entails.refl _))))))))
      sep_entail
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with
      ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]
    simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
