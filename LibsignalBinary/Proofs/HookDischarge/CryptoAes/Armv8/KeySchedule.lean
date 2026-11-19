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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeyScheduleAux
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
meta import ProofLib.StdStartup.StdDetect

/-!
# ARMv8 Hardware AES-256 Key Schedule (`Armv8.KeySchedule`)

Placement- and relocation-generic (`hasInstrs`) `subroutine_ok` verification of the `aes` `0.9.1`
`aes::armv8::expand` routines:
- `expand_key::<32, 15>` (`70` reachable instructions / `73` total symbol words, `0x100` B stack,
  relocation-parameterized `RCON` `ADRP + ADD` with zero raw address literals);
- `inv_expanded_keys::<15>` (`30` position-independent instructions, re-exported from
  `Armv8.InvExpand`), plus `↦ₛ` / `memRegion` ↔ `roundKeys15At` bridges.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (aesRconWords aesRconBytes armv8SubWord armv8ExpandStep armv8ExpandKeyWords
   armv8ExpandKey armv8InvExpandedKeys roundKeys15Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (expandWords60At expandWords60At_eq_roundKeys15At map_decode_eq_of_all_isSome
   SepLoad32.of_expandWords60At SepStore32.of_expandWords60At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeyScheduleAux
  (expandKeySeg0Words expandKeyPrologueTailWords expandKeyLoopJoinWords
   expandKeyLoopHdrWords expandKeyEpilogueWords step_str32_perm step_bCond step_cbz64
   sepLoad32_of_bytesAt dup4s_expanded_eq
   truncate32_aese_dup_eq_armv8SubWord armv8InitWords epilogue_stack_entails_stackFrameAt256
   calleeSavedGprs19_28 ExpandInv k_lsl2_eq k_prev_off_eq k_out_off_eq k_inc_eq k_cmp52_iff
   k_mod8_eq4_iff k_mod8_eq0_iff k_div8_ne0 k_rcon_off_eq k_rcon_word_eq prologue_sepWP)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved adrpAddPair adrpAddPair_length hasInstrs_prefix)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand.Simp
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

/-! ## 1. Re-Exports from `InvExpand` (`roundKeys15At` Bridges & `inv_expanded_keys::<15>`) -/

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (bytesToRoundKeys15 roundKeys15Bytes_length roundKeys15At_eq_pointsToBytes
   roundKeys15Bytes_bytesToRoundKeys15 pointsToBytes240_eq_roundKeys15At)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (roundKeys15At_entails_memRegion memRegion240_eq_exists_roundKeys15At
   invExpandedKeys15Words invExpandedKeys15Instrs invExpandedKeys15Instrs_template_eq)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.InvExpand
  (invExpandedKeys15Spec invExpandedKeys15RegionSpec
   invExpandedKeys15_subroutine_ok invExpandedKeys15_region_subroutine_ok)

/-! ## 2. Relocation-Generic `expand_key::<32, 15>` Instruction Sequence & Template Check -/

@[expose] def expandKeySeg1Words : List (BitVec 32) :=
  expandKeyPrologueTailWords ++ expandKeyLoopJoinWords ++
    expandKeyLoopHdrWords ++ expandKeyEpilogueWords

/-- Relocation-generic 70-instruction reachable prefix (`+0x000..+0x114`, ending at `ret`) of
    `aes::armv8::expand::expand_key::<32, 15>`. -/
@[expose] def expandKey15ReachableInstrs (fnAddr rconAddr : BitVec 64)
    (relaxRcon : Bool := false) : List Instr :=
  decodeWords expandKeySeg0Words ++
  adrpAddPair (.gpr 10#5) (fnAddr + 0x44#64) rconAddr relaxRcon ++
  decodeWords expandKeySeg1Words

/-- Complete 73-word unrelocated `.rlib` template of `expand_key::<32, 15>`. -/
@[expose] def expandKey15TemplateWords : List (BitVec 32) :=
  expandKeySeg0Words ++ [0x9000000a#32, 0x9100014a#32] ++ expandKeySeg1Words ++
  [0x90000000#32, 0x91000000#32, 0x94000000#32]

/-- Relocation parameters for the full 73-instruction symbol of `expand_key::<32, 15>`
    (including the unreachable 3-instruction `panic_const_sub_overflow` cold block at `+0x118`). -/
structure ExpandKey15Syms where
  fnAddr : BitVec 64
  rconAddr : BitVec 64
  panicLoc : BitVec 64
  panicTarget : BitVec 64
  relaxRcon : Bool := false
  relaxPanic : Bool := false

/-- Unrelocated `.rlib` template instance of `ExpandKey15Syms` at `fnAddr`. -/
@[expose] def ExpandKey15Syms.template (fnAddr : BitVec 64 := 0#64) : ExpandKey15Syms :=
  let page := fnAddr &&& 0xfffffffffffff000#64
  { fnAddr := fnAddr, rconAddr := page, panicLoc := page, panicTarget := fnAddr + 0x120#64 }

/-- Full 73-instruction sequence of `expand_key::<32, 15>` (reachable prefix + cold panic tail). -/
@[expose] def expandKey15FullInstrs (p : ExpandKey15Syms) : List Instr :=
  expandKey15ReachableInstrs p.fnAddr p.rconAddr p.relaxRcon ++
  (adrpAddPair (.gpr 0#5) (p.fnAddr + 0x118#64) p.panicLoc p.relaxPanic ++
   [ .bl (p.panicTarget - (p.fnAddr + 0x120#64)) ])

theorem expandKey15ReachableInstrs_length (fnAddr rconAddr : BitVec 64) (relaxRcon : Bool) :
    (expandKey15ReachableInstrs fnAddr rconAddr relaxRcon).length = 70 := by
  simp only [expandKey15ReachableInstrs, List.length_append, adrpAddPair_length]
  have h0 : (decodeWords expandKeySeg0Words).length = 17 := rfl
  have h1 : (decodeWords expandKeySeg1Words).length = 51 := rfl
  omega

theorem expandKey15FullInstrs_length (p : ExpandKey15Syms) :
    (expandKey15FullInstrs p).length = 73 := by
  simp [expandKey15FullInstrs, expandKey15ReachableInstrs_length, adrpAddPair_length]

theorem expandKey15FullInstrs_template_eq :
    expandKey15TemplateWords.map Arm64.decode =
      (expandKey15FullInstrs (ExpandKey15Syms.template 0#64)).map some := by
  have hall : expandKey15TemplateWords.all (fun w => (Arm64.decode w).isSome) = true := by decide
  rw [map_decode_eq_of_all_isSome _ hall]
  exact congrArg (List.map some) (by decide)

private theorem hasInstrs_expandKey_parts {P : Program} {fnAddr rconAddr : BitVec 64}
    {relaxRcon : Bool}
    (hc : hasInstrs P fnAddr (expandKey15ReachableInstrs fnAddr rconAddr relaxRcon)) :
    hasInstrs P fnAddr (decodeWords expandKeySeg0Words) ∧
    hasInstrs P (fnAddr + 0x44#64)
      (adrpAddPair (.gpr 10#5) (fnAddr + 0x44#64) rconAddr relaxRcon) ∧
    hasInstrs P (fnAddr + 0x4c#64) (decodeWords expandKeyPrologueTailWords) ∧
    hasInstrs P (fnAddr + 0x68#64) (decodeWords expandKeyLoopJoinWords) ∧
    hasInstrs P (fnAddr + 0x8c#64) (decodeWords expandKeyLoopHdrWords) ∧
    hasInstrs P (fnAddr + 0xcc#64) (decodeWords expandKeyEpilogueWords) := by
  dsimp only [expandKey15ReachableInstrs, expandKeySeg1Words] at hc
  simp only [decodeWords, List.map_append, List.append_assoc] at hc ⊢
  obtain ⟨hc0, hc⟩ := hc.split_append (off := 0x44#64) rfl
  obtain ⟨hcRcon, hc⟩ := hc.split_append (off := 0x08#64) (by rw [adrpAddPair_length])
  obtain ⟨hcTail, hc⟩ := hc.split_append (off := 0x1c#64) rfl
  obtain ⟨hcJoin, hc⟩ := hc.split_append (off := 0x24#64) rfl
  obtain ⟨hcHdr, hcEpi⟩ := hc.split_append (off := 0x40#64) rfl
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcTail hcJoin hcHdr hcEpi
  exact ⟨hc0, hcRcon, hcTail, hcJoin, hcHdr, hcEpi⟩

/-! ## 3. Hoare Contracts (`expandKey15Spec`, `expandKey15RegionSpec`) -/

/-- Total-correctness Hoare contract for `expand_key::<32, 15>` over `roundKeys15At outPtr oldRks`. -/
@[expose] def expandKey15Spec (rconAddr : BitVec 64) :
    Spec (Bool × Bool × BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × List (BitVec 8)) where
  pre := fun (roKey, roRcon, outPtr, keyPtr, oldRks, keyBytes) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧ s0.readReg64 .x1 = keyPtr ∧ keyBytes.length = 32⌝ ∗
    (roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
     bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)
  post := fun (roKey, roRcon, outPtr, keyPtr, _oldRks, keyBytes) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.readReg64 .x0 = outPtr⌝ ∗
    (roundKeys15At outPtr (armv8ExpandKey keyBytes) ∗ bytesAt roKey keyPtr keyBytes ∗
     bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Region-destination Hoare contract (`memRegion outPtr 240`) for `expand_key::<32, 15>`. -/
@[expose] def expandKey15RegionSpec (rconAddr : BitVec 64) :
    Spec (Bool × Bool × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (roKey, roRcon, outPtr, keyPtr, keyBytes) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧ s0.readReg64 .x1 = keyPtr ∧ keyBytes.length = 32⌝ ∗
    (memRegion outPtr 240 ∗ bytesAt roKey keyPtr keyBytes ∗
     bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)
  post := fun (roKey, roRcon, outPtr, keyPtr, keyBytes) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.readReg64 .x0 = outPtr⌝ ∗
    (roundKeys15At outPtr (armv8ExpandKey keyBytes) ∗ bytesAt roKey keyPtr keyBytes ∗
     bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. 52-Iteration Key-Expansion Loop & Epilogue `SepWP` Proofs -/

private theorem loopJoin_sepWP {P : Program} {target_pc fnAddr outPtr rconAddr : BitVec 64}
    {ws : Vector (BitVec 32) 60} {k : Fin 52} {transformed : BitVec 32} {F : SepProp}
    {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcJoin : hasInstrs P (fnAddr + 0x68#64) (decodeWords expandKeyLoopJoinWords))
    (hpc : s.pc = fnAddr + 0x74#64) (hrun : s.status = .Running)
    (hinv : ExpandInv s0 outPtr rconAddr s)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 k.val)
    (hx11 : s.readReg64 (.gpr 11#5) = (s0.sp - 0x100#64) + BitVec.ofNat 64 (4 * k.val))
    (hw12 : s.readReg32 (.gpr 12#5) = transformed)
    (htrans : transformed =
      if (k.val + 8) % 8 = 4 then armv8SubWord ws[k.val + 7]
      else if (k.val + 8) % 8 = 0 then
        aesRconWords.getD ((k.val + 8) / 8 - 1) 0#32 ^^^ (armv8SubWord ws[k.val + 7]).rotateRight 8
      else ws[k.val + 7])
    (hnext : ∀ s' : State,
      s'.pc = (if k.val + 1 = 52 then fnAddr + 0xcc#64 else fnAddr + 0x8c#64) →
      s'.status = .Running → ExpandInv s0 outPtr rconAddr s' →
      s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (k.val + 1) →
      SepWP P target_pc s' (expandWords60At (s0.sp - 0x100#64) (armv8ExpandStep ws k) ∗ F) post oom) :
    SepWP P target_pc s (expandWords60At (s0.sp - 0x100#64) ws ∗ F) post oom := by
  have_instrs hcJoin 3 6
  apply SepWP.step_ldr32 (ea := (s0.sp - 0x100#64) + BitVec.ofNat 64 (4 * k.val)) (wb := none)
    hpc hrun hf_3 (by wp_focus_close wp_norm_lhs)
    (by simp [evalAddrMode, wp_norm, arm64_norm, hinv.x9_eq, hx8, k_lsl2_eq])
    (SepLoad32.of_expandWords60At (by omega) rfl) rfl
  try wp_norm_state
  wp_steps 3
  apply step_str32_perm (ea := (s0.sp - 0x100#64) + BitVec.ofNat 64 (4 * k.val) + 32#64)
    (wb := none) hf_7 (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by wp_focus_close wp_norm_lhs) (by wp_focus_close wp_norm_lhs)
    (by simp [evalAddrMode, wp_norm, arm64_norm, hx11]) rfl
    (SepStore32.of_expandWords60At (idx := k.val + 8) (by omega)
      (by rw [BitVec.add_assoc, k_out_off_eq])) rfl
  intro m1 hm1
  try wp_norm_state
  apply step_bCond (taken := decide (k.val + 1 = 52))
    (nextPc := if k.val + 1 = 52 then fnAddr + 0xcc#64 else fnAddr + 0x8c#64)
    hf_8 (by simp [wp_norm, arm64_norm]; try bv_lin) (by wp_focus_close wp_norm_lhs)
    (by by_cases hk52 : k.val + 1 = 52 <;> simp [wp_norm, arm64_norm, k_inc_eq, k_cmp52_iff, hk52])
    (by by_cases hk52 : k.val + 1 = 52 <;> simp [hk52])
  try wp_norm_state
  have hstep_eq : ws.setIfInBounds (k.val + 8) (ws[k.val] ^^^ transformed) = armv8ExpandStep ws k := by
    dsimp only [armv8ExpandStep]; rw [htrans]
  have hw12_trunc : (s.readReg64 (.gpr 12#5)).truncate 32 = transformed := hw12
  simp only [wp_norm, arm64_norm, hw12_trunc, hstep_eq]
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    (by simp [wp_norm, arm64_norm, k_inc_eq])
  exact hinv.step
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm1])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedGprs19_28, wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])

set_option maxHeartbeats 400000 in
private theorem loopIter_sepWP {P : Program} {target_pc fnAddr outPtr rconAddr : BitVec 64}
    {roRcon : Bool} {ws : Vector (BitVec 32) 60} {k : Fin 52} {F : SepProp}
    {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcJoin : hasInstrs P (fnAddr + 0x68#64) (decodeWords expandKeyLoopJoinWords))
    (hcHdr : hasInstrs P (fnAddr + 0x8c#64) (decodeWords expandKeyLoopHdrWords))
    (hpc : s.pc = fnAddr + 0x8c#64) (hrun : s.status = .Running)
    (hinv : ExpandInv s0 outPtr rconAddr s)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 k.val)
    (hnext : ∀ s' : State,
      s'.pc = (if k.val + 1 = 52 then fnAddr + 0xcc#64 else fnAddr + 0x8c#64) →
      s'.status = .Running → ExpandInv s0 outPtr rconAddr s' →
      s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (k.val + 1) →
      SepWP P target_pc s'
        (expandWords60At (s0.sp - 0x100#64) (armv8ExpandStep ws k) ∗
         bytesAt roRcon rconAddr aesRconBytes ∗ F) post oom) :
    SepWP P target_pc s
      (expandWords60At (s0.sp - 0x100#64) ws ∗ bytesAt roRcon rconAddr aesRconBytes ∗ F) post oom := by
  have_instrs hcHdr 0 16
  wp_steps 3
  apply SepWP.step_ldr32 (ea := (s0.sp - 0x100#64) + BitVec.ofNat 64 (4 * k.val) + 28#64)
    (wb := none) (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by wp_focus_close wp_norm_lhs) hf_3 (by wp_focus_close wp_norm_lhs)
    (by simp [evalAddrMode, wp_norm, arm64_norm, hinv.x9_eq, k_lsl2_eq])
    (SepLoad32.of_expandWords60At (idx := k.val + 7) (by omega)
      (by rw [BitVec.add_assoc, k_prev_off_eq])) rfl
  try wp_norm_state
  wp_steps 1
  by_cases h4 : k.val % 8 = 4
  · apply step_bCond (taken := true) (nextPc := fnAddr + 0x68#64) hf_5
      (by simp [wp_norm, arm64_norm]; try bv_lin) (by wp_focus_close wp_norm_lhs)
      (by simp [wp_norm, arm64_norm, k_mod8_eq4_iff, h4]) (by simp; try bv_lin)
    try wp_norm_state
    clear hf_0 hf_1 hf_2
    have_instrs hcJoin 0 3
    wp_steps 3
    refine loopJoin_sepWP hcJoin (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun])
      (hinv.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedGprs19_28, wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, isCalleeSavedVReg]))
      (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hinv.x9_eq, k_lsl2_eq])
      rfl ?_ hnext
    simp [wp_norm, arm64_norm, h4, hinv.v0_eq, dup4s_expanded_eq,
      truncate32_aese_dup_eq_armv8SubWord]
  · apply step_bCond (taken := false) (nextPc := fnAddr + 0xa4#64) hf_5
      (by simp [wp_norm, arm64_norm]; try bv_lin) (by wp_focus_close wp_norm_lhs)
      (by simp [wp_norm, arm64_norm, k_mod8_eq4_iff, h4]) (by simp; try bv_lin)
    try wp_norm_state
    by_cases h0 : k.val % 8 = 0
    · apply step_cbz64 (taken := false) (nextPc := fnAddr + 0xa8#64) hf_6
        (by simp [wp_norm, arm64_norm]) (by wp_focus_close wp_norm_lhs)
        (by simp [wp_norm, arm64_norm, k_mod8_eq0_iff, h0]) (by simp; try bv_lin)
      try wp_norm_state
      wp_steps 1
      apply step_cbz64 (taken := false) (nextPc := fnAddr + 0xb0#64) hf_8
        (by simp [wp_norm, arm64_norm]; try bv_lin) (by wp_focus_close wp_norm_lhs)
        (by simp [wp_norm, arm64_norm, k_div8_ne0]) (by simp; try bv_lin)
      try wp_norm_state
      wp_steps 2
      have hreord : expandWords60At (s0.sp - 0x100#64) ws ∗ bytesAt roRcon rconAddr aesRconBytes ∗ F =
          bytesAt roRcon rconAddr aesRconBytes ∗ (expandWords60At (s0.sp - 0x100#64) ws ∗ F) := by
        sep_ac_rfl
      rw [hreord]
      have hq : 4 * ((k.val + 8) / 8 - 1) + 4 ≤ aesRconBytes.length := by
        have hlen : aesRconBytes.length = 40 := rfl
        omega
      apply SepWP.step_ldr32
        (ea := rconAddr + (((BitVec.ofNat 64 k.val + 8#64) >>> 3) <<< 2) + 0xfffffffffffffffc#64)
        (wb := none) (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by wp_focus_close wp_norm_lhs) hf_11 (by wp_focus_close wp_norm_lhs)
        (by simp [evalAddrMode, wp_norm, arm64_norm, hinv.x10_eq])
        (sepLoad32_of_bytesAt (off := 4 * ((k.val + 8) / 8 - 1)) (F := _) rfl hq
          (by rw [BitVec.add_assoc, ← k_rcon_off_eq])) rfl
      rw [← hreord]
      try wp_norm_state
      wp_steps 4
      refine loopJoin_sepWP hcJoin (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (hinv.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedGprs19_28, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, isCalleeSavedVReg]))
        (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hinv.x9_eq, k_lsl2_eq])
        rfl ?_ hnext
      simp [wp_norm, arm64_norm, h0, k_rcon_word_eq k, hinv.v0_eq, dup4s_expanded_eq,
        truncate32_aese_dup_eq_armv8SubWord]
    · apply step_cbz64 (taken := true) (nextPc := fnAddr + 0x74#64) hf_6
        (by simp [wp_norm, arm64_norm]) (by wp_focus_close wp_norm_lhs)
        (by simp [wp_norm, arm64_norm, k_mod8_eq0_iff, h0]) (by simp; try bv_lin)
      try wp_norm_state
      refine loopJoin_sepWP hcJoin (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (hinv.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp [calleeSavedGprs19_28, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]))
        (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hinv.x9_eq, k_lsl2_eq])
        rfl
        (by simp [wp_norm, arm64_norm, h4, h0]) hnext

private def foldExpandSteps (ws0 : Vector (BitVec 32) 60) : Nat → Vector (BitVec 32) 60
  | 0 => ws0
  | n + 1 =>
    if h : n < 52 then armv8ExpandStep (foldExpandSteps ws0 n) ⟨n, h⟩ else foldExpandSteps ws0 n

private theorem foldExpandSteps_52_eq (keyBytes : List (BitVec 8)) :
    foldExpandSteps (armv8InitWords keyBytes) 52 = armv8ExpandKeyWords keyBytes := by
  have hfold : ∀ (n : Nat) (hn : n ≤ 52),
      foldExpandSteps (armv8InitWords keyBytes) n =
        Fin.foldl n (fun acc (j : Fin n) => armv8ExpandStep acc ⟨j.val, by omega⟩)
          (armv8InitWords keyBytes) := by
    intro n hn
    induction n with
    | zero => rfl
    | succ m ih =>
      have hm : m < 52 := by omega
      simp only [foldExpandSteps, hm, ↓reduceDIte, Fin.foldl_succ_last, Fin.val_last,
        Fin.val_castSucc, ih (by omega)]
  exact hfold 52 (Nat.le_refl 52)

private theorem loopFrom_sepWP {P : Program} {target_pc fnAddr outPtr rconAddr : BitVec 64}
    {roRcon : Bool} {ws0 : Vector (BitVec 32) 60} {F : SepProp}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcJoin : hasInstrs P (fnAddr + 0x68#64) (decodeWords expandKeyLoopJoinWords))
    (hcHdr : hasInstrs P (fnAddr + 0x8c#64) (decodeWords expandKeyLoopHdrWords))
    (rem : Nat) (hrem : rem ≤ 52) :
    ∀ s : State,
      s.pc = (if 52 - rem = 52 then fnAddr + 0xcc#64 else fnAddr + 0x8c#64) →
      s.status = .Running → ExpandInv s0 outPtr rconAddr s →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (52 - rem) →
      (∀ sf : State, sf.pc = fnAddr + 0xcc#64 → sf.status = .Running →
        ExpandInv s0 outPtr rconAddr sf →
        SepWP P target_pc sf
          (expandWords60At (s0.sp - 0x100#64) (foldExpandSteps ws0 52) ∗
           bytesAt roRcon rconAddr aesRconBytes ∗ F) post oom) →
      SepWP P target_pc s
        (expandWords60At (s0.sp - 0x100#64) (foldExpandSteps ws0 (52 - rem)) ∗
         bytesAt roRcon rconAddr aesRconBytes ∗ F) post oom := by
  induction rem with
  | zero => intro s hpc hrun hinv _ hnext; exact hnext s hpc hrun hinv
  | succ r ih =>
    intro s hpc hrun hinv hx8 hnext
    have hk : 52 - (r + 1) < 52 := by omega
    have hne : ¬ (52 - (r + 1) = 52) := by omega
    simp only [hne, ↓reduceIte] at hpc
    refine loopIter_sepWP (k := ⟨52 - (r + 1), hk⟩) hcJoin hcHdr hpc hrun hinv hx8 ?_
    intro s' hpc' hrun' hinv' hx8'
    have hstep : armv8ExpandStep (foldExpandSteps ws0 (52 - (r + 1))) ⟨52 - (r + 1), hk⟩ =
        foldExpandSteps ws0 (52 - r) := by
      have heq : 52 - r = (52 - (r + 1)) + 1 := by omega
      rw [heq]; dsimp only [foldExpandSteps]; simp only [hk, ↓reduceDIte]
    have hidx : (52 - (r + 1)) + 1 = 52 - r := by omega
    rw [hstep]; rw [hidx] at hpc' hx8'
    exact ih (by omega) s' hpc' hrun' hinv' hx8' hnext

set_option maxHeartbeats 400000 in
private theorem epilogue_sepWP {P : Program} {fnAddr outPtr keyPtr rconAddr : BitVec 64}
    {roKey roRcon : Bool} {oldRks : Vector (BitVec 128) 15} {keyBytes : List (BitVec 8)}
    {R : SepProp} {s0 s : State}
    (hcEpi : hasInstrs P (fnAddr + 0xcc#64) (decodeWords expandKeyEpilogueWords))
    (hpc : s.pc = fnAddr + 0xcc#64) (hrun : s.status = .Running)
    (hinv : ExpandInv s0 outPtr rconAddr s) :
    SepWP P (s0.readReg64 Reg.lr) s
      (roundKeys15At (s0.sp - 0x100#64) (armv8ExpandKey keyBytes) ∗ roundKeys15At outPtr oldRks ∗
       bytesAt roKey keyPtr keyBytes ∗ bytesAt roRcon rconAddr aesRconBytes ∗
       (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)))
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf ∧ sf.readReg64 .x0 = outPtr⌝ ∗
            (roundKeys15At outPtr (armv8ExpandKey keyBytes) ∗ bytesAt roKey keyPtr keyBytes ∗
             bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have hsp0_al : (s0.sp &&& 15#64 == 0#64) = true := hinv.sp0_al
  have hsp_al : ((s0.sp - 0x100#64) &&& 15#64 == 0#64) = true := by
    have h := hinv.sp_al; simp only [State.spAligned, hinv.sp_eq] at h; exact h
  have hx0 := hinv.x0_eq; have hsp := hinv.sp_eq
  dsimp only [roundKeys15At]
  have_instrs hcEpi 0 19
  wp_ldp128 hf_0; wp_ldr128 hf_1; wp_str128 hf_2 m1 hm1; wp_stp128 hf_3 m2 hm2
  wp_ldp128 hf_4; wp_stp128 hf_5 m3 hm3; wp_ldp128 hf_6; wp_stp128 hf_7 m4 hm4
  wp_ldp128 hf_8; wp_stp128 hf_9 m5 hm5; wp_ldp128 hf_10; wp_stp128 hf_11 m6 hm6
  wp_ldp128 hf_12; wp_stp128 hf_13 m7 hm7; wp_ldp128 hf_14; wp_stp128 hf_15 m8 hm8
  apply SepWP.step_ldp64 (ea := s0.sp - 0x100#64 + 0xf0#64) (ea2 := s0.sp - 0x100#64 + 0xf8#64)
    (wb := none) (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by wp_focus_close wp_norm_lhs) hf_16
    (by simp [wp_norm, arm64_norm, hsp, beq_iff_eq.mp hsp0_al])
    (by simp [evalAddrMode, wp_norm, arm64_norm, hsp]) (by bv_lin)
    (by wp_focus_close wp_sep_access) (by wp_focus_close wp_sep_access) rfl
  try wp_norm_state
  wp_steps 2
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hinv.pure.trans (PureStepPreserved.of_proj_perm
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1])),
      by simp [wp_norm, arm64_norm, hx0]⟩, ?_⟩
    let spRk := roundKeys15At (s0.sp - 0x100#64) (armv8ExpandKey keyBytes)
    let outRk := roundKeys15At outPtr (armv8ExpandKey keyBytes)
    let saved := ((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)
    change _ ⊨ (spRk ∗ outRk ∗ bytesAt roKey keyPtr keyBytes ∗
      bytesAt roRcon rconAddr aesRconBytes ∗ saved) ∗ R at hm
    have hreord1 : (spRk ∗ outRk ∗ bytesAt roKey keyPtr keyBytes ∗
        bytesAt roRcon rconAddr aesRconBytes ∗ saved) ∗ R =
      (outRk ∗ bytesAt roKey keyPtr keyBytes ∗ bytesAt roRcon rconAddr aesRconBytes ∗
        (spRk ∗ saved)) ∗ R := by sep_ac_rfl
    rw [hreord1] at hm
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (epilogue_stack_entails_stackFrameAt256 s0.sp _ _ _))))) hm
  · have hg := hinv.cs_gprs
    dsimp only [calleeSavedGprs19_28] at hg
    injection hg with h19 hg; injection hg with h20 hg; injection hg with h21 hg
    injection hg with h22 hg; injection hg with h23 hg; injection hg with h24 hg
    injection hg with h25 hg; injection hg with h26 hg; injection hg with h27 h28
    refine ⟨by simp [wp_norm, arm64_norm, h19], by simp [wp_norm, arm64_norm, h20],
      by simp [wp_norm, arm64_norm, h21], by simp [wp_norm, arm64_norm, h22],
      by simp [wp_norm, arm64_norm, h23], by simp [wp_norm, arm64_norm, h24],
      by simp [wp_norm, arm64_norm, h25], by simp [wp_norm, arm64_norm, h26],
      by simp [wp_norm, arm64_norm, h27], by simp [wp_norm, arm64_norm, h28],
      by simp [wp_norm, arm64_norm],
      Eq.trans (by simp [wp_norm, arm64_norm, isCalleeSavedVReg]) hinv.cs_vregs⟩

private theorem expandKey15_sepWP {P : Program} {fnAddr outPtr keyPtr rconAddr : BitVec 64}
    {roKey roRcon relaxRcon : Bool} {oldRks : Vector (BitVec 128) 15} {keyBytes : List (BitVec 8)}
    {R : SepProp} {s0 : State}
    (hc : hasInstrs P fnAddr (expandKey15ReachableInstrs fnAddr rconAddr relaxRcon))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = outPtr) (hx1 : s0.readReg64 .x1 = keyPtr)
    (hklen : keyBytes.length = 32) :
    SepWP P (s0.readReg64 Reg.lr) s0
      (roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
       bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf ∧ sf.readReg64 .x0 = outPtr⌝ ∗
            (roundKeys15At outPtr (armv8ExpandKey keyBytes) ∗ bytesAt roKey keyPtr keyBytes ∗
             bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100)) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  obtain ⟨hc0, hcRcon, hcTail, hcJoin, hcHdr, hcEpi⟩ := hasInstrs_expandKey_parts hc
  have hpre_eq : roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
      bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100 =
    bytesAt roKey keyPtr keyBytes ∗ stackFrameAt s0.sp 0x100 ∗
      (roundKeys15At outPtr oldRks ∗ bytesAt roRcon rconAddr aesRconBytes) := by sep_ac_rfl
  rw [hpre_eq]
  refine prologue_sepWP hc0 hcRcon hcTail hpc hrun hsp hx0 hx1 hklen ?_
  intro s1 hpc1 hrun1 hinv1 hx8_1
  have hmid_eq : expandWords60At (s0.sp - 0x100#64) (armv8InitWords keyBytes) ∗
      bytesAt roKey keyPtr keyBytes ∗
      (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
      (roundKeys15At outPtr oldRks ∗ bytesAt roRcon rconAddr aesRconBytes) =
    expandWords60At (s0.sp - 0x100#64) (foldExpandSteps (armv8InitWords keyBytes) (52 - 52)) ∗
      bytesAt roRcon rconAddr aesRconBytes ∗
      (roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
       (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr))) := by
    dsimp only [Nat.reduceSub, foldExpandSteps]; sep_ac_rfl
  rw [hmid_eq]
  refine loopFrom_sepWP hcJoin hcHdr 52 (Nat.le_refl 52) s1
    (by simpa using hpc1) hrun1 hinv1 (by simpa using hx8_1) ?_
  intro s2 hpc2 hrun2 hinv2
  rw [foldExpandSteps_52_eq, expandWords60At_eq_roundKeys15At]
  change SepWP P (s0.readReg64 Reg.lr) s2
    (roundKeys15At (s0.sp - 0x100#64) (armv8ExpandKey keyBytes) ∗
     bytesAt roRcon rconAddr aesRconBytes ∗
     (roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
      (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)))) _ _
  have hepi_eq : roundKeys15At (s0.sp - 0x100#64) (armv8ExpandKey keyBytes) ∗
      bytesAt roRcon rconAddr aesRconBytes ∗
      (roundKeys15At outPtr oldRks ∗ bytesAt roKey keyPtr keyBytes ∗
       (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr))) =
    roundKeys15At (s0.sp - 0x100#64) (armv8ExpandKey keyBytes) ∗
      roundKeys15At outPtr oldRks ∗
      bytesAt roKey keyPtr keyBytes ∗ bytesAt roRcon rconAddr aesRconBytes ∗
      (((s0.sp - 0x100#64 + 0xf0#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 0x100#64 + 0xf8#64) ↦₆₄ s0.readReg64 Reg.lr)) := by sep_ac_rfl
  rw [hepi_eq]
  exact epilogue_sepWP hcEpi hpc2 hrun2 hinv2

/-- Placement- and relocation-generic `subroutine_ok` verification of the 70-instruction reachable
    prefix of `aes::armv8::expand::expand_key::<32, 15>`. -/
theorem expandKey15_subroutine_ok {P : Program} {fnAddr rconAddr : BitVec 64} {relaxRcon : Bool}
    (hc : hasInstrs P fnAddr (expandKey15ReachableInstrs fnAddr rconAddr relaxRcon)) :
    subroutine_ok P fnAddr (expandKey15Spec rconAddr) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨roKey, roRcon, outPtr, keyPtr, oldRks, keyBytes⟩ R s0 hpc hrun hpre hsp
  dsimp only [expandKey15Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hklen⟩, hpre⟩
  exact ⟨_, hpre, expandKey15_sepWP hc hpc hrun hsp hx0 hx1 hklen⟩

/-- Placement- and relocation-generic `subroutine_ok` verification of the full 73-instruction
    `expand_key::<32, 15>` symbol (including its unreachable cold panic tail). -/
theorem expandKey15_full_subroutine_ok {P : Program} {p : ExpandKey15Syms}
    (hc : hasInstrs P p.fnAddr (expandKey15FullInstrs p)) :
    subroutine_ok P p.fnAddr (expandKey15Spec p.rconAddr) :=
  expandKey15_subroutine_ok (hasInstrs_prefix hc)

/-- Region-destination (`memRegion outPtr 240`) `subroutine_ok` verification of the 70-instruction
    reachable prefix of `expand_key::<32, 15>`. -/
theorem expandKey15_region_subroutine_ok {P : Program} {fnAddr rconAddr : BitVec 64}
    {relaxRcon : Bool}
    (hc : hasInstrs P fnAddr (expandKey15ReachableInstrs fnAddr rconAddr relaxRcon)) :
    subroutine_ok P fnAddr (expandKey15RegionSpec rconAddr) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨roKey, roRcon, outPtr, keyPtr, keyBytes⟩ R s0 hpc hrun hpre hsp
  dsimp only [expandKey15RegionSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hklen⟩, hpre⟩
  refine ⟨memRegion outPtr 240 ∗ bytesAt roKey keyPtr keyBytes ∗
    bytesAt roRcon rconAddr aesRconBytes ∗ stackFrameAt s0.sp 0x100, hpre, ?_⟩
  rw [memRegion240_eq_exists_roundKeys15At]
  exact SepWP.of_sepExists_left fun oldRks => expandKey15_sepWP hc hpc hrun hsp hx0 hx1 hklen

/-- Region-destination (`memRegion outPtr 240`) `subroutine_ok` verification of the full
    73-instruction `expand_key::<32, 15>` symbol. -/
theorem expandKey15_full_region_subroutine_ok {P : Program} {p : ExpandKey15Syms}
    (hc : hasInstrs P p.fnAddr (expandKey15FullInstrs p)) :
    subroutine_ok P p.fnAddr (expandKey15RegionSpec p.rconAddr) :=
  expandKey15_region_subroutine_ok (hasInstrs_prefix hc)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.KeySchedule
