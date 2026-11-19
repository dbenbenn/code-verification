/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Process.FsLemmas
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir
public meta import ProofLib.ProgramReflection

/-!
# `write_file` Prologue, C-Path Copy, `open`, and Error-Path Step Lemmas

Proves the stack layout (`0x1060 = 4192` B frame + `112` B `open` = `4304` B peak), shared return
epilogue (`+0x110 .. +0x12c`), scalar byte-by-byte path copy and interior-NUL scan loop
(`+0x04c .. +0x064`), pre-`open` path validation (`+0x000 .. +0x080`), and `open` +
`__errno_location` error branch (`+0x080 .. +0x09c`) for `signalSessionIoMultiLib` block `1`
(`libsignal_cli_io::write_file`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.Musl (
  ValidRelCPath memcpySrc
  muslErrnoLocationSpec muslOpenCreateTruncSpec
)
open VerifiedLibraries.RustStd (
  SameCpuState StdErrnoCell stdErrnoAddr
  cPathOf rustSepWP_cut rustNz_byte_ze_beq_false
  cells cells_zero cells_succ stackAt_split_cells
)
open VerifiedLibraries.RustStd.Io (SameCpuOracleState)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure cliIoBlocks_len
  cliIoOpenSym cliIoWriteSym cliIoCloseSym cliIoErrnoLocationSym
  cliIoBlockNoSvc0_01
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  bv64_beq_ofNat_false bv64_sub_ofNat bv64_ult_ofNat_true bv64_ult_ofNat_false
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileDir (muslErrnoAddr_eq_stdErrnoAddr)

-- Local `@[expose]` block-1 (`signal_session_io::write_file`, `304` B / `76` insns) placement & fetches
@[expose] def cliIoLib01 : PlacedLib := signalSessionIoMultiLib.blockLib 1
@[expose] def cliIoPl01 [CliIoPlacement] : Placement :=
  signalSessionIoMultiLib.blockPlacement CliIoPlacement.mpl 1
theorem cliIoPlaceable01 [CliIoPlacement] : cliIoLib01.Placeable cliIoPl01 :=
  signalSessionIoMultiLib.placeable_blockLib (by rw [cliIoBlocks_len]; decide) CliIoPlacement.placeable
@[expose] def cliIoPC01 [CliIoPlacement] : Program := cliIoLib01.program cliIoPl01

def cliIoProg01 : Program := { code := cliIoLib01.text.code, symbols := cliIoLib01.text.symbols }
def cliIoTree01 : WordTree := word_tree_of% cliIoProg01
theorem cliIo01_code_eq : cliIoLib01.text.code = cliIoTree01.toBytes := by rfl_kernel
theorem cliIo01_tree_size : cliIoTree01.checkSize? = some 76 := by rfl_kernel
def cliIoSymChars01 : List (List Char × Nat) := sym_chars_of% cliIoProg01
theorem cliIo01_symbols_eq : cliIoLib01.text.symbols = toStringSymbols cliIoSymChars01 := by rfl_kernel
theorem cliIo01_symbols_fresh : allFreshCharSymbols cliIoSymChars01 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches cliIoPC01 cliIoLib01 cliIoTree01 cliIo01_code_eq cliIo01_tree_size
  via_placement cliIoPl01 cliIoPlaceable01 [0x0 → 0x12c]
gen_placed_fnOffs cliIoPC01 cliIoLib01 cliIoSymChars01 cliIo01_symbols_eq cliIo01_symbols_fresh
end

/-! ## 1. Pure `cPathOf` ↔ `cstrBytes`, Block Indices, and `SyscallPreserved` Helpers -/

private theorem char_ofNat_byte_toNat (b : BitVec 8) :
    (Char.ofNat b.toNat).toNat = b.toNat := by
  have hlt : b.toNat < 256 := b.isLt
  have hval : Nat.isValidChar b.toNat := Or.inl (by omega)
  simp [Char.ofNat, Char.ofNatAux, hval]

theorem toList_cPathOf (bs : List (BitVec 8)) :
    (cPathOf bs).toList = bs.map (fun b => Char.ofNat b.toNat) := by
  simp [cPathOf]

theorem toList_cPathOf_length (bs : List (BitVec 8)) :
    (cPathOf bs).toList.length = bs.length := by
  rw [toList_cPathOf, List.length_map]

theorem mem_toList_cPathOf_lt_256 {bs : List (BitVec 8)} {c : Char}
    (hc : c ∈ (cPathOf bs).toList) : c.toNat < 256 := by
  rw [toList_cPathOf, List.mem_map] at hc
  rcases hc with ⟨b, _, rfl⟩
  rw [char_ofNat_byte_toNat]
  exact b.isLt

theorem cstrBytes_cPathOf (bs : List (BitVec 8)) :
    cstrBytes (cPathOf bs) = bs ++ [0#8] := by
  unfold cstrBytes
  rw [toList_cPathOf, List.map_map]
  congr 1
  have hid : ((fun c : Char => BitVec.ofNat 8 c.toNat) ∘ fun b : BitVec 8 => Char.ofNat b.toNat) = id := by
    funext b
    simp [Function.comp, char_ofNat_byte_toNat]
  rw [hid, List.map_id]

theorem cstrBytes_cPathOf_length (bs : List (BitVec 8)) :
    (cstrBytes (cPathOf bs)).length = bs.length + 1 := by
  rw [cstrBytes_cPathOf, List.length_append, List.length_singleton]

theorem cliIo1_lt : 1 < signalSessionIoMultiLib.blocks.length := by
  rw [cliIoBlocks_len]; decide

theorem cliIoWriteFile_open_pc [CliIoPlacement] :
    cliIoPl01.base + 128#64 + (cliIoPl01.ρ cliIoOpenSym - cliIoPl01.base - 128#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoOpenSym := by
  change cliIoPl01.base + 128#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl01.base - 128#64) = _
  bv_lin

theorem cliIoWriteFile_errno_pc [CliIoPlacement] :
    cliIoPl01.base + 136#64 + (cliIoPl01.ρ cliIoErrnoLocationSym - cliIoPl01.base - 136#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoErrnoLocationSym := by
  change cliIoPl01.base + 136#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl01.base - 136#64) = _
  bv_lin

theorem cliIoWriteFile_write_pc [CliIoPlacement] :
    cliIoPl01.base + 208#64 + (cliIoPl01.ρ cliIoWriteSym - cliIoPl01.base - 208#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoWriteSym := by
  change cliIoPl01.base + 208#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl01.base - 208#64) = _
  bv_lin

theorem cliIoWriteFile_close_pc [CliIoPlacement] :
    cliIoPl01.base + 264#64 + (cliIoPl01.ρ cliIoCloseSym - cliIoPl01.base - 264#64) =
      signalSessionIoMultiLib.resolve CliIoPlacement.mpl cliIoCloseSym := by
  change cliIoPl01.base + 264#64 + (signalSessionIoMultiLib.resolve _ _ - cliIoPl01.base - 264#64) = _
  bv_lin

theorem syscallPreserved_refl (s : State) : SyscallPreserved s s :=
  ⟨rfl, rfl, ⟨rfl, rfl, rfl, fun _ => rfl⟩⟩

theorem syscallPreserved_trans {s0 s1 s2 : State}
    (h01 : SyscallPreserved s0 s1) (h12 : SyscallPreserved s1 s2) :
    SyscallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h01.2.2.trans h12.2.2⟩

theorem syscallPreserved_of_seg {s s' sm' sm : State}
    (h_in : SameCpuOracleState s' s) (h_out : SameCpuOracleState sm sm')
    (hnsp : ProofLib.NonSyscallPreserved s sm)
    (htp : sm'.tpidrEl0 = s'.tpidrEl0)
    (hsig : sm'.sigActions = s'.sigActions) :
     (sm.fs = s.fs ∧ sm.trace = s.trace) ∧ SyscallPreserved s sm := by
  have htp_sm : sm.tpidrEl0 = s.tpidrEl0 :=
    h_out.1.tpidrEl0_eq.trans (htp.trans h_in.1.tpidrEl0_eq)
  have hsig_sm : sm.sigActions = s.sigActions :=
    h_out.1.sigActions_eq.trans (hsig.trans h_in.1.sigActions_eq)
  exact ⟨⟨hnsp.2.2.2.2.2.2, hnsp.1⟩, htp_sm, hsig_sm,
    ProofLib.nonSyscallPreserved_toVmFields hnsp⟩

theorem syscallPreserved_of_stdState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    SyscallPreserved s0 sf :=
  ⟨h.2.2.1, h.2.2.2.1,
   ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩⟩

theorem seqCodeLoaded [CliIoPlacement] {P : Program} {mid target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl s.mem)
    (h : SepWP P mid s Pre
      (fun sm Pm => (signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem →
        SepWP P target_pc sm Pm post oom)) oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps1, hout1⟩ := SepWP.to_reaches_pc h hm hL
  rcases hout1 with ⟨_, _, Pm, hmm, hcont⟩ | hoom
  · have hcl_m : signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem :=
      fun k hk => hsteps1.codeLoaded (hcl k hk)
    obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc (hcont hcl_m) hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hoom⟩

/-! ## 2. Stack Frame Layout (`0x1060 = 4192` B) and `4096`-B Buffer Helpers -/

section
arm64_proof_prelude

/-- 10 callee-saved register slots (`[s0.sp - 80, s0.sp)`) saved by `write_file` (`block[1]`).
    Registers `x26` and `x27` are untouched by `write_file` and remain in GPRs. -/
@[expose] def cliIoSavedRegs10 (s0 : State) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

/-- Expose the 8-byte stack-probe word at `base + 4` (`s0.sp - 4176`) inside the `4096`-byte
    C-path buffer at `base = s0.sp - 4180` (`sp + 0xc`). -/
theorem memRegion4096_split_probe4 (base : BitVec 64) :
    memRegion base 4096 =
      memRegion base 4 ∗
        (∃∗ w : BitVec 64, (base + 4#64) ↦₆₄ w) ∗
        memRegion (base + 12#64) 4084 := by
  rw [memRegion_split_le base 4 4096 (by decide) (by decide),
    memRegion_split_le (base + 4#64) 8 4092 (by decide) (by decide),
    show (8 : Nat) = 8 * 1 by decide,
    memRegion_cells (base + 4#64) 1 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, bv_lin_norm]

/-- Refold the 8-byte stack-probe word at `base + 4` back into `memRegion base 4096`. -/
theorem memRegion4096_refold_probe4 (base : BitVec 64) (w : BitVec 64) :
    memRegion base 4 ∗ ((base + 4#64) ↦₆₄ w) ∗ memRegion (base + 12#64) 4084 ⊢
      memRegion base 4096 := by
  rw [memRegion4096_split_probe4 base]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w (Entails.refl _)))

/-- Refold a NUL-terminated path of `< 4096` bytes back into `memRegion base 4096`. -/
theorem refold_cstr_buf4096 (base : BitVec 64) (pathBytes : List (BitVec 8))
    (hlt : pathBytes.length < 4096) :
    (base ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
      memRegion (base + BitVec.ofNat 64 (pathBytes.length + 1)) (4095 - pathBytes.length) ⊢
      memRegion base 4096 := by
  have hlen := cstrBytes_cPathOf_length pathBytes
  have hsub : 4096 - (cstrBytes (cPathOf pathBytes)).length = 4095 - pathBytes.length := by
    rw [hlen]; omega
  rw [← hlen, ← hsub]
  exact pointsToBytes_memRegion_entails base (cstrBytes (cPathOf pathBytes)) 4096
    (by rw [hlen]; omega) (by decide)

/-- Split `stackAt sp stackBytes` (`4192 ≤ stackBytes ≤ 2^64`) for `write_file` (`block[1]`):
    - `stackAt (sp - 4192) (stackBytes - 4192)` below the frame `sp`,
    - `memRegion (sp - 4192) 12` (`[sp_frame, sp_frame + 0xc)`),
    - `memRegion (sp - 4180) 4096` (`4096`-B C-string path buffer at `sp_frame + 0xc`),
    - `memRegion (sp - 84) 4` (`4`-B `black_box` scratch slot at `x29 - 0x4`), and
    - `10` saved-register cells at `[sp - 80, sp)`. -/
theorem cliIoWriteFile_stack_split (sp : BitVec 64) {stackBytes : Nat}
    (hlo : 4192 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) :
    stackAt sp stackBytes =
      ∃∗ r0, ∃∗ r1, ∃∗ r2, ∃∗ r3, ∃∗ r4,
      ∃∗ r5, ∃∗ r6, ∃∗ r7, ∃∗ r8, ∃∗ r9,
        stackAt (sp - 4192#64) (stackBytes - 4192) ∗
        memRegion (sp - 4192#64) 12 ∗
        memRegion (sp - 4180#64) 4096 ∗
        memRegion (sp - 84#64) 4 ∗
        (((sp - 80#64) ↦₆₄ r0) ∗ ((sp - 72#64) ↦₆₄ r1) ∗
          ((sp - 64#64) ↦₆₄ r2) ∗ ((sp - 56#64) ↦₆₄ r3) ∗
          ((sp - 48#64) ↦₆₄ r4) ∗ ((sp - 40#64) ↦₆₄ r5) ∗
          ((sp - 32#64) ↦₆₄ r6) ∗ ((sp - 24#64) ↦₆₄ r7) ∗
          ((sp - 16#64) ↦₆₄ r8) ∗ ((sp - 8#64) ↦₆₄ r9)) := by
  have heq_sb : stackBytes = (stackBytes - 80) + 8 * 10 := by omega
  conv => lhs; rw [heq_sb]
  rw [stackAt_split_cells sp (stackBytes - 80) 10 (by omega)]
  have hbot : stackAt (sp - BitVec.ofNat 64 (8 * 10)) (stackBytes - 80) =
      stackAt (sp - 4192#64) (stackBytes - 4192) ∗
        memRegion (sp - 4192#64) 12 ∗
        memRegion (sp - 4180#64) 4096 ∗
        memRegion (sp - 84#64) 4 := by
    have h80 : sp - BitVec.ofNat 64 (8 * 10) = sp - 80#64 := rfl
    rw [h80]
    unfold ProofLib.stackAt
    have h4192 : sp - 80#64 - BitVec.ofNat 64 (stackBytes - 80) =
        sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192) := by
      have hsplit : stackBytes - 80 = (stackBytes - 4192) + 4112 := by omega
      rw [hsplit, BitVec.ofNat_add]
      bv_lin
    rw [h4192,
      memRegion_split_le (sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192))
        (stackBytes - 4192) (stackBytes - 80) (by omega) (by omega)]
    have h4112_sz : stackBytes - 80 - (stackBytes - 4192) = 4112 := by omega
    have h4192_addr : sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192) +
        BitVec.ofNat 64 (stackBytes - 4192) = sp - 4192#64 := by bv_lin
    rw [h4112_sz, h4192_addr,
      memRegion_split_le (sp - 4192#64) 12 4112 (by decide) (by decide)]
    have h4180_addr : sp - 4192#64 + BitVec.ofNat 64 12 = sp - 4180#64 := by bv_lin
    rw [h4180_addr,
      memRegion_split_le (sp - 4180#64) 4096 4100 (by decide) (by decide)]
    have h84_addr : sp - 4180#64 + BitVec.ofNat 64 4096 = sp - 84#64 := by bv_lin
    rw [h84_addr]
  rw [hbot]
  dsimp only [cells]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right,
    bv_lin_norm, sepConj_assoc]

/-- Refold `write_file`'s `4192`-byte frame back into `stackAt s0.sp stackBytes`. -/
theorem cliIoWriteFile_stack_refold (s0 : State) {stackBytes : Nat}
    (hlo : 4192 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64) :
    stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
      memRegion (s0.sp - 4192#64) 12 ∗
      memRegion (s0.sp - 4180#64) 4096 ∗
      memRegion (s0.sp - 84#64) 4 ∗
      cliIoSavedRegs10 s0 ⊢
      stackAt s0.sp stackBytes := by
  rw [cliIoWriteFile_stack_split s0.sp hlo hhi]
  dsimp only [cliIoSavedRegs10]
  exact Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) <|
    by sep_entail

/-! ## 3. Shared Return Epilogue (`+0x110 = 272#64 .. +0x12c = 300#64`) -/

/-- Shared stack-restore + `ret` epilogue of `write_file` (`+0x110 .. +0x12c`). -/
theorem cliIoWriteFile_ret_epilogue [CliIoPlacement]
    {P : Program} (hext1 : CliIoBlockNoExtern cliIoMpl P 1)
    {s0 se : State} {R_out : SepProp} {stackBytes : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4192 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl se.mem)
    (hpc : se.pc = cliIoPl01.base + 272#64) (hrun : se.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 4192#64)
    (hx26 : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27 : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
      sf.readReg64 .x0 = se.readReg64 .x0 →
      sf.fs = se.fs → sf.trace = se.trace →
      SyscallPreserved se sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ stackAt s0.sp stackBytes ∗ R_out) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
        memRegion (s0.sp - 4192#64) 12 ∗
        memRegion (s0.sp - 4180#64) 4096 ∗
        memRegion (s0.sp - 84#64) 4 ∗
        cliIoSavedRegs10 s0 ∗
        R_out)
      post oomProp := by
  apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e0
  have hcpu_e := hcpu_e0.1
  change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = cliIoPl01.base + 272#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 4192#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 4192#64 hsp0
  wp_conv_pre => dsimp only [cliIoSavedRegs10]
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
    fun sf hcpu_f0 hcl_f hnsp_f _hsym_f => ?_
  have hcpu_f := hcpu_f0.1
  have ⟨⟨hfs_ef, htr_ef⟩, hsys_ef⟩ :=
    syscallPreserved_of_seg hcpu_e0 hcpu_f0 hnsp_f
      (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
  have hx0_f : sf.readReg64 .x0 = se.readReg64 .x0 := by
    rw [hcpu_f.readReg64 .x0]; simp only [arm64_norm]
    exact hcpu_e.readReg64 .x0
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp only [arm64_norm]; exact (hcpu_e.readReg64 _).trans hx26
    · rw [hcpu_f.readReg64]; simp only [arm64_norm]; exact (hcpu_e.readReg64 _).trans hx27
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · rw [hcpu_f.readReg64]; simp [arm64_norm]
    · exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))
  refine SepWP.done hpc_f hrun_f
    (hcont sf hpc_f hrun_f hsp_f hcs_f hcl_f hx0_f hfs_ef htr_ef hsys_ef ?_)
  have hstk_back := cliIoWriteFile_stack_refold s0 hlo hhi
  dsimp only [cliIoSavedRegs10] at hstk_back
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := R_out) hstk_back) (by sep_entail))
  sep_entail

/-! ## 4. Scalar Byte Copy / Interior-NUL Scan Loop (`+0x04c = 76#64 .. +0x064 = 100#64`) -/

private abbrev memcpySrc8 (ro : Bool) (a : BitVec 64) (b : BitVec 8) : SepProp :=
  bif ro then a ↦₈ᵣ b else a ↦₈ b

private theorem memcpySrc_cons (ro : Bool) (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    memcpySrc ro a (b :: bs) = (memcpySrc8 ro a b ∗ memcpySrc ro (a + 1#64) bs) := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private theorem memcpySrc_singleton (ro : Bool) (a : BitVec 64) (b : BitVec 8) :
    memcpySrc ro a [b] = memcpySrc8 ro a b := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private structure WriteScanPreserved (s0 s1 : State) : Prop where
  run_eq : s1.status = .Running
  sp_eq : s1.sp = s0.sp
  spAligned_eq : s1.spAligned = true
  fs_eq : s1.fs = s0.fs
  trace_eq : s1.trace = s0.trace
  sig_eq : s1.sigActions = s0.sigActions
  tp_eq : s1.tpidrEl0 = s0.tpidrEl0
  bs_eq : s1.brkStart = s0.brkStart
  oracle_eq : s1.oracle = s0.oracle
  symtab_eq : s1.symtab = s0.symtab
  lr_eq : s1.readReg64 .lr = s0.readReg64 .lr
  x1_eq : s1.readReg64 .x1 = s0.readReg64 .x1
  x8_eq : s1.readReg64 .x8 = s0.readReg64 .x8
  x19_eq : s1.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5)
  x20_eq : s1.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5)
  x26_eq : s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27_eq : s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  x29_eq : s1.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
  vregs_eq : calleeSavedVRegs s1 = calleeSavedVRegs s0

private theorem WriteScanPreserved.trans_right {s0 s1 s2 : State}
    (h12 : WriteScanPreserved s1 s2) (h01 : WriteScanPreserved s0 s1) :
    WriteScanPreserved s0 s2 :=
  ⟨h12.run_eq, h12.sp_eq.trans h01.sp_eq, h12.spAligned_eq,
   h12.fs_eq.trans h01.fs_eq, h12.trace_eq.trans h01.trace_eq,
   h12.sig_eq.trans h01.sig_eq, h12.tp_eq.trans h01.tp_eq,
   h12.bs_eq.trans h01.bs_eq, h12.oracle_eq.trans h01.oracle_eq,
   h12.symtab_eq.trans h01.symtab_eq, h12.lr_eq.trans h01.lr_eq,
   h12.x1_eq.trans h01.x1_eq, h12.x8_eq.trans h01.x8_eq,
   h12.x19_eq.trans h01.x19_eq, h12.x20_eq.trans h01.x20_eq,
   h12.x26_eq.trans h01.x26_eq, h12.x27_eq.trans h01.x27_eq,
   h12.x29_eq.trans h01.x29_eq, h12.vregs_eq.trans h01.vregs_eq⟩

private theorem cliIoWriteFile_nul_scan_loop [CliIoPlacement] {ro : Bool} {tgt : BitVec 64}
    {post : State → SepProp → Prop}
    (rem : List (BitVec 8)) {idx n : Nat} {pathPtr dst scratchPtr : BitVec 64}
    {F : SepProp} {s : State} {sc0 : BitVec 8}
    (h1 : 1 ≤ rem.length) (hsum : idx + rem.length = n) (hn : n < 4096)
    (hpc : s.pc = cliIoPl01.base + 76#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = pathPtr + BitVec.ofNat 64 idx)
    (hx8 : s.readReg64 .x8 = scratchPtr)
    (hx9 : s.readReg64 (.gpr 9#5) = dst + BitVec.ofNat 64 idx)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 rem.length)
    (hfound : ∀ sf : State, ∀ sc1 : BitVec 8, sf.pc = cliIoPl01.base + 152#64 →
      WriteScanPreserved s sf → 0#8 ∈ rem →
      SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) tgt sf
        (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
          memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) ∗
          (scratchPtr ↦₈ sc1) ∗ F) post)
    (hnone : ∀ sf : State, ∀ sc1 : BitVec 8, sf.pc = cliIoPl01.base + 104#64 →
      WriteScanPreserved s sf → (∀ b ∈ rem, b ≠ 0#8) →
      SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) tgt sf
        (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
          ((dst + BitVec.ofNat 64 idx) ↦ₛ rem) ∗
          memRegion (dst + BitVec.ofNat 64 n) (4096 - n) ∗
          (scratchPtr ↦₈ sc1) ∗ F) post) :
    SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) tgt s
      (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
        memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) ∗
        (scratchPtr ↦₈ sc0) ∗ F) post := by
  induction rem generalizing idx F s sc0 with
  | nil => simp at h1
  | cons b rem' ih =>
    by_cases hb0 : b = 0#8
    · subst hb0
      wp_conv_pre => rw [memcpySrc_cons]; simp only [sepConj_assoc]
      apply rustSepWP_cut (mid := cliIoPl01.base + 152#64)
      cases ro <;>
      · dsimp only [memcpySrc, memcpySrc8, cond] at hfound ⊢
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
        refine SepWP.weaken_pre ?_
          (hfound _ 0#8 (by simp [arm64_norm])
            ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
             by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩
            (List.mem_cons_self ..))
        simp only [pointsToBytes_cons, pointsToBytesRO_cons, bv_lin_norm]
        sep_entail
    · obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false hb0
      wp_conv_pre =>
        rw [show 4096 - idx = (4095 - idx) + 1 by simp at hsum; omega,
          memRegion_succ_off dst idx (4095 - idx) (by simp at hsum; omega)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro z_dst
      rcases rem' with _ | ⟨b2, rest⟩
      · have hlen1 : ([b] : List (BitVec 8)).length = 1 := rfl
        rw [hlen1] at hx11
        wp_conv_pre => rw [memcpySrc_singleton]
        apply rustSepWP_cut (mid := cliIoPl01.base + 104#64)
        cases ro <;>
        · dsimp only [memcpySrc, memcpySrc8, cond] at hnone ⊢
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          refine SepWP.weaken_pre ?_
            (hnone _ b (by simp [arm64_norm])
              ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
               by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
               by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩
              (by intro x hx; simp at hx; subst hx; exact hb0))
          rw [show n = idx + 1 by simp at hsum; omega,
            show 4096 - (idx + 1) = 4095 - idx by omega]
          simp only [pointsToBytes_singleton, pointsToBytesRO_singleton, bv_lin_norm]
          sep_entail
      · have hlen_cons_lt : (b :: b2 :: rest).length < 4096 := by
          simp only [List.length_cons] at hsum ⊢; omega
        have hsub1 : BitVec.ofNat 64 (b :: b2 :: rest).length - 1#64 =
            BitVec.ofNat 64 (b2 :: rest).length :=
          bv64_sub_ofNat (b := 1) (by simp)
        have hne1 : (BitVec.ofNat 64 (b :: b2 :: rest).length != 1#64) = true := by
          rw [bne_iff_ne]
          intro heq
          have hto := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, List.length_cons] at hto hlen_cons_lt
          omega
        have hp_add1 : pathPtr + BitVec.ofNat 64 idx + 1#64 =
            pathPtr + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
        have hd_add1 : dst + BitVec.ofNat 64 idx + 1#64 =
            dst + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
        let DstHead : SepProp := (dst + BitVec.ofNat 64 idx) ↦₈ b
        wp_conv_pre => rw [memcpySrc_cons]; simp only [sepConj_assoc]
        apply rustSepWP_cut (mid := cliIoPl01.base + 76#64)
        cases ro
        · dsimp only [memcpySrc8, cond]
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ b
          refine SepWP.weaken_pre
            (P' := memcpySrc false (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
              memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
              (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
            (by dsimp only [SrcHead, DstHead]
                rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
                sep_entail)
            (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
              (by simp) (by simp only [List.length_cons] at hsum ⊢; omega)
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun)
              (by simpa [arm64_norm] using hsp)
              (by rw [← hp_add1]; simp only [arm64_norm])
              (by simpa [arm64_norm] using hx8)
              (by rw [← hd_add1]; simp only [arm64_norm])
              (by simp only [arm64_norm])
              (fun sf sc1 hpc_f hpres2 hmem_rest =>
                SepWP.weaken_pre ?_
                  (hfound sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (List.mem_cons_of_mem b hmem_rest)))
              (fun sf sc1 hpc_f hpres2 hno_rest =>
                SepWP.weaken_pre ?_
                  (hnone sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hxr
                        · exact hb0
                        · exact hno_rest x hxr))))
          · have hmerge_dst :
                DstHead ∗ memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ⊢
                  memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) := by
              dsimp only [DstHead]
              rw [← hd_add1,
                show 4096 - (idx + 1) = 4095 - idx by omega,
                show 4096 - idx = (4095 - idx) + 1 by simp only [List.length_cons] at hsum; omega]
              exact memRegion_byte_merge (dst + BitVec.ofNat 64 idx) b (4095 - idx)
                (by simp only [List.length_cons] at hsum; omega)
            rw [memcpySrc_cons (b := b) (bs := b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond]
            let KeepFound : SepProp :=
              SrcHead ∗ memcpySrc false (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
                (scratchPtr ↦₈ sc1) ∗ F
            refine Entails.trans ?_
              (Entails.trans (sepConj_mono_left (Q := KeepFound) hmerge_dst)
                (by dsimp only [KeepFound, SrcHead]; sep_entail))
            dsimp only [KeepFound, SrcHead]; sep_entail
          · rw [memcpySrc_cons (b := b) (bs := b2 :: rest),
              pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail
        · dsimp only [memcpySrc8, cond]
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ᵣ b
          refine SepWP.weaken_pre
            (P' := memcpySrc true (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
              memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
              (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
            (by dsimp only [SrcHead, DstHead]
                rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
                sep_entail)
            (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
              (by simp) (by simp only [List.length_cons] at hsum ⊢; omega)
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun)
              (by simpa [arm64_norm] using hsp)
              (by rw [← hp_add1]; simp only [arm64_norm])
              (by simpa [arm64_norm] using hx8)
              (by rw [← hd_add1]; simp only [arm64_norm])
              (by simp only [arm64_norm])
              (fun sf sc1 hpc_f hpres2 hmem_rest =>
                SepWP.weaken_pre ?_
                  (hfound sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (List.mem_cons_of_mem b hmem_rest)))
              (fun sf sc1 hpc_f hpres2 hno_rest =>
                SepWP.weaken_pre ?_
                  (hnone sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hxr
                        · exact hb0
                        · exact hno_rest x hxr))))
          · have hmerge_dst :
                DstHead ∗ memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ⊢
                  memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) := by
              dsimp only [DstHead]
              rw [← hd_add1,
                show 4096 - (idx + 1) = 4095 - idx by omega,
                show 4096 - idx = (4095 - idx) + 1 by simp only [List.length_cons] at hsum; omega]
              exact memRegion_byte_merge (dst + BitVec.ofNat 64 idx) b (4095 - idx)
                (by simp only [List.length_cons] at hsum; omega)
            rw [memcpySrc_cons (b := b) (bs := b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond]
            let KeepFound : SepProp :=
              SrcHead ∗ memcpySrc true (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
                (scratchPtr ↦₈ sc1) ∗ F
            refine Entails.trans ?_
              (Entails.trans (sepConj_mono_left (Q := KeepFound) hmerge_dst)
                (by dsimp only [KeepFound, SrcHead]; sep_entail))
            dsimp only [KeepFound, SrcHead]; sep_entail
          · rw [memcpySrc_cons (b := b) (bs := b2 :: rest),
              pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail

/-! ## 5. Pre-`open` Segment (`+0x000 .. +0x080`) -/

/-- Pre-`open` segment of `libsignal_cli_io::write_file` (`+0x000 .. +0x080`):
    - When `4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes`, returns `x0 = 1#64` directly with
      `sf.fs = s0.fs`, `sf.trace = s0.trace`, and `SyscallPreserved s0 sf`.
    - When `pathBytes.length < 4096 ∧ 0#8 ∉ pathBytes`, reaches `bl open` (`+0x080`) with
      `(s0.sp - 4180#64) ↦ₛ cstrBytes (cPathOf pathBytes)`, `w1 = 0x80241#32`, `w2 = 0x1b6#32`,
      `x19 = bsLen`, and `x20 = buf`. -/
theorem cliIoWriteFile_pre_open [CliIoPlacement]
    {P : Program} (hext1 : CliIoBlockNoExtern cliIoMpl P 1)
    {ro : Bool} {s0 : State} {pathPtr buf : BitVec 64} {pathBytes : List (BitVec 8)}
    {bsLen stackBytes : Nat} {R_rest : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4192 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl0 : signalSessionIoMultiLib.CodeLoaded cliIoMpl s0.mem)
    (hpc0 : s0.pc = cliIoPl01.base) (hrun0 : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = pathPtr)
    (hx1 : (s0.readReg64 .x1).toNat = pathBytes.length)
    (hx2 : s0.readReg64 .x2 = buf)
    (hx3 : (s0.readReg64 .x3).toNat = bsLen)
    (herr_ret : (4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes) →
      ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
        sf.readReg64 .x0 = 1#64 →
        sf.fs = s0.fs → sf.trace = s0.trace →
        SyscallPreserved s0 sf →
        ∀ {Pre_f : SepProp},
          (Pre_f ⊢ stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗ R_rest) →
          post sf Pre_f)
    (hat_open : pathBytes.length < 4096 → 0#8 ∉ pathBytes →
      ∀ sm : State,
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem →
        sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym →
        sm.status = .Running →
        sm.sp = s0.sp - 4192#64 →
        sm.spAligned = true →
        sm.readReg64 .lr = cliIoPl01.base + 132#64 →
        sm.readReg64 .x0 = s0.sp - 4180#64 →
        sm.readReg32 .x1 = 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32 →
        sm.readReg32 .x2 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK →
        sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bsLen →
        sm.readReg64 (.gpr 20#5) = buf →
        sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) →
        sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        sm.fs = s0.fs → sm.trace = s0.trace →
        SyscallPreserved s0 sm →
        SepWP P (s0.readReg64 .lr) sm
          (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            ((s0.sp - 4180#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
            memRegion ((s0.sp - 4180#64) + BitVec.ofNat 64 (pathBytes.length + 1))
              (4095 - pathBytes.length) ∗
            memRegion (s0.sp - 84#64) 4 ∗
            cliIoSavedRegs10 s0 ∗
            memcpySrc ro pathPtr pathBytes ∗
            R_rest)
          post oomProp) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗ R_rest)
      post oomProp := by
  have hpath_lt64 : pathBytes.length < 2 ^ 64 := hx1 ▸ (s0.readReg64 .x1).isLt
  have hx1_bv : s0.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := by
    rw [← hx1]; simp
  have hbs_lt64 : bsLen < 2 ^ 64 := hx3 ▸ (s0.readReg64 .x3).isLt
  have hx3_bv : s0.readReg64 .x3 = BitVec.ofNat 64 bsLen := by
    rw [← hx3]; simp
  by_cases hlen : 4096 ≤ pathBytes.length
  · -- Fast error exit `+0x000 .. +0x00c`: `4096 ≤ pathBytes.length` (no stack touched).
    have hule_f : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have h4095_ult : (4095#64 : BitVec 64).ult (BitVec.ofNat 64 pathBytes.length) = true :=
      bv64_ult_ofNat_true (a := 4095) (by omega) hpath_lt64
    apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl0
      (mid := s0.readReg64 .lr)
    intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
    change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = cliIoPl01.base := hcpu1.pc_eq.trans hpc0
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
      (hcpu1.readReg64 .x1).trans hx1_bv
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm, hcpu1.readReg64 .lr])
      (by simpa [arm64_norm] using hrun1')
      fun sf hcpu_f0 hcl_f hnsp_f _ => ?_
    have hcpu_f := hcpu_f0.1
    have ⟨⟨hfs_f, htr_f⟩, hsys_f⟩ :=
      syscallPreserved_of_seg hcpu1_0 hcpu_f0 hnsp_f
        (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc_f : sf.pc = s0.readReg64 .lr :=
      hcpu_f.pc_eq.trans ((by simp [arm64_norm] : _ = s1'.readReg64 .lr).trans (hcpu1.readReg64 .lr))
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun1'
    have hsp_f : sf.sp = s0.sp :=
      hcpu_f.sp_eq.trans ((by simp [arm64_norm] : _ = s1'.sp).trans hcpu1.sp_eq)
    have hx0_f : sf.readReg64 .x0 = 1#64 :=
      (hcpu_f.readReg64 .x0).trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (rw [hcpu_f.readReg64]; simp only [arm64_norm]; exact hcpu1.readReg64 _)
      exact hcpu_f.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
    exact SepWP.done hpc_f hrun_f
      (herr_ret (Or.inl hlen) sf hpc_f hrun_f hsp_f hcs_f hcl_f hx0_f hfs_f htr_f hsys_f
        (Entails.refl _))
  · -- `pathBytes.length < 4096`: run prologue `+0x000 .. +0x038`.
    have hlt : pathBytes.length < 4096 := Nat.lt_of_not_ge hlen
    have hule_t : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hult_f : BitVec.ult 4095#64 (BitVec.ofNat 64 pathBytes.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    wp_conv_pre =>
      rw [cliIoWriteFile_stack_split s0.sp hlo hhi, memRegion4096_split_probe4 (s0.sp - 4180#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
    repeat (apply SepWP.exists_left; intro)
    by_cases hnul : (0#8 : BitVec 8) ∈ pathBytes
    · -- Interior NUL in `pathBytes` (`1 ≤ pathBytes.length`, branches to `+0x098`, then `+0x110`).
      have h1_pos : 1 ≤ pathBytes.length := by
        cases pathBytes with
        | nil => simp at hnul
        | cons _ _ => simp
      have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
        bv64_beq_ofNat_false (b := 0) (by omega) hpath_lt64 (by decide)
      apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl0
        (mid := cliIoPl01.base + 272#64)
      intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl01.base := hcpu1.pc_eq.trans hpc0
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
        (hcpu1.readReg64 .x1).trans hx1_bv
      apply rustSepWP_cut (mid := cliIoPl01.base + 76#64)
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
      have hrefold4180 := memRegion4096_refold_probe4 (s0.sp - 4180#64) 0#64
      have hcarve84 :
          memRegion (s0.sp - 84#64) 4 =
            ((∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗ memRegion (s0.sp - 83#64) 3) := by
        simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 84#64) 0 3 (by decide)
      let F_err : SepProp :=
        memRegion (s0.sp - 83#64) 3 ∗
          stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
          memRegion (s0.sp - 4192#64) 12 ∗
          cliIoSavedRegs10 s0 ∗ R_rest
      refine SepWP.weaken_pre
        (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
          memRegion ((s0.sp - 4180#64) + 0#64) 4096 ∗
          (∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗ F_err) ?_ ?_
      · rw [hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
          hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 25#5),
          hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
          hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
          hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5),
          show s0.sp - (84 : BitVec 64) = s0.sp - 84#64 from rfl, hcarve84]
        dsimp only [F_err, cliIoSavedRegs10]; simp only [bv_lin_norm]
        let KeepErr0 : SepProp :=
          memcpySrc ro pathPtr pathBytes ∗
            stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            (∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗
            memRegion (s0.sp - 83#64) 3 ∗
            cliIoSavedRegs10 s0 ∗ R_rest
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := KeepErr0) hrefold4180)
            (by dsimp only [KeepErr0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail))
        dsimp only [KeepErr0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail
      · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_left; intro sc0
        wp_conv_pre => simp only [← sepConj_assoc]
        refine SepWP.weaken_pre (by sep_entail)
          (cliIoWriteFile_nul_scan_loop pathBytes (idx := 0) (n := pathBytes.length)
            (pathPtr := pathPtr) (dst := s0.sp - 4180#64) (scratchPtr := s0.sp - 84#64)
            (F := F_err) (sc0 := sc0)
            h1_pos (Nat.zero_add _) hlt
            (by simp [arm64_norm])
            (by simpa [arm64_norm] using hrun1')
            (by simp only [State.spAligned, arm64_norm]; exact hsp0)
            (by simp [arm64_norm, hx0_1', bv_lin_norm])
            (by simp [arm64_norm, bv_lin_norm])
            (by simp [arm64_norm, bv_lin_norm])
            (by simp [arm64_norm])
            (fun sf_scan sc1 hpc_scan hpres_scan _ => ?_)
            (fun _ _ _ _ hno => False.elim (hno 0#8 hnul rfl)))
        -- At `+0x098 = 152#64`: `mov w0, #1; b +0x110` (`272#64`).
        have hrun_scan := hpres_scan.run_eq
        have hsp_scan := hpres_scan.spAligned_eq
        have hsp_scan_eq : sf_scan.sp = s0.sp - 4192#64 :=
          hpres_scan.sp_eq.trans (by simp [arm64_norm])
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_scan)
          fun se hcpu_e0 hcl_e hnsp_e _ => ?_
        have hcpu_e := hcpu_e0.1
        have ⟨⟨hfs_0e, htr_0e⟩, hsys_0e⟩ :=
          syscallPreserved_of_seg hcpu1_0 hcpu_e0 hnsp_e
            ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
              (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
            ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
              (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
        have hpc_e : se.pc = cliIoPl01.base + 272#64 :=
          hcpu_e.pc_eq.trans (by simp [arm64_norm])
        have hrun_e : se.status = .Running := hcpu_e.status_eq.trans hrun_scan
        have hsp_e : se.sp = s0.sp - 4192#64 :=
          hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sf_scan.sp).trans hsp_scan_eq)
        have hx0_e : se.readReg64 .x0 = 1#64 :=
          (hcpu_e.readReg64 .x0).trans (by simp [arm64_norm])
        have hx26_e : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
          (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
            (hpres_scan.x26_eq.trans ((by simp [arm64_norm] : _ = s1'.readReg64 _).trans
              (hcpu1.readReg64 _))))
        have hx27_e : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
          (hcpu_e.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
            (hpres_scan.x27_eq.trans ((by simp [arm64_norm] : _ = s1'.readReg64 _).trans
              (hcpu1.readReg64 _))))
        have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
          hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
            (hpres_scan.vregs_eq.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
        have hmerge84 :
            ((s0.sp - 84#64) ↦₈ sc1) ∗ memRegion (s0.sp - 83#64) 3 ⊢
              memRegion (s0.sp - 84#64) 4 := by
          simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 84#64) sc1 3 (by decide)
        refine SepWP.weaken_pre ?_
          (cliIoWriteFile_ret_epilogue hext1
            (R_out := memcpySrc ro pathPtr pathBytes ∗ R_rest)
            hlo hhi hcl_e hpc_e hrun_e hsp0 hsp_e hx26_e hx27_e hvregs_e
            fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hx0_f hfs_ef htr_ef hsys_ef _ hent =>
              herr_ret (Or.inr hnul) sf hpc_f hrun_f hsp_f hcs_f hcl_f
                (hx0_f.trans hx0_e) (hfs_ef.trans hfs_0e) (htr_ef.trans htr_0e)
                (syscallPreserved_trans hsys_0e hsys_ef) hent)
        dsimp only [F_err]
        let KeepErr1 : SepProp :=
          stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            memRegion (s0.sp - 4180#64) 4096 ∗
            cliIoSavedRegs10 s0 ∗
            memcpySrc ro pathPtr pathBytes ∗ R_rest
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := KeepErr1) hmerge84)
            (by dsimp only [KeepErr1]; simp only [bv_lin_norm]; sep_entail))
        dsimp only [KeepErr1]; simp only [bv_lin_norm]; sep_entail
    · -- Valid NUL-free `< 4096` path: reaches `bl open` (`+0x080 = 128#64`).
      apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl0
        (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
      intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl01.base := hcpu1.pc_eq.trans hpc0
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
        (hcpu1.readReg64 .x1).trans hx1_bv
      have hx2_1' : s1'.readReg64 .x2 = buf := (hcpu1.readReg64 .x2).trans hx2
      have hx3_1' : s1'.readReg64 .x3 = BitVec.ofNat 64 bsLen :=
        (hcpu1.readReg64 .x3).trans hx3_bv
      have hrefold4180 := memRegion4096_refold_probe4 (s0.sp - 4180#64) 0#64
      by_cases hnil : pathBytes = []
      · subst hnil
        have hnil_len : ([] : List (BitVec 8)).length = 0 := rfl
        rw [hnil_len] at hx1_1'
        apply rustSepWP_cut (mid := cliIoPl01.base + 104#64)
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
        have hcarve4180 :
            memRegion (s0.sp - 4180#64) 4096 =
              ((∃∗ z0 : BitVec 8, (s0.sp - 4180#64) ↦₈ z0) ∗ memRegion (s0.sp - 4179#64) 4095) := by
          simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 4180#64) 0 4095 (by decide)
        let KeepEmpty0 : SepProp :=
          memcpySrc ro pathPtr [] ∗
            stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            memRegion (s0.sp - 84#64) 4 ∗
            cliIoSavedRegs10 s0 ∗ R_rest
        refine SepWP.weaken_pre
          (P' := ((∃∗ z0 : BitVec 8, (s0.sp - 4180#64) ↦₈ z0) ∗ memRegion (s0.sp - 4179#64) 4095) ∗
            KeepEmpty0)
          (by rw [← hcarve4180,
                hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
                hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 25#5),
                hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
                hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
                hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
              refine Entails.trans ?_
                (Entails.trans (sepConj_mono_left (Q := KeepEmpty0) hrefold4180)
                  (by dsimp only [KeepEmpty0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail))
              dsimp only [KeepEmpty0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail) ?_
        wp_conv_pre =>
          dsimp only [KeepEmpty0]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_left; intro z0
        wp_sym_steps
        refine SepWP.done cliIoWriteFile_open_pc (by simpa [arm64_norm] using hrun1')
          fun sm hcpu_m0 hcl_m hnsp_m _ => ?_
        have hcpu_m := hcpu_m0.1
        have ⟨⟨hfs_0m, htr_0m⟩, hsys_0m⟩ :=
          syscallPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m
            (by simp [arm64_norm]) (by simp [arm64_norm])
        have hsp_m_eq : sm.sp = s0.sp - 4192#64 := hcpu_m.sp_eq.trans (by simp [arm64_norm])
        have hsp_m : sm.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 4192#64 hsp0
        have hw1_m : sm.readReg32 .x1 =
            1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32 := by
          rw [State.readReg32, hcpu_m.readReg64 .x1]
          simp only [arm64_norm]
          decide
        have hw2_m : sm.readReg32 .x2 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK := by
          rw [State.readReg32, hcpu_m.readReg64 .x2]
          simp only [arm64_norm]
          decide
        refine SepWP.weaken_pre ?_
          (hat_open hlt hnul sm hcl_m
            (hcpu_m.pc_eq.trans cliIoWriteFile_open_pc) (hcpu_m.status_eq.trans hrun1')
            hsp_m_eq hsp_m
            (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
            (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
            hw1_m hw2_m
            (by rw [hcpu_m.readReg64]; simp [arm64_norm])
            (by rw [hcpu_m.readReg64]; simp [arm64_norm])
            (by rw [hcpu_m.readReg64]; simp only [arm64_norm]; exact hcpu1.readReg64 _)
            (by rw [hcpu_m.readReg64]; simp only [arm64_norm]; exact hcpu1.readReg64 _)
            (hcpu_m.calleeSavedVRegs.trans
              ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
            hfs_0m htr_0m hsys_0m)
        have hcstr_nil : cstrBytes (cPathOf []) = [0#8] := by rw [cstrBytes_cPathOf]; rfl
        rw [hcstr_nil, pointsToBytes_singleton]
        simp only [bv_lin_norm]
        sep_entail
      · have h1_pos : 1 ≤ pathBytes.length := List.length_pos_iff.mpr hnil
        have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
          bv64_beq_ofNat_false (b := 0) (by omega) hpath_lt64 (by decide)
        apply rustSepWP_cut (mid := cliIoPl01.base + 76#64)
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
        have hcarve84 :
            memRegion (s0.sp - 84#64) 4 =
              ((∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗ memRegion (s0.sp - 83#64) 3) := by
          simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 84#64) 0 3 (by decide)
        let F_ok : SepProp :=
          memRegion (s0.sp - 83#64) 3 ∗
            stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            cliIoSavedRegs10 s0 ∗ R_rest
        refine SepWP.weaken_pre
          (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
            memRegion ((s0.sp - 4180#64) + 0#64) 4096 ∗
            (∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗ F_ok) ?_ ?_
        · rw [hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
            hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 25#5),
            hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
            hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
            hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5),
            show s0.sp - (84 : BitVec 64) = s0.sp - 84#64 from rfl, hcarve84]
          dsimp only [F_ok, cliIoSavedRegs10]; simp only [bv_lin_norm]
          let KeepOk0 : SepProp :=
            memcpySrc ro pathPtr pathBytes ∗
              stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
              memRegion (s0.sp - 4192#64) 12 ∗
              (∃∗ sc0 : BitVec 8, (s0.sp - 84#64) ↦₈ sc0) ∗
              memRegion (s0.sp - 83#64) 3 ∗
              cliIoSavedRegs10 s0 ∗ R_rest
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := KeepOk0) hrefold4180)
              (by dsimp only [KeepOk0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail))
          dsimp only [KeepOk0, cliIoSavedRegs10]; simp only [bv_lin_norm]; sep_entail
        · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_left; intro sc0
          wp_conv_pre => simp only [← sepConj_assoc]
          refine SepWP.weaken_pre (by sep_entail)
            (cliIoWriteFile_nul_scan_loop pathBytes (idx := 0) (n := pathBytes.length)
              (pathPtr := pathPtr) (dst := s0.sp - 4180#64) (scratchPtr := s0.sp - 84#64)
              (F := F_ok) (sc0 := sc0)
              h1_pos (Nat.zero_add _) hlt
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun1')
              (by simp only [State.spAligned, arm64_norm]; exact hsp0)
              (by simp [arm64_norm, hx0_1', bv_lin_norm])
              (by simp [arm64_norm, bv_lin_norm])
              (by simp [arm64_norm, bv_lin_norm])
              (by simp [arm64_norm])
              (fun _ _ _ _ hmem => False.elim (hnul hmem))
              (fun sf_scan sc1 hpc_scan hpres_scan _ => ?_))
          dsimp only [F_ok]
          wp_conv_pre =>
            rw [show 4096 - pathBytes.length = (4095 - pathBytes.length) + 1 by omega,
              memRegion_succ_off (s0.sp - 4180#64) pathBytes.length (4095 - pathBytes.length) (by omega)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_left; intro z_nul
          have hx1_scan : sf_scan.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
            hpres_scan.x1_eq.trans (by simp [arm64_norm, hx1_1'])
          have hsp_scan_eq : sf_scan.sp = s0.sp - 4192#64 :=
            hpres_scan.sp_eq.trans (by simp [arm64_norm])
          have hrun_scan := hpres_scan.run_eq
          have hsp_scan := hpres_scan.spAligned_eq
          wp_sym_steps
          refine SepWP.done cliIoWriteFile_open_pc (by simpa [arm64_norm] using hrun_scan)
            fun sm hcpu_m0 hcl_m hnsp_m _ => ?_
          have hcpu_m := hcpu_m0.1
          have ⟨⟨hfs_0m, htr_0m⟩, hsys_0m⟩ :=
            syscallPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m
              ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
                (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
              ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
                (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
          have hsp_m_eq : sm.sp = s0.sp - 4192#64 :=
            hcpu_m.sp_eq.trans ((by simp [arm64_norm] : _ = sf_scan.sp).trans hsp_scan_eq)
          have hsp_m : sm.spAligned = true := by
            simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 4192#64 hsp0
          have hw1_m : sm.readReg32 .x1 =
              1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32 := by
            rw [State.readReg32, hcpu_m.readReg64 .x1]
            simp only [arm64_norm]
            decide
          have hw2_m : sm.readReg32 .x2 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK := by
            rw [State.readReg32, hcpu_m.readReg64 .x2]
            simp only [arm64_norm]
            decide
          have hx19_m : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bsLen :=
            (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
              (hpres_scan.x19_eq.trans (by simp [arm64_norm])))
          have hx20_m : sm.readReg64 (.gpr 20#5) = buf :=
            (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
              (hpres_scan.x20_eq.trans (by simp [arm64_norm])))
          have hx26_m : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
            (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
              (hpres_scan.x26_eq.trans ((by simp [arm64_norm] : _ = s1'.readReg64 _).trans
                (hcpu1.readReg64 _))))
          have hx27_m : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
            (hcpu_m.readReg64 _).trans ((by simp [arm64_norm] : _ = sf_scan.readReg64 _).trans
              (hpres_scan.x27_eq.trans ((by simp [arm64_norm] : _ = s1'.readReg64 _).trans
                (hcpu1.readReg64 _))))
          have hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
            hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
              (hpres_scan.vregs_eq.trans
                ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
          refine SepWP.weaken_pre ?_
            (hat_open hlt hnul sm hcl_m
              (hcpu_m.pc_eq.trans cliIoWriteFile_open_pc) (hcpu_m.status_eq.trans hrun_scan)
              hsp_m_eq hsp_m
              (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
              (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
              hw1_m hw2_m hx19_m hx20_m hx26_m hx27_m hvregs_m hfs_0m htr_0m hsys_0m)
          have hmerge84 :
              ((s0.sp - 84#64) ↦₈ sc1) ∗ memRegion (s0.sp - 83#64) 3 ⊢
                memRegion (s0.sp - 84#64) 4 := by
            simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 84#64) sc1 3 (by decide)
          have hcstr_eq :
              ((s0.sp - 4180#64) ↦ₛ pathBytes) ∗
                (((s0.sp - 4180#64) + BitVec.ofNat 64 pathBytes.length) ↦₈ 0#8) =
              ((s0.sp - 4180#64) ↦ₛ cstrBytes (cPathOf pathBytes)) := by
            rw [cstrBytes_cPathOf, pointsToBytes_snoc]
          let KeepOk1 : SepProp :=
            stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
              memRegion (s0.sp - 4192#64) 12 ∗
              ((s0.sp - 4180#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
              memRegion ((s0.sp - 4180#64) + BitVec.ofNat 64 (pathBytes.length + 1))
                (4095 - pathBytes.length) ∗
              cliIoSavedRegs10 s0 ∗
              memcpySrc ro pathPtr pathBytes ∗ R_rest
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := KeepOk1) hmerge84)
              (by dsimp only [KeepOk1]; simp only [bv_lin_norm]; sep_entail))
          dsimp only [KeepOk1]
          rw [← hcstr_eq]
          simp only [bv_lin_norm]
          sep_entail

/-! ## 6. `open` Call (`+0x080`) and `open < 0` `__errno_location` Error Branch (`+0x084 .. +0x12c`) -/

private theorem getLsbD_31_of_readReg32_eq {s : State} {r : Reg} {w : BitVec 32}
    (h : s.readReg32 r = w) :
    (s.readReg64 r).getLsbD 31 = w.getLsbD 31 := by
  have ht : (s.readReg64 r).truncate 32 = w := h
  rw [← ht]; simp

theorem getLsbD_31_of_fd_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  have hlt32 : fd.toNat < 2 ^ 32 := Nat.lt_trans hfd (by decide)
  have htr : (fd.truncate 32).toNat = fd.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt32]
  have hd : fd.toNat / 2 ^ 31 = 0 := Nat.div_eq_of_lt hfd
  simp only [BitVec.getLsbD, htr, Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

theorem readReg32_zeroExtend_of_truncate {w : BitVec 32} {fd : BitVec 64}
    (hw : w = fd.truncate 32) (hfd : fd.toNat < 2 ^ 32) :
    w.zeroExtend 64 = fd := by
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hfd, Nat.mod_eq_of_lt (Nat.lt_trans hfd (by decide))]

/-- Execute `bl open` (`+0x080`) via `muslOpenCreateTruncSpec fd`:
    - When `fsCanWriteFile s0.fs (cPathOf pathBytes) = false`, steps through `+0x084 .. +0x09c`
      (`bl __errno_location`, `err ∈ {2, 20, 21, 36} ≠ 4 = EINTR`, `mov w0, #1`, `b +0x110`) and
      `cliIoWriteFile_ret_epilogue` returning `x0 = 1#64` with `sf.fs = s0.fs` and
      `sf.trace = s0.trace`.
    - When `fsCanWriteFile s0.fs (cPathOf pathBytes) = true`, refolds the `112`-B `open` frame and
      `cstrBytes` buffer and hands off at `+0x084` (`132#64`) with `w0 = fd.truncate 32`. -/
theorem cliIoWriteFile_open_step [CliIoPlacement]
    {P : Program} {fd : BitVec 64}
    (hext1 : CliIoBlockNoExtern cliIoMpl P 1)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
      (muslOpenCreateTruncSpec fd))
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    {s0 sm : State} {buf : BitVec 64} {pathBytes : List (BitVec 8)}
    {bsLen stackBytes : Nat} {R_keep : SepProp}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 4304 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hlt : pathBytes.length < 4096)
    (hrel : ValidRelCPath (cPathOf pathBytes))
    (halloc : s0.fs.allocFd = some fd) (hfd_lt : fd.toNat < 2 ^ 31)
    (hcl_m : signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem)
    (hpc_m : sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
    (hrun_m : sm.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_m_eq : sm.sp = s0.sp - 4192#64) (hsp_m : sm.spAligned = true)
    (hlr_m : sm.readReg64 .lr = cliIoPl01.base + 132#64)
    (hx0_m : sm.readReg64 .x0 = s0.sp - 4180#64)
    (hw1_m : sm.readReg32 .x1 = 1#32 ||| O_CREAT_W32 ||| O_TRUNC_W32 ||| O_CLOEXEC_W32)
    (hw2_m : sm.readReg32 .x2 &&& O_CREAT_OWNER_RW_MASK = O_CREAT_OWNER_RW_MASK)
    (hx19_m : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bsLen)
    (hx20_m : sm.readReg64 (.gpr 20#5) = buf)
    (hx26_m : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27_m : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hfs_0m : sm.fs = s0.fs) (htr_0m : sm.trace = s0.trace)
    (hsys_0m : SyscallPreserved s0 sm)
    (herr_ret : fsCanWriteFile s0.fs (cPathOf pathBytes) = false →
      ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
        sf.readReg64 .x0 = 1#64 →
        sf.fs = s0.fs → sf.trace = s0.trace →
        SyscallPreserved s0 sf →
        ∀ {Pre_f : SepProp},
          (Pre_f ⊢ stackAt s0.sp stackBytes ∗ StdErrnoCell s0.tpidrEl0 ∗ R_keep) →
          post sf Pre_f)
    (hok_open : fsCanWriteFile s0.fs (cPathOf pathBytes) = true →
      ∀ so : State,
        signalSessionIoMultiLib.CodeLoaded cliIoMpl so.mem →
        so.pc = cliIoPl01.base + 132#64 →
        so.status = .Running →
        so.sp = s0.sp - 4192#64 →
        so.spAligned = true →
        so.readReg32 .x0 = fd.truncate 32 →
        so.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bsLen →
        so.readReg64 (.gpr 20#5) = buf →
        so.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) →
        so.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) →
        calleeSavedVRegs so = calleeSavedVRegs s0 →
        so.fs = (s0.fs.setFile (cPathOf pathBytes) (some (.file []))).setFd fd
          (some { path := cPathOf pathBytes, accMode := .wronly, append := false,
                  cloexec := true, offset := 0 }) →
        so.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] →
        SyscallPreserved s0 so →
        SepWP P (s0.readReg64 .lr) so
          (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            memRegion (s0.sp - 4180#64) 4096 ∗
            memRegion (s0.sp - 84#64) 4 ∗
            cliIoSavedRegs10 s0 ∗
            StdErrnoCell s0.tpidrEl0 ∗
            R_keep)
          post oomProp) :
    SepWP P (s0.readReg64 .lr) sm
      (stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
        memRegion (s0.sp - 4192#64) 12 ∗
        ((s0.sp - 4180#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
        memRegion ((s0.sp - 4180#64) + BitVec.ofNat 64 (pathBytes.length + 1))
          (4095 - pathBytes.length) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        cliIoSavedRegs10 s0 ∗
        StdErrnoCell s0.tpidrEl0 ∗
        R_keep)
      post oomProp := by
  have hlo4192 : 4192 ≤ stackBytes := by omega
  have h112_le : 112 ≤ stackBytes - 4192 := by omega
  have hsb_hi : stackBytes - 4192 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 112 h112_le hsb_hi]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro e0
  let T_open : SepProp :=
    memRegion (s0.sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192)) (stackBytes - 4192 - 112) ∗
      memRegion (s0.sp - 4192#64) 12 ∗
      memRegion ((s0.sp - 4180#64) + BitVec.ofNat 64 (pathBytes.length + 1))
        (4095 - pathBytes.length) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      cliIoSavedRegs10 s0 ∗
      R_keep
  apply seqCodeLoaded hcl_m (mid := cliIoPl01.base + 132#64)
  apply (SepWP.call_subroutine_frame hopen (F := T_open)
    (x := (s0.sp - 4180#64, cPathOf pathBytes, e0))
    hpc_m hrun_m hsp_m hlr_m
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [muslOpenCreateTruncSpec, T_open]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_m, hw1_m, hw2_m, hrel, by rw [hfs_0m]; exact halloc, hfd_lt⟩, ?_⟩
    refine Satisfies.mono ?_ hm'
    rw [muslErrnoAddr_eq_stdErrnoAddr sm, hsys_0m.1, hsp_m_eq]
    sep_frame
  · intro so hpc_so hrun_so hsp_so hcs_so
    refine SepWP.done hpc_so hrun_so fun hcl_so => ?_
    have hsp_so_eq : so.sp = s0.sp - 4192#64 := hsp_so.trans hsp_m_eq
    have hsp_so_al : so.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_so_eq]; exact s0.spAligned_sub 4192#64 hsp0
    have hx19_so : so.readReg64 (.gpr 19#5) = BitVec.ofNat 64 bsLen :=
      hcs_so.1.trans hx19_m
    have hx20_so : so.readReg64 (.gpr 20#5) = buf :=
      hcs_so.2.1.trans hx20_m
    have hx26_so : so.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
      hcs_so.2.2.2.2.2.2.2.1.trans hx26_m
    have hx27_so : so.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
      hcs_so.2.2.2.2.2.2.2.2.1.trans hx27_m
    have hvregs_so : calleeSavedVRegs so = calleeSavedVRegs s0 :=
      hcs_so.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m
    have hrefold_cstr := refold_cstr_buf4096 (s0.sp - 4180#64) pathBytes hlt
    dsimp only [muslOpenCreateTruncSpec, T_open]
    rw [hfs_0m]
    by_cases hcan : fsCanWriteFile s0.fs (cPathOf pathBytes) = true
    · -- `open` succeeded: refold `112`-B stack and `cstrBytes`, hand off at `+0x084`.
      wp_conv_pre => simp only [hcan, ↓reduceIte, sepConj_assoc]
      apply SepWP.pure_elim
      rintro ⟨hw0_so, hfs_so, htr_so_m, hsys_so⟩
      have htr_so :
          so.trace = s0.trace ++ [.fileChanged (normalizePath (cPathOf pathBytes)).toPathString] :=
        htr_so_m.trans (by rw [htr_0m])
      have hsys_0so : SyscallPreserved s0 so := syscallPreserved_trans hsys_0m hsys_so
      refine SepWP.weaken_pre ?_
        (hok_open hcan so hcl_so hpc_so hrun_so hsp_so_eq hsp_so_al hw0_so
          hx19_so hx20_so hx26_so hx27_so hvregs_so hfs_so htr_so hsys_0so)
      rw [muslErrnoAddr_eq_stdErrnoAddr so, hsys_0so.1, hsp_m_eq,
        stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 112 h112_le hsb_hi]
      dsimp only [StdErrnoCell]
      let KeepOpenOk : SepProp :=
        (memRegion (s0.sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192))
            (stackBytes - 4192 - 112) ∗
          stackAt (s0.sp - 4192#64) 112) ∗
          memRegion (s0.sp - 4192#64) 12 ∗
          memRegion (s0.sp - 84#64) 4 ∗
          cliIoSavedRegs10 s0 ∗
          (∃∗ v : BitVec 32, stdErrnoAddr s0.tpidrEl0 ↦₃₂ v) ∗
          R_keep
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_left (Q := KeepOpenOk) hrefold_cstr)
          (by dsimp only [KeepOpenOk]; sep_entail))
      dsimp only [KeepOpenOk]
      refine Entails.trans ?_
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_left (Entails.sepExists_right e0 (Entails.refl _))))))))
      sep_entail
    · -- `open` returned `-1` (`0xffffffff#32`): run `+0x084 .. +0x09c` + epilogue.
      have hcan_f : fsCanWriteFile s0.fs (cPathOf pathBytes) = false :=
        Bool.eq_false_iff.mpr hcan
      wp_conv_pre =>
        simp only [hcan_f, Bool.false_eq_true, ↓reduceIte,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro err
      apply SepWP.pure_elim
      rintro ⟨hw0_so, herr_cases, hfs_so, htr_so_m, hsys_so⟩
      have htr_so : so.trace = s0.trace := htr_so_m.trans htr_0m
      have hsys_0so : SyscallPreserved s0 so := syscallPreserved_trans hsys_0m hsys_so
      -- Step `+0x084 .. +0x088`: `tbz w0, #0x1f` falls through to `bl __errno_location`.
      apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_so
        (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym)
      intro so' hcpu_o0; have hcpu_o := hcpu_o0.1
      change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
      have hpc_o' : so'.pc = cliIoPl01.base + 132#64 := hcpu_o.pc_eq.trans hpc_so
      have hrun_o' : so'.status = .Running := hcpu_o.status_eq.trans hrun_so
      have hsp_o' : so'.spAligned = true := by rw [hcpu_o.spAligned]; exact hsp_so_al
      have hbit31_o' : (so'.readReg64 .x0).getLsbD 31 = true := by
        rw [hcpu_o.readReg64 .x0, getLsbD_31_of_readReg32_eq hw0_so]; decide
      wp_sym_steps
      refine SepWP.done cliIoWriteFile_errno_pc (by simpa [arm64_norm] using hrun_o')
        fun sm1 hcpu_10 hcl_1 hnsp_1 _ => ?_
      have hcpu_1 := hcpu_10.1
      have ⟨⟨hfs_o1, htr_o1⟩, hsys_o1⟩ :=
        syscallPreserved_of_seg hcpu_o0 hcpu_10 hnsp_1
          (by simp [arm64_norm]) (by simp [arm64_norm])
      have hsys_01 : SyscallPreserved s0 sm1 := syscallPreserved_trans hsys_0so hsys_o1
      have hpc_1 : sm1.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoErrnoLocationSym :=
        hcpu_1.pc_eq.trans cliIoWriteFile_errno_pc
      have hrun_1 : sm1.status = .Running := hcpu_1.status_eq.trans hrun_o'
      have hsp_1_eq : sm1.sp = s0.sp - 4192#64 :=
        hcpu_1.sp_eq.trans ((by simp [arm64_norm] : _ = so'.sp).trans (hcpu_o.sp_eq.trans hsp_so_eq))
      have hsp_1 : sm1.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_1_eq]; exact s0.spAligned_sub 4192#64 hsp0
      have hlr_1 : sm1.readReg64 .lr = cliIoPl01.base + 140#64 := by
        rw [hcpu_1.readReg64 .lr]; simp [arm64_norm]
      have hx26_1 : sm1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
        (hcpu_1.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
          ((hcpu_o.readReg64 _).trans hx26_so))
      have hx27_1 : sm1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
        (hcpu_1.readReg64 _).trans ((by simp [arm64_norm] : _ = so'.readReg64 _).trans
          ((hcpu_o.readReg64 _).trans hx27_so))
      have hvregs_1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 :=
        hcpu_1.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs so').trans
          (hcpu_o.calleeSavedVRegs.trans hvregs_so))
      -- Refold `112`-B `open` frame and `cstrBytes` before `muslErrnoLocationSpec`.
      let T_el : SepProp :=
        stackAt (s0.sp - 4192#64) (stackBytes - 4192) ∗
          memRegion (s0.sp - 4192#64) 12 ∗
          memRegion (s0.sp - 4180#64) 4096 ∗
          memRegion (s0.sp - 84#64) 4 ∗
          cliIoSavedRegs10 s0 ∗
          (stdErrnoAddr s0.tpidrEl0 ↦₃₂ err) ∗
          R_keep
      refine SepWP.weaken_pre (P' := T_el) ?_ ?_
      · dsimp only [T_el]
        rw [muslErrnoAddr_eq_stdErrnoAddr so, hsys_0so.1, hsp_m_eq,
          stackAt_shrink (s0.sp - 4192#64) (stackBytes - 4192) 112 h112_le hsb_hi]
        let KeepEl0 : SepProp :=
          (memRegion (s0.sp - 4192#64 - BitVec.ofNat 64 (stackBytes - 4192))
              (stackBytes - 4192 - 112) ∗
            stackAt (s0.sp - 4192#64) 112) ∗
            memRegion (s0.sp - 4192#64) 12 ∗
            memRegion (s0.sp - 84#64) 4 ∗
            cliIoSavedRegs10 s0 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ err) ∗
            R_keep
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono_left (Q := KeepEl0) hrefold_cstr)
            (by dsimp only [KeepEl0]; sep_entail))
        dsimp only [KeepEl0]; sep_entail
      · apply seqCodeLoaded hcl_1 (mid := cliIoPl01.base + 140#64)
        apply (SepWP.call_subroutine_frame herrno (F := T_el) (x := ())
          hpc_1 hrun_1 hsp_1 hlr_1
          (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
          (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
        · intro R' hm'
          dsimp only [muslErrnoLocationSpec]; rw [emp_sepConj]
          exact hm'
        · intro se1 hpc_se1 hrun_se1 hsp_se1 hcs_1
          refine SepWP.done hpc_se1 hrun_se1 fun hcl_se1 => ?_
          wp_conv_pre => dsimp only [muslErrnoLocationSpec, T_el]; simp only [sepConj_assoc]
          apply SepWP.pure_elim
          rintro ⟨hx0_se1, _hmem_se1, hstd_1⟩
          have hsys_0se1 : SyscallPreserved s0 se1 :=
            syscallPreserved_trans hsys_01 (syscallPreserved_of_stdState hstd_1)
          have hfs_0se1 : se1.fs = s0.fs := hstd_1.1.trans (hfs_o1.trans hfs_so)
          have htr_0se1 : se1.trace = s0.trace := hstd_1.2.1.trans (htr_o1.trans htr_so)
          have hsp_se1_eq : se1.sp = s0.sp - 4192#64 := hsp_se1.trans hsp_1_eq
          have hsp_se1_al : se1.spAligned = true := by
            simp only [State.spAligned]; rw [hsp_se1_eq]; exact s0.spAligned_sub 4192#64 hsp0
          have hx0_addr : se1.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 := by
            rw [hx0_se1, muslErrnoAddr_eq_stdErrnoAddr sm1, hsys_01.1]
          have hx26_se1 : se1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
            hcs_1.2.2.2.2.2.2.2.1.trans hx26_1
          have hx27_se1 : se1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
            hcs_1.2.2.2.2.2.2.2.2.1.trans hx27_1
          have hvregs_se1 : calleeSavedVRegs se1 = calleeSavedVRegs s0 :=
            hcs_1.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_1
          have herr_ne4 : (err == 4#32) = false := by
            rcases herr_cases with rfl | rfl | rfl | rfl <;> decide
          -- Step `+0x08c .. +0x09c` (`140#64 .. 156#64 -> 272#64`).
          apply sepWP_seg_cliIo_block_pure 1 cliIo1_lt hext1 cliIoBlockNoSvc0_01 hcl_se1
            (mid := cliIoPl01.base + 272#64)
          intro se1' hcpu_se1_0; have hcpu_se1 := hcpu_se1_0.1
          change SepWP (cliIoPC01.rebase cliIoPl01.base (fun _ => none)) _ _ _ _
          have hpc_se1' : se1'.pc = cliIoPl01.base + 140#64 := hcpu_se1.pc_eq.trans hpc_se1
          have hrun_se1' : se1'.status = .Running := hcpu_se1.status_eq.trans hrun_se1
          have hsp_se1' : se1'.spAligned = true := by rw [hcpu_se1.spAligned]; exact hsp_se1_al
          have hx0_se1' : se1'.readReg64 .x0 = stdErrnoAddr s0.tpidrEl0 :=
            (hcpu_se1.readReg64 .x0).trans hx0_addr
          -- Note: `ldr w8, [x0]` compares `(err.zeroExtend 64).truncate 32 == 4#32` or `err.zeroExtend 64 == 4#64`.
          have herr64_ne4 : (err.zeroExtend 64 == 4#64) = false := by
            rcases herr_cases with rfl | rfl | rfl | rfl <;> decide
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_se1')
            fun se2 hcpu_20 hcl_2 hnsp_2 _ => ?_
          have hcpu_2 := hcpu_20.1
          have ⟨⟨hfs_12, htr_12⟩, hsys_12⟩ :=
            syscallPreserved_of_seg hcpu_se1_0 hcpu_20 hnsp_2
              (by simp [arm64_norm]) (by simp [arm64_norm])
          have hsys_02 : SyscallPreserved s0 se2 := syscallPreserved_trans hsys_0se1 hsys_12
          have hpc_2 : se2.pc = cliIoPl01.base + 272#64 :=
            hcpu_2.pc_eq.trans (by simp [arm64_norm])
          have hrun_2 : se2.status = .Running := hcpu_2.status_eq.trans hrun_se1'
          have hsp_2 : se2.sp = s0.sp - 4192#64 :=
            hcpu_2.sp_eq.trans
              ((by simp [arm64_norm] : _ = se1'.sp).trans (hcpu_se1.sp_eq.trans hsp_se1_eq))
          have hx0_2 : se2.readReg64 .x0 = 1#64 :=
            (hcpu_2.readReg64 .x0).trans (by simp [arm64_norm])
          have hx26_2 : se2.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) :=
            (hcpu_2.readReg64 _).trans ((by simp [arm64_norm] : _ = se1'.readReg64 _).trans
              ((hcpu_se1.readReg64 _).trans hx26_se1))
          have hx27_2 : se2.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) :=
            (hcpu_2.readReg64 _).trans ((by simp [arm64_norm] : _ = se1'.readReg64 _).trans
              ((hcpu_se1.readReg64 _).trans hx27_se1))
          have hvregs_2 : calleeSavedVRegs se2 = calleeSavedVRegs s0 :=
            hcpu_2.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se1').trans
              (hcpu_se1.calleeSavedVRegs.trans hvregs_se1))
          refine SepWP.weaken_pre ?_
            (cliIoWriteFile_ret_epilogue hext1
              (R_out := StdErrnoCell s0.tpidrEl0 ∗ R_keep)
              hlo4192 hhi hcl_2 hpc_2 hrun_2 hsp0 hsp_2 hx26_2 hx27_2 hvregs_2
              fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hx0_f hfs_2f htr_2f hsys_2f _ hent =>
                herr_ret hcan_f sf hpc_f hrun_f hsp_f hcs_f hcl_f
                  (hx0_f.trans hx0_2)
                  (hfs_2f.trans (hfs_12.trans hfs_0se1))
                  (htr_2f.trans (htr_12.trans htr_0se1))
                  (syscallPreserved_trans hsys_02 hsys_2f) hent)
          dsimp only [StdErrnoCell]
          refine Entails.trans ?_
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono_left (Entails.sepExists_right err (Entails.refl _))))))))
          sep_entail

end

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileOpenSteps
