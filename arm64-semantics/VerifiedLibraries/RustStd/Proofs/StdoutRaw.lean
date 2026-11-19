/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.OsFunctions
public import VerifiedLibraries.Musl.Proofs.SyscallProof
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Unix Raw `Stdout::write_all` Proof

Placement-generic symbolic execution proof of `<std::sys::stdio::unix::Stdout as std::io::Write>::write_all`
(block `41` of `rustStdIoMultiLib`), parameterized over `[RustStdIoPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
  ProofLib.GenPlacedFetches ProofLib.StdStartup
  VerifiedLibraries.RustStd VerifiedLibraries.Musl

/-! ## `musl` `write(1, ...)` and `<unix::Stdout as Write>::write_all` contracts -/

abbrev unixStdoutWriteAllSym : String :=
  "<std::sys::stdio::unix::Stdout as std::io::Write>::write_all [rust_std_io]"

/-- Contract for `ssize_t write(1, const void *buf, size_t count)` (`32`-byte stack frame)
writing a non-empty byte slice `bs` (`0 < bs.length < 2 ^ 63`, read-only or read-write via `ro`)
to `stdout` (`fd = 1`), clamping the transfer to `MAX_RW_COUNT`
(`chunk := bs.take (min bs.length MAX_RW_COUNT)`). -/
def muslWriteStdout32Spec : Spec (Bool × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, buf, bs) s0 =>
    ⌜s0.readReg32 .x0 = 1#32 ∧ s0.readReg64 .x1 = buf ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ 0 < bs.length ∧
      bs.length < 2 ^ 63 ∧ buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (stackAt s0.sp 32 ∗ stdoutBytesAt ro buf bs)
  post := fun (ro, buf, bs) s0 sf =>
    let chunk := bs.take (min bs.length Arm64.MAX_RW_COUNT)
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧ sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout chunk ∧ SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ stdoutBytesAt ro buf bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Contract for `<std::sys::stdio::unix::Stdout as std::io::Write>::write_all`.
Because `&mut unix::Stdout` is a zero-sized type (`PassMode::Ignore`), `x0 = buf` and
`x1 = bs.length`, returning `io::Result<()>` in `x0` (`0#64 = Ok(())`). -/
def rustUnixStdoutWriteAllSpec [RustStdIoPlacement] :
    Spec (Bool × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ro, buf, bs, osFnCell) s0 =>
    ⌜s0.readReg64 .x0 = buf ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      (0 < bs.length → buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)⌝ ∗
    (stackAt s0.sp 144 ∗
      stdoutBytesAt ro buf bs ∗
      (stdIoMpl.ρ stdOsFunctionsGotSym ↦₆₄ᵣ osFnCell))
  post := fun (ro, buf, bs, osFnCell) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout bs ∧
      SyscallPreserved s0 sf⌝ ∗
    (stackAt s0.sp 144 ∗
      stdoutBytesAt ro buf bs ∗
      (stdIoMpl.ρ stdOsFunctionsGotSym ↦₆₄ᵣ osFnCell))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## Block `41` fetch and `no-svc0` generation -/

private def stdIoLib41 : PlacedLib := rustStdIoMultiLib.blockLib 41
private def stdIoPl41 [RustStdIoPlacement] : Placement :=
  rustStdIoMultiLib.blockPlacement stdIoMpl 41
private theorem stdIoPlaceable41 [RustStdIoPlacement] : stdIoLib41.Placeable stdIoPl41 :=
  rustStdIoMultiLib.placeable_blockLib (by decide) RustStdIoPlacement.placeable
private def stdIoPC41 [RustStdIoPlacement] : Program := stdIoLib41.program stdIoPl41

private def stdIoProg41 : Program :=
  { code := stdIoLib41.text.code, symbols := stdIoLib41.text.symbols }
private def stdIoTree41 : WordTree := word_tree_of% stdIoProg41
private theorem stdIo41_code_eq : stdIoLib41.text.code = stdIoTree41.toBytes := by rfl_kernel
private theorem stdIo41_tree_size : stdIoTree41.checkSize? = some 73 := by rfl_kernel
private def stdIoSymChars41 : List (List Char × Nat) := sym_chars_of% stdIoProg41
private theorem stdIo41_symbols_eq : stdIoLib41.text.symbols = toStringSymbols stdIoSymChars41 := by
  rfl_kernel
private theorem stdIo41_symbols_fresh : allFreshCharSymbols stdIoSymChars41 = true := by rfl_kernel

gen_placed_fetches stdIoPC41 stdIoLib41 stdIoTree41 stdIo41_code_eq stdIo41_tree_size
  via_placement stdIoPl41 stdIoPlaceable41
  [0x0 → 0x20, 0x28 → 0x2c, 0x34 → 0x84, 0xc8 → 0xec]
gen_placed_fnOffs stdIoPC41 stdIoLib41 stdIoSymChars41 stdIo41_symbols_eq stdIo41_symbols_fresh

private theorem rustIoBlockNoSvc0_41 :
    checkBlockNoSvc0 (rustStdIoMultiLib.blockLib 41).text = true := by decide

/-! ## Proof of `rustUnixStdoutWriteAll_ok` -/

section
arm64_proof_prelude

private abbrev unixStdoutSavedSlots (s0 : State) (st0 st1 : BitVec 64) : SepProp :=
  ((s0.sp - 112#64) ↦₆₄ st0) ∗ ((s0.sp - 104#64) ↦₆₄ st1) ∗
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem stdIo41Write_pc [RustStdIoPlacement] :
    stdIoPl41.base + 100#64 + (stdIoPl41.ρ "write" - stdIoPl41.base - 100#64) =
      rustStdIoMultiLib.resolve stdIoMpl "write" := by
  change stdIoPl41.base + 100#64 +
    (rustStdIoMultiLib.resolve stdIoMpl "write" - stdIoPl41.base - 100#64) =
    rustStdIoMultiLib.resolve stdIoMpl "write"
  bv_lin

private theorem stdoutBytesAt_append' (ro : Bool) (a : BitVec 64) (xs ys : List (BitVec 8)) :
    stdoutBytesAt ro a (xs ++ ys) =
      (stdoutBytesAt ro a xs ∗ stdoutBytesAt ro (a + BitVec.ofNat 64 xs.length) ys) := by
  cases ro
  · exact pointsToBytes_append a xs ys
  · exact pointsToBytesRO_append a xs ys

private theorem traceEvent_ofBytes_append' (s : OutputStream) (a b : List (BitVec 8)) :
    TraceEvent.ofBytes s (a ++ b) = TraceEvent.ofBytes s a ++ TraceEvent.ofBytes s b := by
  unfold TraceEvent.ofBytes; exact List.map_append

set_option maxHeartbeats 800000 in
private theorem unixStdoutWriteLoop_from_0x58 [RustStdIoPlacement] {P : Program} {keep : Nat → Bool}
    (hext : ∀ pc, P.externAt? pc = none)
    (hk41 : keep 41 = true)
    (hwrite : subroutine_ok P (rustStdIoMultiLib.resolve stdIoMpl "write")
      (rustStdIoMultiLib.withCodeLoadedWhere keep stdIoMpl muslWriteStdout32Spec))
    (n : Nat) :
    ∀ {s0 s_loop : State} {ro : Bool} {ptr st0 st1 : BitVec 64}
      {rem : List (BitVec 8)} {F : SepProp}
      {post : State → SepProp → Prop} {oomProp : State → SepProp},
      rem.length ≤ n →
      0 < rem.length →
      rem.length < 2 ^ 63 →
      ptr.toNat + rem.length ≤ Arm64.USER_VA_LIMIT →
      rustStdIoMultiLib.CodeLoadedWhere keep stdIoMpl s_loop.mem →
      s_loop.pc = stdIoPl41.base + 88#64 →
      s_loop.status = .Running →
      s0.spAligned = true →
      s_loop.sp = s0.sp - 112#64 →
      s_loop.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length →
      s_loop.readReg64 (.gpr 21#5) = ptr →
      calleeSavedVRegs s_loop = calleeSavedVRegs s0 →
      (∀ (sf : State) (P_f : SepProp),
        (P_f ⊢ stackAt s0.sp 144 ∗ stdoutBytesAt ro ptr rem ∗ F) →
        sf.pc = s0.readReg64 .lr → sf.status = .Running →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
        SyscallPreserved s_loop sf → sf.fs = s_loop.fs →
        sf.trace = s_loop.trace ++ TraceEvent.ofBytes .stdout rem →
        sf.readReg64 .x0 = 0#64 →
        post sf P_f) →
      SepWP P (s0.readReg64 .lr) s_loop
        (stackAt (s0.sp - 112#64) 32 ∗ stdoutBytesAt ro ptr rem ∗
          unixStdoutSavedSlots s0 st0 st1 ∗ F)
        post oomProp := by
  induction n with
  | zero =>
    intro s0 s_loop ro ptr st0 st1 rem F post oomProp hle hpos
    omega
  | succ n ih =>
    intro s0 s_loop ro ptr st0 st1 rem F post oomProp
      hle hrem_pos hrem_lt hva hcl_loop hpc_loop hrun_loop hsp hsp_loop
      hx20_loop hx21_loop hvregs_loop hcont
    apply sepWP_seg_rebase_pureWhere (lib := rustStdIoMultiLib) (mpl := stdIoMpl)
      (keep := keep) hext 41 ⟨by decide, hk41⟩ rustIoBlockNoSvc0_41 hcl_loop
      (mid := rustStdIoMultiLib.resolve stdIoMpl "write")
    intro sl' hcpul; change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
    have hpcl' : sl'.pc = stdIoPl41.base + 88#64 := hcpul.pc_eq.trans hpc_loop
    have hrunl' : sl'.status = .Running := hcpul.status_eq.trans hrun_loop
    have hx20l' : sl'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length :=
      (hcpul.readReg64 (.gpr 20#5)).trans hx20_loop
    have hx21l' : sl'.readReg64 (.gpr 21#5) = ptr :=
      (hcpul.readReg64 (.gpr 21#5)).trans hx21_loop
    clear hpc_loop; wp_sym_steps
    refine SepWP.done stdIo41Write_pc (by simpa [arm64_norm] using hrunl')
      fun sm1 hcpu_m1 hcl1 hnsp1 => ?_
    have hpres_01 : SyscallPreserved s_loop sm1 :=
      syscallPreserved_of_seg hcpul hcpu_m1 hnsp1 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hfs_01 : sm1.fs = s_loop.fs := hnsp1.2.2.2.2.2.2
    have htr_01 : sm1.trace = s_loop.trace := hnsp1.1
    have hpc1 : sm1.pc = rustStdIoMultiLib.resolve stdIoMpl "write" :=
      hcpu_m1.pc_eq.trans stdIo41Write_pc
    have hrun1 : sm1.status = .Running := hcpu_m1.status_eq.trans hrunl'
    have hsp1_eq : sm1.sp = s0.sp - 112#64 :=
      (hcpu_m1.sp_eq.trans (by simp [arm64_norm])).trans (hcpul.sp_eq.trans hsp_loop)
    have hsp1 : sm1.spAligned = true := by
      simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 112#64 hsp
    have hlr1 : sm1.readReg64 .lr =
        stdIoPl41.base + (reloc_call_off% stdIoLib41.text.relocs "write" + 4#64) := by
      rw [hcpu_m1.readReg64 .lr]; simp [arm64_norm]
    have hx0_m1 : sm1.readReg32 .x0 = 1#32 := by
      rw [hcpu_m1.readReg32 .x0]; simp [arm64_norm]
    have hx1_m1 : sm1.readReg64 .x1 = ptr := by
      rw [hcpu_m1.readReg64 .x1]; simp [arm64_norm]
    have hx2_m1 : sm1.readReg64 .x2 = BitVec.ofNat 64 rem.length := by
      rw [hcpu_m1.readReg64 .x2]; simp [arm64_norm]
    have hx20_m1 : sm1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length := by
      rw [hcpu_m1.readReg64 (.gpr 20#5)]; simp [arm64_norm, hx20l']
    have hx21_m1 : sm1.readReg64 (.gpr 21#5) = ptr := by
      rw [hcpu_m1.readReg64 (.gpr 21#5)]; simp [arm64_norm, hx21l']
    have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
      rw [hcpu_m1.calleeSavedVRegs]; simp only [arm64_norm]
      exact hcpul.calleeSavedVRegs.trans hvregs_loop
    rw [← hsp1_eq]
    apply seqCodeLoadedWhere hcl1
      (mid := stdIoPl41.base + (reloc_call_off% stdIoLib41.text.relocs "write" + 4#64))
    apply (SepWP.call_subroutine_frame hwrite
      (x := (ro, ptr, rem))
      hpc1 hrun1 hsp1 hlr1
      (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
      (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
    · intro R' hm'
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, muslWriteStdout32Spec]
      rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoadedWhere keep stdIoMpl sm1.mem⌝,
          sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl1, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_m1, hx1_m1, hx2_m1, hrem_pos, hrem_lt, hva⟩,
        Satisfies.mono (by sep_frame) hm'⟩
    · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
      refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
      dsimp only [MultiPlacedLib.withCodeLoadedWhere, muslWriteStdout32Spec]
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hx0_sf1, hfs_12, htr_12, hpres_12⟩
      rw [CalleeSavedPreserved.iff_regs] at hcs_sf1
      rcases hcs_sf1 with ⟨_, hx20_cs, hx21_cs, _, _, _, _, _, _, _, _, hvregs_cs⟩
      have hsp_sf1_eq : sf1.sp = s0.sp - 112#64 := hsp_sf1.trans hsp1_eq
      have hx20_sf1 : sf1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length :=
        hx20_cs.trans hx20_m1
      have hx21_sf1 : sf1.readReg64 (.gpr 21#5) = ptr :=
        hx21_cs.trans hx21_m1
      have hvregs_sf1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 :=
        hvregs_cs.trans hvregs_m1
      obtain ⟨k, hk_def⟩ : ∃ k, k = min rem.length Arm64.MAX_RW_COUNT := ⟨_, rfl⟩
      obtain ⟨chunk, hchunk_def⟩ : ∃ chunk, chunk = rem.take k := ⟨_, rfl⟩
      obtain ⟨rest, hrest_def⟩ : ∃ rest, rest = rem.drop k := ⟨_, rfl⟩
      have hx0_sf1' : sf1.readReg64 .x0 = BitVec.ofNat 64 chunk.length := by
        rw [hchunk_def, hk_def]; exact hx0_sf1
      have htr_12' : sf1.trace = sm1.trace ++ TraceEvent.ofBytes .stdout chunk := by
        rw [hchunk_def, hk_def]; exact htr_12
      clear hx0_sf1 htr_12
      have hk_le : k ≤ rem.length := hk_def ▸ Nat.min_le_left _ _
      have hk_pos : 0 < k := by rw [hk_def]; simp only [Arm64.MAX_RW_COUNT]; omega
      have hchunk_len : chunk.length = k := by rw [hchunk_def]; exact List.length_take_of_le hk_le
      have hchunk_pos : 0 < chunk.length := by rw [hchunk_len]; exact hk_pos
      have hchunk_le : chunk.length ≤ rem.length := by rw [hchunk_len]; exact hk_le
      have hchunk_lt : chunk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hchunk_le hrem_lt
      have hrest_len : rest.length = rem.length - chunk.length := by
        rw [hrest_def, hchunk_len]; exact List.length_drop
      have hrem_split : chunk ++ rest = rem := by
        rw [hchunk_def, hrest_def, List.take_append_drop]
      by_cases hrest0 : rest.length = 0
      ·
        have hk_eq : k = rem.length := by omega
        have hchunk_eq : chunk = rem := by rw [hchunk_def, hk_eq, List.take_length]
        rw [hchunk_eq] at hx0_sf1' htr_12'
        clear hk_def hchunk_def hrest_def hchunk_len hrest_len hrem_split
        have hne_m1 : BitVec.ofNat 64 rem.length + 1#64 ≠ 0#64 := by bv_omega
        have hbeq_m1 : (BitVec.ofNat 64 rem.length + 1#64 == 0#64) = false := beq_false_of_ne hne_m1
        apply sepWP_seg_rebase_pureWhere (lib := rustStdIoMultiLib) (mpl := stdIoMpl)
          (keep := keep) hext 41 ⟨by decide, hk41⟩ rustIoBlockNoSvc0_41 hcl_sf1 (mid := s0.readReg64 .lr)
        intro s2' hcpu2; change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = stdIoPl41.base + 104#64 := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hsp2_in : s2'.sp = s0.sp - 112#64 := hcpu2.sp_eq.trans hsp_sf1_eq
        have hsp2' : s2'.spAligned = true := by
          simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 112#64 hsp
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 rem.length :=
          (hcpu2.readReg64 .x0).trans hx0_sf1'
        have hx20_2' : s2'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length :=
          (hcpu2.readReg64 (.gpr 20#5)).trans hx20_sf1
        have hx21_2' : s2'.readReg64 (.gpr 21#5) = ptr :=
          (hcpu2.readReg64 (.gpr 21#5)).trans hx21_sf1
        wp_conv_pre => simp only [hsp_sf1_eq, unixStdoutSavedSlots, ← hsp2_in,
          show s0.sp - 104#64 = s2'.sp + 8#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 96#64 = s2'.sp + 16#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 88#64 = s2'.sp + 24#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 80#64 = s2'.sp + 32#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 72#64 = s2'.sp + 40#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 64#64 = s2'.sp + 48#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 56#64 = s2'.sp + 56#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 48#64 = s2'.sp + 64#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 40#64 = s2'.sp + 72#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 32#64 = s2'.sp + 80#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 24#64 = s2'.sp + 88#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 16#64 = s2'.sp + 96#64 by rw [hsp2_in]; bv_lin,
          show s0.sp - 8#64 = s2'.sp + 104#64 by rw [hsp2_in]; bv_lin]
        clear hpc1 hpc_sf1; wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2')
          fun sf hcpu_f _hcl_f hnsp_f => ?_
        have hpres_2f : SyscallPreserved sf1 sf :=
          syscallPreserved_of_seg hcpu2 hcpu_f hnsp_f (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpres_f : SyscallPreserved s_loop sf := hpres_01.trans (hpres_12.trans hpres_2f)
        have hpc_f : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.pc_eq]; simp [arm64_norm]
        have hrun_f : sf.status = .Running :=
          hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun2')
        have hsp_f : sf.sp = s0.sp := by
          rw [hcpu_f.sp_eq]; simp [arm64_norm]
        have hcs_f : CalleeSavedPreserved s0 sf := by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨by rw [hcpu_f.readReg64 .x19]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x20]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x21]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x22]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x23]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x24]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x25]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x26]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x27]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .x28]; simp [arm64_norm],
            by rw [hcpu_f.readReg64 .fp]; simp [arm64_norm], ?_⟩
          rw [hcpu_f.calleeSavedVRegs]; simp only [arm64_norm]
          exact hcpu2.calleeSavedVRegs.trans hvregs_sf1
        have hx0_f : sf.readReg64 .x0 = 0#64 := by
          rw [hcpu_f.readReg64 .x0]; simp [arm64_norm]
        have hfs_f : sf.fs = s_loop.fs := hnsp_f.2.2.2.2.2.2.trans (hfs_12.trans hfs_01)
        have htr_f : sf.trace = s_loop.trace ++ TraceEvent.ofBytes .stdout rem := by
          rw [hnsp_f.1, htr_12', htr_01]
        refine SepWP.weaken_pre ?_
          (SepWP.done hpc_f hrun_f (hcont sf _ (Entails.refl _) hpc_f hrun_f hsp_f hcs_f hpres_f hfs_f htr_f hx0_f))
        rw [hsp1_eq,
            show (144 : Nat) = 32 + 8 * 14 by omega,
            stackAt_split_cells s0.sp 32 14 (by omega)]
        dsimp only [cells]
        simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
          sepExists_sepConj_left, sepExists_sepConj_right, hsp2_in]
        refine Entails.sepExists_right st0 <| Entails.sepExists_right st1 <|
          Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
          Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)
      ·
        have hrest_pos : 0 < rest.length := Nat.pos_of_ne_zero hrest0
        have hrest_le_n : rest.length ≤ n := by omega
        have hrest_lt : rest.length < 2 ^ 63 := by omega
        have hva_rest : (ptr + BitVec.ofNat 64 chunk.length).toNat + rest.length ≤ Arm64.USER_VA_LIMIT := by
          have hadd_toNat : (ptr + BitVec.ofNat 64 chunk.length).toNat = ptr.toNat + chunk.length := by
            simp only [Arm64.USER_VA_LIMIT] at hva
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
          rw [hadd_toNat]; omega
        have hne_m1 : BitVec.ofNat 64 chunk.length + 1#64 ≠ 0#64 := by
          intro h
          have h := congrArg BitVec.toNat h
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show chunk.length < 2 ^ 64 by omega)] at h
          omega
        have hbeq_m1 : (BitVec.ofNat 64 chunk.length + 1#64 == 0#64) = false := beq_false_of_ne hne_m1
        have hchunk_ne0 : BitVec.ofNat 64 chunk.length ≠ 0#64 := by
          intro h
          have h := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show chunk.length < 2 ^ 64 by omega)] at h
          omega
        have hchunk_beq0 : (BitVec.ofNat 64 chunk.length == 0#64) = false := beq_false_of_ne hchunk_ne0
        have hult_f : (BitVec.ofNat 64 rem.length).ult (BitVec.ofNat 64 chunk.length) = false := by
          simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show rem.length < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show chunk.length < 2 ^ 64 by omega)]
          omega
        have hsub_eq : BitVec.ofNat 64 rem.length - BitVec.ofNat 64 chunk.length =
            BitVec.ofNat 64 rest.length := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show rem.length < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show chunk.length < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show rest.length < 2 ^ 64 by omega)]
          omega
        have hrest_ne0 : BitVec.ofNat 64 rest.length ≠ 0#64 := by
          intro h
          have h := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show rest.length < 2 ^ 64 by omega)] at h
          omega
        have hrest_beq0 : (BitVec.ofNat 64 rest.length == 0#64) = false := beq_false_of_ne hrest_ne0
        have hsub_beq0 : (BitVec.ofNat 64 rem.length - BitVec.ofNat 64 chunk.length == 0#64) = false := by
          rw [hsub_eq]; exact hrest_beq0
        clear hk_def hchunk_def hrest_def hchunk_len hrest_len
        apply sepWP_seg_rebase_pureWhere (lib := rustStdIoMultiLib) (mpl := stdIoMpl)
          (keep := keep) hext 41 ⟨by decide, hk41⟩ rustIoBlockNoSvc0_41 hcl_sf1
          (mid := stdIoPl41.base + 88#64)
        intro s2' hcpu2; change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = stdIoPl41.base + 104#64 := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 chunk.length :=
          (hcpu2.readReg64 .x0).trans hx0_sf1'
        have hx20_2' : s2'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rem.length :=
          (hcpu2.readReg64 (.gpr 20#5)).trans hx20_sf1
        have hx21_2' : s2'.readReg64 (.gpr 21#5) = ptr :=
          (hcpu2.readReg64 (.gpr 21#5)).trans hx21_sf1
        clear hpc1 hpc_sf1; wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2')
          fun s_next hcpu_n hcl_n hnsp_n => ?_
        have hpres_2n : SyscallPreserved sf1 s_next :=
          syscallPreserved_of_seg hcpu2 hcpu_n hnsp_n (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpres_0n : SyscallPreserved s_loop s_next := hpres_01.trans (hpres_12.trans hpres_2n)
        have hfs_0n : s_next.fs = s_loop.fs := hnsp_n.2.2.2.2.2.2.trans (hfs_12.trans hfs_01)
        have htr_0n : s_next.trace = s_loop.trace ++ TraceEvent.ofBytes .stdout chunk := by
          rw [hnsp_n.1, htr_12', htr_01]
        have hpc_n : s_next.pc = stdIoPl41.base + 88#64 := by
          rw [hcpu_n.pc_eq]; simp [arm64_norm]
        have hrun_n : s_next.status = .Running :=
          hcpu_n.status_eq.trans (by simpa [arm64_norm] using hrun2')
        have hsp_n : s_next.sp = s0.sp - 112#64 :=
          (hcpu_n.sp_eq.trans (by simp [arm64_norm])).trans (hcpu2.sp_eq.trans hsp_sf1_eq)
        have hx20_n : s_next.readReg64 (.gpr 20#5) = BitVec.ofNat 64 rest.length := by
          rw [hcpu_n.readReg64 (.gpr 20#5)]; simp [arm64_norm]
        have hx21_n : s_next.readReg64 (.gpr 21#5) = ptr + BitVec.ofNat 64 chunk.length := by
          rw [hcpu_n.readReg64 (.gpr 21#5)]; simp [arm64_norm]
        have hvregs_n : calleeSavedVRegs s_next = calleeSavedVRegs s0 := by
          rw [hcpu_n.calleeSavedVRegs]; simp only [arm64_norm]
          exact hcpu2.calleeSavedVRegs.trans hvregs_sf1
        have hbytes_split : stdoutBytesAt ro ptr rem =
            (stdoutBytesAt ro ptr chunk ∗
              stdoutBytesAt ro (ptr + BitVec.ofNat 64 chunk.length) rest) := by
          conv => lhs; rw [← hrem_split]
          exact stdoutBytesAt_append' ro ptr chunk rest
        wp_conv_pre => rw [hsp1_eq, hbytes_split]
        refine SepWP.weaken_pre
          (P' := stackAt (s0.sp - 112#64) 32 ∗
            stdoutBytesAt ro (ptr + BitVec.ofNat 64 chunk.length) rest ∗
            unixStdoutSavedSlots s0 st0 st1 ∗
            (stdoutBytesAt ro ptr chunk ∗ F))
          (by dsimp only [unixStdoutSavedSlots]; sep_entail) ?_
        refine ih hrest_le_n hrest_pos hrest_lt hva_rest hcl_n hpc_n hrun_n hsp hsp_n
          hx20_n hx21_n hvregs_n fun sf P_f hent_ih hpc_f hrun_f hsp_f hcs_f hpres_nf hfs_nf htr_nf hx0_f => ?_
        have hpres_f : SyscallPreserved s_loop sf := hpres_0n.trans hpres_nf
        have hfs_f : sf.fs = s_loop.fs := hfs_nf.trans hfs_0n
        have htr_f : sf.trace = s_loop.trace ++ TraceEvent.ofBytes .stdout rem := by
          rw [htr_nf, htr_0n, List.append_assoc, ← traceEvent_ofBytes_append', hrem_split]
        have hent : P_f ⊢ stackAt s0.sp 144 ∗ stdoutBytesAt ro ptr rem ∗ F := by
          refine Entails.trans hent_ih ?_
          rw [hbytes_split]
          sep_entail
        exact hcont sf P_f hent hpc_f hrun_f hsp_f hcs_f hpres_f hfs_f htr_f hx0_f

set_option maxHeartbeats 800000 in
theorem rustUnixStdoutWriteAll_okWhere [RustStdIoPlacement] {P : Program} {keep : Nat → Bool}
    (hext : ∀ pc, P.externAt? pc = none)
    (hk41 : keep 41 = true := by decide)
    (hwrite : subroutine_ok P (rustStdIoMultiLib.resolve stdIoMpl "write")
      (rustStdIoMultiLib.withCodeLoadedWhere keep stdIoMpl muslWriteStdout32Spec)) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr stdIoMpl unixStdoutWriteAllSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep stdIoMpl rustUnixStdoutWriteAllSpec) := by
  rw [stdIoFnAddr_eq_base 41 unixStdoutWriteAllSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ro, buf, bs, osFnCell⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustUnixStdoutWriteAllSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoadedWhere keep stdIoMpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hva_if⟩, hpre⟩
  rw [show (144 : Nat) = 32 + 8 * 14 by omega,
      stackAt_split_cells s0.sp 32 14 (by omega)] at hpre
  dsimp only [cells] at hpre
  simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10, st11, st12, st13, hpre⟩
  refine ⟨_, hpre, ?_⟩
  by_cases hbs0 : bs.length = 0
  ·
    have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero hbs0
    subst hbs_nil
    apply sepWP_seg_rebase_pureWhere (lib := rustStdIoMultiLib) (mpl := stdIoMpl)
      (keep := keep) hext 41 ⟨by decide, hk41⟩ rustIoBlockNoSvc0_41 hcl (mid := s0.readReg64 .lr)
    intro s0' hcpu0; change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
    have hpc0' : s0'.pc = stdIoPl41.base := hcpu0.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
    have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp
    have hx1' : s0'.readReg64 (.gpr 1#5) = 0#64 := (hcpu0.readReg64 .x1).trans hx1
    have hlr0' : s0'.readReg64 (.gpr 30#5) = s0.readReg64 .lr := hcpu0.readReg64 .lr
    wp_conv_pre => simp only [← hcpu0.sp_eq]
    clear hpc; wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun0')
      fun sf hcpu_f _hcl_f hnsp_f => ?_
    have hpres : SyscallPreserved s0 sf :=
      syscallPreserved_of_seg hcpu0 hcpu_f hnsp_f (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpc_f : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.pc_eq]; simp [arm64_norm]
    have hrun_f : sf.status = .Running :=
      hcpu_f.status_eq.trans (by simpa [arm64_norm] using hrun0')
    have hsp_f : sf.sp = s0.sp := by
      rw [hcpu_f.sp_eq]; simp [arm64_norm, hcpu0.sp_eq]
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨by rw [hcpu_f.readReg64 .x19]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x20]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x21]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x22]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x23]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x24]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x25]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x26]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x27]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .x28]; simp [arm64_norm, hcpu0.readReg64],
        by rw [hcpu_f.readReg64 .fp]; simp [arm64_norm, hcpu0.readReg64], ?_⟩
      rw [hcpu_f.calleeSavedVRegs]; simp only [arm64_norm]; exact hcpu0.calleeSavedVRegs
    have hx0_f : sf.readReg64 .x0 = 0#64 := by
      rw [hcpu_f.readReg64 .x0]; simp [arm64_norm]
    have htr_f : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout [] := by
      simpa [TraceEvent.ofBytes] using hnsp_f.1
    refine SepWP.weaken_pre ?_ (SepWP.done hpc_f hrun_f ⟨id, hsp_f, hcs_f⟩)
    rw [pure_sepConj_of_true ⟨hx0_f, hnsp_f.2.2.2.2.2.2, htr_f, hpres⟩,
        show (144 : Nat) = 32 + 8 * 14 by omega,
        stackAt_split_cells s0.sp 32 14 (by omega)]
    dsimp only [cells]
    simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, hcpu0.sp_eq]
    refine Entails.sepExists_right st0 <| Entails.sepExists_right st1 <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 29#5)) <|
      Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 28#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 27#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 26#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 25#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 24#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 23#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 22#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 21#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 20#5)) <|
      Entails.sepExists_right (s0'.readReg64 (.gpr 19#5)) (by sep_entail)
  ·
    have hlen_pos : 0 < bs.length := Nat.pos_of_ne_zero hbs0
    have hva : buf.toNat + bs.length ≤ Arm64.USER_VA_LIMIT := hva_if hlen_pos
    have hlen_lt : bs.length < 2 ^ 63 := by simp only [Arm64.USER_VA_LIMIT] at hva; omega
    have hx1_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by bv_omega
    have hx1_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne hx1_ne0
    apply sepWP_seg_rebase_pureWhere (lib := rustStdIoMultiLib) (mpl := stdIoMpl)
      (keep := keep) hext 41 ⟨by decide, hk41⟩ rustIoBlockNoSvc0_41 hcl
      (mid := stdIoPl41.base + 88#64)
    intro s0' hcpu0; change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
    have hpc0' : s0'.pc = stdIoPl41.base := hcpu0.pc_eq.trans hpc
    have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
    have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp
    have hx0' : s0'.readReg64 (.gpr 0#5) = buf := (hcpu0.readReg64 .x0).trans hx0
    have hx1' : s0'.readReg64 (.gpr 1#5) = BitVec.ofNat 64 bs.length :=
      (hcpu0.readReg64 .x1).trans hx1
    wp_conv_pre => simp only [← hcpu0.sp_eq]
    clear hpc; wp_sym_steps
    apply sepWP_rebase_adrGotPage_unpaired (lib := stdIoLib41) (pl := stdIoPl41)
      (off := 36) (off4 := 40)
      (r := ⟨36, .adrGotPage, stdOsFunctionsGotSym, 0, false⟩) (rd := 26#5)
      (T := stdIoMpl.ρ stdOsFunctionsGotSym)
      stdIoPlaceable41 rfl rfl rfl (by decide) (by decide)
      (wordAt_of_getQuad? stdIo41_code_eq stdIo41_tree_size (j := 9) rfl)
      (by decide) rfl (by decide) rfl rfl
      (hookAtOff?_rebase_of_placeable stdIo41_code_eq stdIo41_tree_size stdIoPlaceable41 (by omega))
      (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun0')
    change SepWP (stdIoPC41.rebase stdIoPl41.base (fun _ => none)) _ _ _ _
    wp_sym_steps
    have hfe48 : (stdIoPC41.rebase stdIoPl41.base (fun _ => none)).fetch
        (stdIoPl41.base + BitVec.ofNat 64 48) =
        some (.ldr .W64 .X64 false (.gpr 26#5)
          (.Offset (.gpr 26#5) (lo12Of (stdIoMpl.ρ stdOsFunctionsGotSym)))) :=
      fetch_rebase_ld64GotLo12_unpaired (lib := stdIoLib41) (pl := stdIoPl41) (off := 48)
        (r := ⟨48, .ld64GotLo12Nc, stdOsFunctionsGotSym, 0, false⟩)
        (T := stdIoMpl.ρ stdOsFunctionsGotSym)
        stdIoPlaceable41 rfl rfl (by decide) (by decide)
        (hookAtOff?_rebase_of_placeable stdIo41_code_eq stdIo41_tree_size stdIoPlaceable41 (by omega))
        (wordAt_of_getQuad? stdIo41_code_eq stdIo41_tree_size (j := 12) rfl)
        (by decide) (by decide) (by decide) rfl rfl
    wp_step
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun0')
      fun sm0 hcpu_m0 hcl0 hnsp0 => ?_
    have hpres_00 : SyscallPreserved s0 sm0 :=
      syscallPreserved_of_seg hcpu0 hcpu_m0 hnsp0 (by simp [arm64_norm]) (by simp [arm64_norm])
    have hfs_00 : sm0.fs = s0.fs := hnsp0.2.2.2.2.2.2
    have htr_00 : sm0.trace = s0.trace := hnsp0.1
    have hpc0 : sm0.pc = stdIoPl41.base + 88#64 := by
      rw [hcpu_m0.pc_eq]; simp [arm64_norm]
    have hrun0 : sm0.status = .Running := hcpu_m0.status_eq.trans hrun0'
    have hsp0_eq : sm0.sp = s0.sp - 112#64 := by
      rw [hcpu_m0.sp_eq]; simp [arm64_norm, hcpu0.sp_eq]
    have hx20_m0 : sm0.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length := by
      rw [hcpu_m0.readReg64 (.gpr 20#5)]; simp [arm64_norm]
    have hx21_m0 : sm0.readReg64 (.gpr 21#5) = buf := by
      rw [hcpu_m0.readReg64 (.gpr 21#5)]; simp [arm64_norm]
    have hvregs_m0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0 := by
      rw [hcpu_m0.calleeSavedVRegs]; simp only [arm64_norm]; exact hcpu0.calleeSavedVRegs
    refine SepWP.weaken_pre (P' :=
        stackAt (s0.sp - 112#64) 32 ∗ stdoutBytesAt ro buf bs ∗
        unixStdoutSavedSlots s0 st0 st1 ∗
        (stdIoMpl.ρ stdOsFunctionsGotSym ↦₆₄ᵣ osFnCell))
      (by
        simp only [hcpu0.sp_eq, hcpu0.readReg64, unixStdoutSavedSlots, bv_lin_norm]
        sep_entail) ?_
    refine unixStdoutWriteLoop_from_0x58 hext hk41 hwrite bs.length
      (Nat.le_refl _) hlen_pos hlen_lt hva hcl0 hpc0 hrun0 hsp hsp0_eq hx20_m0 hx21_m0 hvregs_m0
      fun sf P_f hent hpc_f hrun_f hsp_f hcs_f hpres_0f hfs_0f htr_0f hx0_f => ?_
    refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
    rw [pure_sepConj_of_true ⟨hx0_f, hfs_0f.trans hfs_00, by rw [htr_0f, htr_00], hpres_00.trans hpres_0f⟩]
    exact Satisfies.mono (sepConj_mono_left hent) hm

theorem rustUnixStdoutWriteAll_ok [RustStdIoPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    (hwrite : subroutine_ok P (rustStdIoMultiLib.resolve stdIoMpl "write")
      (rustStdIoMultiLib.withCodeLoaded stdIoMpl muslWriteStdout32Spec)) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr stdIoMpl unixStdoutWriteAllSym)
      (rustStdIoMultiLib.withCodeLoaded stdIoMpl rustUnixStdoutWriteAllSpec) :=
  rustStdIoMultiLib.subroutine_ok_withCodeLoaded_of_where
    (rustUnixStdoutWriteAll_okWhere (keep := fun _ => true) hext rfl
      (rustStdIoMultiLib.subroutine_ok_withCodeLoadedWhere_of_all hwrite))

end

end VerifiedLibraries.RustStd.Io
