/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import ProofLib.Placed.Split -- proof-setup: allow-public-import
import ProofLib.Placed.CheckText
import ProofLib.Process.FastParse
import ProofLib.ProgramReflection

/-!
# Shared `WordTree` Code-Walk, `seg[1]` Code-Slice, and `.rodata` Helpers

Kernel-friendly layout dischargers shared across `C2RowLayoutFacts` leaf modules
(`Compress512`, `X25519`, `CliIoFmt`, and `MlKem`):
1. `resolve_lsExtern_eq_cliElf_rho`: resolves any `libsignalSessionExterns` symbol under
   `libsignalSessionLib.LinkedAt cliElfBytes mpl` to `cliElfMultiPlacement.ρ s`.
2. `checkCodeBlockWalk` / `checkMultiBlockWalk`: `O(off + len)` unrelaxed word-walk checker against
   `f3TrialRxWordTree.toBytes` (`seg[2]`), avoiding quadratic `CodeBlock.patched` unfolding and
   bridging directly to `checkProgCodeSubslice f3TrialRxProg` and `CodeLoaded`.
3. `checkSeg1BlockSlice` / `f3CodeInv_seg1_blockCodeLoaded`: `seg[1]` (`:text_a`) `CodeLoaded`
   discharger via `f3PatchedElf.segments[1]?` and `F3CodeInv.fromLoad`.
4. `rGetD_map_some_eq_getElem?` / `checkRoSegSlice` / `f3CodeInv_roDataAt_of_roSegSlice`: fast
   `rGetD`/`rLen` `.rodata` (`seg[0]`) `RoDataAt` discharger.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (libsignalSessionExterns)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (libsignalSessionExterns_resolve_eq_rho)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3CodeInv_roDataAt_of_checkSegSlice f3PatchedElf_wellFormed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf f3PatchedElf_eq_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq)

/-! ## 1. Generic `libsignalSessionExterns` Resolution under `LinkedAt cliElfBytes` -/

/-- Resolve any `s ∈ libsignalSessionExterns ∩ lsInternedMultiLib.names` under
    `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl` directly to `cliElfMultiPlacement.ρ s`. -/
theorem resolve_lsExtern_eq_cliElf_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (s : String)
    (hchk : (libsignalSessionExterns.contains s &&
      lsInternedMultiLib.names.contains s) = true := by rfl_kernel) :
    libsignalSessionLib.resolve mpl s = cliElfMultiPlacement.ρ s := by
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hchk
  have huniq := (cliElf_linkedAt_unique hLs).2.1 s hchk.2
  exact huniq.trans (libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement s hchk.1)

/-! ## 2. Linear Unrelaxed Relocation Walk on `f3TrialRxWordTree.toBytes` (`seg[2]`) -/

@[expose] def relocsSorted (len : Nat) : Nat → List RelocEntry → Bool
  | _, [] => true
  | lb, r :: rs =>
    Nat.ble lb r.off && Nat.beq (r.off % 4) 0 && Nat.blt r.off len &&
      relocsSorted len (r.off + 1) rs

private theorem find?_reloc_append_of_lt {o : Nat} :
    ∀ {pre rs : List RelocEntry}, (∀ x ∈ pre, x.off < o) →
      (pre ++ rs).find? (·.off == o) = rs.find? (·.off == o)
  | [], _, _ => rfl
  | x :: xs, rs, hpre => by
    have hx : (x.off == o) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hpre x (List.mem_cons_self ..)))
    simp only [List.cons_append, List.find?_cons, hx]
    exact find?_reloc_append_of_lt fun y hy => hpre y (List.mem_cons_of_mem _ hy)

private theorem find?_reloc_eq_none_of_gt {o len : Nat} :
    ∀ {lb : Nat} {rs : List RelocEntry}, o < lb → relocsSorted len lb rs = true →
      rs.find? (·.off == o) = none
  | _, [], _, _ => rfl
  | lb, r :: rs, hlt, hwf => by
    simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq] at hwf
    have hne : (r.off == o) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [List.find?_cons, hne]
    exact find?_reloc_eq_none_of_gt (by omega) hwf.2

private theorem patchedWord_unrelaxed (blk : CodeBlock) (pl : Placement)
    (hRel : pl.relax = fun _ => false) (hB2b : pl.b2b = fun _ => false)
    (hWeak : pl.undefWeak = fun _ => false) (o : Nat) :
    blk.patchedWord pl o =
      match blk.relocAt? o with
      | none => blk.wordAt o
      | some r =>
        patchRelocWord r.kind (blk.wordAt o) (pl.base + BitVec.ofNat 64 o) (blk.target pl r) := by
  unfold CodeBlock.patchedWord CodeBlock.relaxedAt CodeBlock.undefWeakBranch CodeBlock.relocTarget
  rw [hRel, hB2b, hWeak]
  cases blk.relocAt? o with
  | none => rfl
  | some r => simp

@[expose] def walkUnrelaxed (blk : CodeBlock) (pl : Placement) :
    Nat → List RelocEntry → List (BitVec 8) → List (BitVec 8) → Bool
  | _, _, [], _ => true
  | o, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let place := pl.base + BitVec.ofNat 64 o
        bytesOfWordLE (patchRelocWord r.kind w place (blk.target pl r)) == [s0, s1, s2, s3] &&
          walkUnrelaxed blk pl (o + 4) rs' cs ss
      else
        b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 &&
          walkUnrelaxed blk pl (o + 4) rs cs ss
    | [] =>
      b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 &&
        walkUnrelaxed blk pl (o + 4) [] cs ss
  | _, _, _ :: _, _ => false

theorem walkUnrelaxed_isPrefix {blk : CodeBlock} {pl : Placement}
    (hRel : pl.relax = fun _ => false) (hB2b : pl.b2b = fun _ => false)
    (hWeak : pl.undefWeak = fun _ => false) :
    ∀ (cs seg : List (BitVec 8)) (o : Nat) (pre rs : List RelocEntry),
      blk.code.drop o = cs → o % 4 = 0 → blk.code.length % 4 = 0 →
      blk.relocs = pre ++ rs → (∀ x ∈ pre, x.off < o) →
      relocsSorted blk.code.length o rs = true →
      walkUnrelaxed blk pl o rs cs seg = true →
      ((blk.patched pl).drop o).IsPrefix seg
  | [], _, o, _, _, hcs, _, _, _, _, _, _ => by
    have hlen : blk.code.length ≤ o := by
      have := congrArg List.length hcs; simp at this; omega
    rw [List.drop_eq_nil_of_le (by rw [CodeBlock.length_patched]; omega)]
    exact List.nil_prefix
  | b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss, o, pre, rs,
      hcs, ho, hal, hrel, hpre, hwf, hw => by
    have hlen : o + 4 ≤ blk.code.length := by
      have := congrArg List.length hcs; simp at this; omega
    have hcs' : blk.code.drop (o + 4) = cs := by
      rw [← List.drop_drop, hcs]; rfl
    have htake := CodeBlock.take4_drop_patched (blk := blk) (pl := pl) ho hlen
    have hdrop : ((blk.patched pl).drop o).drop 4 = (blk.patched pl).drop (o + 4) := by
      rw [List.drop_drop, Nat.add_comm]
    have hw1 : blk.wordAt o = b3 ++ b2 ++ b1 ++ b0 := by
      unfold CodeBlock.wordAt
      rw [← Nat.add_zero o, getD_eq_drop_getD_word, hcs, wordOfBytesLE_cons4_zero]
    have hpw := patchedWord_unrelaxed blk pl hRel hB2b hWeak o
    match rs, hwf, hw with
    | [], _, hw =>
      simp only [walkUnrelaxed, Bool.and_eq_true, beq_iff_eq] at hw
      rcases hw with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hw'⟩
      have hnone : blk.relocAt? o = none := by
        unfold CodeBlock.relocAt?; rw [hrel, find?_reloc_append_of_lt hpre]; rfl
      have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) pre []
        hcs' (by omega) hal hrel (fun x hx => by have := hpre x hx; omega) rfl hw'
      refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [b0, b1, b2, b3])
        (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
      rw [hpw, hnone, hw1, Obj.Interned.bytesOfWordLE_append4]
    | r :: rs', hwf, hw =>
      simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq] at hwf
      rcases hwf with ⟨⟨⟨hlb, hmod⟩, hlt_len⟩, hwf'⟩
      simp only [walkUnrelaxed] at hw
      by_cases hro : r.off = o
      · have hbeq : Nat.beq r.off o = true := Nat.beq_eq.mpr hro
        simp only [hbeq, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨hbytes, hw'⟩ := hw
        have hsome : blk.relocAt? o = some r := by
          unfold CodeBlock.relocAt?
          rw [hrel, find?_reloc_append_of_lt hpre]
          simp [beq_iff_eq.mpr hro]
        have hwf4 : relocsSorted blk.code.length (o + 4) rs' = true := by
          cases rs' with
          | nil => rfl
          | cons r2 rs2 =>
            simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hwf' ⊢
            exact ⟨⟨⟨by omega, hwf'.1.1.2⟩, hwf'.1.2⟩, hwf'.2⟩
        have hrel' : blk.relocs = (pre ++ [r]) ++ rs' := by rw [List.append_assoc]; exact hrel
        have hpre' : ∀ x ∈ pre ++ [r], x.off < o + 4 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have := hpre x hx; omega
          · rw [List.mem_singleton.mp hx]; omega
        have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) (pre ++ [r]) rs'
          hcs' (by omega) hal hrel' hpre' hwf4 hw'
        refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [s0, s1, s2, s3])
          (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
        rw [hpw, hsome, hw1, hbytes]
      · have hbeq : Nat.beq r.off o = false :=
          Bool.eq_false_iff.mpr fun hc => hro (Nat.beq_eq.mp hc)
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hw
        rcases hw with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hw'⟩
        have hwf4 : relocsSorted blk.code.length (o + 4) (r :: rs') = true := by
          simp only [relocsSorted, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.blt_eq]
          exact ⟨⟨⟨by omega, hmod⟩, hlt_len⟩, hwf'⟩
        have hnone : blk.relocAt? o = none := by
          unfold CodeBlock.relocAt?
          rw [hrel, find?_reloc_append_of_lt hpre]
          exact find?_reloc_eq_none_of_gt (by omega) hwf4
        have ih := walkUnrelaxed_isPrefix hRel hB2b hWeak cs ss (o + 4) pre (r :: rs')
          hcs' (by omega) hal hrel (fun x hx => by have := hpre x hx; omega) hwf4 hw'
        refine Obj.Interned.prefix_of_take_drop (k := 4) (t := [b0, b1, b2, b3])
          (htake.trans ?_) (by rw [hdrop]; exact ih) rfl
        rw [hpw, hnone, hw1, Obj.Interned.bytesOfWordLE_append4]
  | [_], _, _, _, _, hcs, _, _, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | [_, _], _, _, _, _, hcs, _, _, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | [_, _, _], _, _, _, _, hcs, _, _, _, _, _, _ => by
    have := congrArg List.length hcs; simp at this; omega
  | _ :: _ :: _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw
  | _ :: _ :: _ :: _ :: _, [_, _, _], _, _, _, _, _, _, _, _, _, hw => by simp [walkUnrelaxed] at hw

/-- Linear check that `blk.patched pl` appears inside `rxBytes` (`f3TrialRxWordTree.toBytes`). -/
@[expose] noncomputable def checkCodeBlockWalk (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (blk : CodeBlock) (pl : Placement) : Bool :=
  let len := ProofLib.Placed.Split.rLen blk.code
  let off := (pl.base - f3RxSegBase).toNat
  Nat.beq (len % 4) 0 &&
  Nat.beq (pl.base.toNat % 4) 0 &&
  Nat.ble (pl.base.toNat + len) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = pl.base) &&
  Nat.ble (off + len) rxLen &&
  relocsSorted len 0 blk.relocs &&
  walkUnrelaxed blk pl 0 blk.relocs blk.code (ProofLib.Placed.Split.rDrop off rxBytes)

/-- Linear check that `(lib.blockProgram mpl j)` appears inside `rxBytes`. -/
@[expose] noncomputable def checkMultiBlockWalk (rxBytes : List (BitVec 8)) (rxLen : Nat)
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  checkCodeBlockWalk rxBytes rxLen (lib.blockLib j).text (lib.blockPlacement mpl j)

/-- Any `subProg` with `subProg.base = pl.base` and `subProg.code = blk.patched pl` satisfies
    `checkProgCodeSubslice f3TrialRxProg subProg = true` when `checkCodeBlockWalk` succeeds. -/
theorem checkProgCodeSubslice_of_codeBlockWalk {blk : CodeBlock} {pl : Placement}
    {subProg : Program}
    (hBase : subProg.base = pl.base)
    (hCode : subProg.code = blk.patched pl)
    (hRel : pl.relax = fun _ => false := by rfl)
    (hB2b : pl.b2b = fun _ => false := by rfl)
    (hWeak : pl.undefWeak = fun _ => false := by rfl)
    (h : checkCodeBlockWalk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) blk pl = true) :
    checkProgCodeSubslice f3TrialRxProg subProg = true := by
  unfold checkCodeBlockWalk at h
  dsimp only at h
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rDrop_eq,
    Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hal, hbase4⟩, hnowrap⟩, hbaseEq⟩, hbound⟩, hwf⟩, hwalk⟩
  have hpre : (blk.patched pl).IsPrefix
      (f3TrialRxWordTree.toBytes.drop (pl.base - f3RxSegBase).toNat) :=
    walkUnrelaxed_isPrefix hRel hB2b hWeak blk.code _ 0 [] blk.relocs
      rfl rfl hal rfl (fun _ hx => nomatch hx) hwf hwalk
  obtain ⟨tail, htail⟩ := hpre
  have hplen : (blk.patched pl).length = blk.code.length :=
    CodeBlock.length_patched_of_aligned pl hal
  unfold checkProgCodeSubslice
  rw [hBase, hCode, f3TrialRxProg_base, f3TrialRxWordTree_eq]
  dsimp only
  rw [← htail, List.take_left, hplen]
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_self_eq_true]
  exact ⟨⟨⟨⟨hbase4, hnowrap⟩, hbaseEq⟩, hbound⟩, trivial⟩

/-- Multi-block specialization of `checkProgCodeSubslice_of_codeBlockWalk`. -/
theorem checkProgCodeSubslice_of_multiBlockWalk {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {j : Nat}
    (hRel : (lib.blockPlacement mpl j).relax = fun _ => false := by rfl)
    (hB2b : (lib.blockPlacement mpl j).b2b = fun _ => false := by rfl)
    (hWeak : (lib.blockPlacement mpl j).undefWeak = fun _ => false := by rfl)
    (h : checkMultiBlockWalk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) lib mpl j = true) :
    checkProgCodeSubslice f3TrialRxProg (lib.blockProgram mpl j) = true :=
  checkProgCodeSubslice_of_codeBlockWalk rfl rfl hRel hB2b hWeak h

/-- Direct `CodeLoaded` corollary of `checkProgCodeSubslice_of_multiBlockWalk`. -/
theorem codeLoaded_of_multiBlockWalk {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {j : Nat} {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m)
    (hRel : (lib.blockPlacement mpl j).relax = fun _ => false := by rfl)
    (hB2b : (lib.blockPlacement mpl j).b2b = fun _ => false := by rfl)
    (hWeak : (lib.blockPlacement mpl j).undefWeak = fun _ => false := by rfl)
    (h : checkMultiBlockWalk f3TrialRxWordTree.toBytes
      (ProofLib.Placed.Split.rLen f3TrialRxWordTree.toBytes) lib mpl j = true) :
    (lib.blockProgram mpl j).CodeLoaded m :=
  codeLoaded_of_checkProgCodeSubslice hRx
    (checkProgCodeSubslice_of_multiBlockWalk hRel hB2b hWeak h)

/-! ## 3. Fast `rGetD`/`rLen` `.rodata` (`seg[0]`) & `seg[1]` (`:text_a`) Dischargers -/

theorem rGetD_map_some_eq_getElem? {α : Type} (l : List α) (n : Nat) :
    ProofLib.Placed.Split.rGetD (l.map some) n none = l[n]? := by
  rw [ProofLib.Placed.Split.rGetD_eq]
  induction l generalizing n with
  | nil => simp
  | cons _ as ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

/-- Fast `rGetD`/`rLen` `.rodata` slice check on `elf.segments[f3StdLayout.roSegIdx]?`. -/
@[expose] noncomputable def checkRoSegSlice (elf : Process.ElfImage)
    (addr : BitVec 64) (bytes : List (BitVec 8)) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) f3StdLayout.roSegIdx none with
  | none => false
  | some seg =>
    let roLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.ro) &&
    checkSegSlice seg roLen addr bytes

theorem roSlice_of_checkRoSegSlice {elf : Process.ElfImage}
    {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : checkRoSegSlice elf addr bytes = true) :
    ∃ seg, elf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length addr bytes = true := by
  unfold checkRoSegSlice at h
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : elf.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨seg, rfl, h.1, h.2⟩

/-- Discharge `RoDataAt m addr bytes` from `F3CodeInv` and `checkRoSegSlice f3PatchedElf`. -/
theorem f3CodeInv_roDataAt_of_roSegSlice
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m)
    {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : checkRoSegSlice f3PatchedElf addr bytes = true) :
    RoDataAt m addr bytes :=
  f3CodeInv_roDataAt_of_checkSegSlice hLs hInv addr bytes (roSlice_of_checkRoSegSlice h)

/-- Fast `rGetD`/`rLen` `seg[1]` (`:text_a`) code-block slice check on `elf.segments[1]?`. -/
@[expose] noncomputable def checkSeg1BlockSlice (elf : Process.ElfImage)
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) 1 none with
  | none => false
  | some seg =>
    let blk := (lib.blockLib j).text
    let pl := lib.blockPlacement mpl j
    let patched := blk.patched pl
    let segLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.rx) &&
    Nat.beq (pl.base.toNat % 4) 0 &&
    Nat.ble (pl.base.toNat + patched.length) (2 ^ 64) &&
    checkSegSlice seg segLen pl.base patched

/-- Discharge `(lib.blockProgram mpl j).CodeLoaded m` for blocks placed in `seg[1]` (`:text_a`,
    such as `write_file`, `write_stdout`, and `<String as Clone>::clone`) from `F3CodeInv`. -/
theorem f3CodeInv_seg1_blockCodeLoaded
    {mplLs mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mplLs)
    (hInv : F3CodeInv mplLs mmpl m)
    {lib : MultiPlacedLib} {mpl : MultiPlacement} {j : Nat}
    (h : checkSeg1BlockSlice f3PatchedElf lib mpl j = true) :
    (lib.blockProgram mpl j).CodeLoaded m := by
  obtain ⟨inputs, sLoad, hload, hkf⟩ := hInv.fromLoad
  rw [f3PatchedElf_eq_of_linkedAt hLs] at hload
  unfold checkSeg1BlockSlice at h
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : f3PatchedElf.segments[1]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true,
      decide_eq_true_eq, Nat.beq_eq, Nat.ble_eq] at h
    rcases h with ⟨⟨⟨hperm, hAlign⟩, hNoWrap⟩, hsl⟩
    obtain ⟨hhb0, _, _⟩ :=
      holdsBytes_of_checkSegSlice f3PatchedElf_wellFormed hload hseg hsl
    have hcl0 : (lib.blockProgram mpl j).CodeLoaded sLoad.mem := by
      refine Program.CodeLoaded.intro hAlign hNoWrap fun i hi => ?_
      have hi_hb := hhb0 i hi
      dsimp only at hi_hb
      rw [hperm] at hi_hb
      exact hi_hb
    exact hcl0.of_keepsFrozen hkf

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
