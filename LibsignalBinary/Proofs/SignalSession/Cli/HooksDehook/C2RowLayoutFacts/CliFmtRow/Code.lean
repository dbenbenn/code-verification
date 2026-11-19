/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
import ProofLib.Process.FastParse
import ProofLib.ProgramReflection

/-!
# `seg[1] ++ seg[2]` `CodeLoaded` & `ElfMaps` Bridges (`CliFmtRow.Code`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open ProofLib.StdStartup (StdBinaryLayout checkSegSlice holdsBytes_of_checkSegSlice)
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (cliElfBytes cliElfImage cliElf_parse libsignalSessionLib patchElfByte patchRegionByte)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (rGetD_map_some_eq_getElem? relocsSorted walkUnrelaxed walkUnrelaxed_isPrefix)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2EmptySeg c2FmtExterns c2FmtProg c2FmtProgTrap c2FmtProg_base c2FmtProg_code c2FmtStubs c2Seg1
   c2Seg1Bytes c2Seg1Start)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsLayout f3LsSymAddrs f3TokenIdx f3TokenPins_ok f3TokenStorageIdx lsInternedMultiLib
   ls_names_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (f3LsMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3PatchedElf_wellFormed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf f3PatchedElf_eq_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree_eq f3TrialRxWordTree_size)

private noncomputable def regionDisjointTokens (seg : Snapshot.Region) : Bool :=
  withForcedNat (Arm64.Process.fastLen512 4096 seg.bytes) fun len =>
    let sAddr := f3LsSymAddrs.getD f3TokenStorageIdx 0#64
    let oAddr := f3LsSymAddrs.getD f3TokenIdx 0#64 + 8#64
    Nat.ble len (sAddr - seg.start).toNat &&
    Nat.ble len (oAddr - seg.start).toNat &&
    Nat.ble len (oAddr + 1#64 - seg.start).toNat &&
    Nat.ble len (oAddr + 2#64 - seg.start).toNat &&
    Nat.ble len (oAddr + 3#64 - seg.start).toNat

set_option maxHeartbeats 2000000 in
private theorem roSeg_disj_chk :
    (match ProofLib.Placed.Split.rGetD (cliElfImage.segments.map some)
        f3StdLayout.roSegIdx none with
     | none => false
     | some seg => regionDisjointTokens seg) = true := by
  rfl_kernel

set_option maxHeartbeats 2000000 in
private theorem c2Seg1_geom_chk :
    (match ProofLib.Placed.Split.rGetD (cliElfImage.segments.map some) 1 none with
     | none => false
     | some seg =>
       withForcedNat (Arm64.Process.fastLen512 4096 seg.bytes) fun segLen =>
         regionDisjointTokens seg &&
         decide (seg.perm.rwx = Perm.rx) &&
         Nat.beq (seg.start.toNat % 4) 0 &&
         Nat.beq (segLen % 4) 0 &&
         Nat.beq (seg.start.toNat + segLen) f3RxSegBase.toNat &&
         Nat.ble (seg.start.toNat + segLen + 4 * f3RxWordCount) (2 ^ 64)) = true := by
  rfl_kernel

set_option maxHeartbeats 2000000 in
private theorem cliElfImage_segments_rx_spine :
    (match cliElfImage.segments with
     | [s0, _, s2, s3] =>
       !(s0.perm == Perm.rx) &&
       decide (s2.start = f3TrialRxProg.base) &&
       !(s3.perm == Perm.rx)
     | _ => false) = true := by
  rfl_kernel

private theorem c2Seg1_def :
    c2Seg1 = (ProofLib.Placed.Split.rGetD (f3PatchedElf.segments.map some) 1 none).getD c2EmptySeg :=
  rfl
private theorem c2Seg1Start_def : c2Seg1Start = c2Seg1.start := rfl
private theorem c2Seg1Bytes_def : c2Seg1Bytes = c2Seg1.bytes := rfl
private theorem c2Seg1_start_eq : c2Seg1.start = c2Seg1Start := rfl
private theorem c2Seg1_bytes_eq : c2Seg1.bytes = c2Seg1Bytes := rfl

attribute [local irreducible] cliElfImage c2Seg1 c2Seg1Start c2Seg1Bytes
  c2FmtStubs c2FmtProg c2FmtProgTrap

private theorem rxProgram_cliElfImage_eq : f3StdLayout.rxProgram cliElfImage = f3TrialRxProg := by
  unfold f3TrialRxProg
  rfl

attribute [local irreducible] f3TrialRxProg

private theorem f3LsMpl_rho_of_getD {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (hn : lsInternedMultiLib.names.getD idx "" = s) :
    f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
  subst hn
  unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    f3LsLayout Obj.Interned.MultiLayout.toMultiPlacement
  dsimp only [Obj.Interned.Layout.toPlacement, Obj.Interned.MultiLayout.dataLayout]
  rw [Obj.Interned.idxOf_getD ls_names_nodup hlt]

private theorem f3LsMpl_token_addrs :
    f3LsMpl.ρ tokenStorageName = f3LsSymAddrs.getD f3TokenStorageIdx 0#64 ∧
    f3LsMpl.ρ tokenName = f3LsSymAddrs.getD f3TokenIdx 0#64 := by
  have hc := f3TokenPins_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hltT, hnT⟩, _⟩, hltS⟩, hnS⟩, _⟩ := hc
  exact ⟨f3LsMpl_rho_of_getD hltS hnS, f3LsMpl_rho_of_getD hltT hnT⟩

private theorem patchRegionByte_of_le {addr : BitVec 64} {val : BitVec 8} {r : Snapshot.Region}
    (hle : r.bytes.length ≤ (addr - r.start).toNat) :
    patchRegionByte addr val r = r := by
  unfold patchRegionByte
  dsimp only
  simp only [Nat.not_lt.mpr hle, ↓reduceIte]

private theorem f3PatchedElf_seg_eq_of_disjoint {idx : Nat} {seg : Snapshot.Region}
    (hseg : cliElfImage.segments[idx]? = some seg)
    (hdisj : regionDisjointTokens seg = true) :
    f3PatchedElf.segments[idx]? = some seg := by
  unfold regionDisjointTokens at hdisj
  simp only [withForcedNat_eq, Arm64.Process.fastLen512_eq_length,
    Bool.and_eq_true, Nat.ble_eq] at hdisj
  rcases hdisj with ⟨⟨⟨⟨hs, ho0⟩, ho1⟩, ho2⟩, ho3⟩
  unfold f3PatchedElf patchElfTokensPlacedAt patchElfByte
  rw [f3LsMpl_token_addrs.1, f3LsMpl_token_addrs.2]
  dsimp only
  simp only [List.getElem?_map, hseg, Option.map_some,
    patchRegionByte_of_le hs, patchRegionByte_of_le ho0,
    patchRegionByte_of_le ho1, patchRegionByte_of_le ho2,
    patchRegionByte_of_le ho3]

private theorem f3PatchedElf_seg1_eq :
    f3PatchedElf.segments[1]? = cliElfImage.segments[1]? := by
  have h := c2Seg1_geom_chk
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : cliElfImage.segments[1]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [withForcedNat_eq, Bool.and_eq_true] at h
    exact f3PatchedElf_seg_eq_of_disjoint hseg h.1.1.1.1.1

theorem f3PatchedElf_roSeg_eq :
    f3PatchedElf.segments[f3StdLayout.roSegIdx]? =
      cliElfImage.segments[f3StdLayout.roSegIdx]? := by
  have h := roSeg_disj_chk
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : cliElfImage.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    exact f3PatchedElf_seg_eq_of_disjoint hseg h

attribute [local irreducible] f3PatchedElf

theorem f3TrialRxProg_code_len : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

theorem c2Seg1_some_and_geom :
    f3PatchedElf.segments[1]? = some c2Seg1 ∧
    cliElfImage.segments[1]? = some c2Seg1 ∧
    c2Seg1.perm.rwx = Perm.rx ∧
    c2Seg1Start.toNat % 4 = 0 ∧
    c2Seg1Bytes.length % 4 = 0 ∧
    c2Seg1Start.toNat + c2Seg1Bytes.length = f3RxSegBase.toNat ∧
    c2Seg1Start.toNat + c2Seg1Bytes.length + f3TrialRxProg.code.length ≤ 2 ^ 64 := by
  have h := c2Seg1_geom_chk
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : cliElfImage.segments[1]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [withForcedNat_eq, Arm64.Process.fastLen512_eq_length,
      Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, Nat.ble_eq] at h
    rcases h with ⟨⟨⟨⟨⟨hdisj, hperm⟩, hal⟩, hslen⟩, hcontig⟩, hbnd⟩
    have hpseg : f3PatchedElf.segments[1]? = some seg := f3PatchedElf_seg1_eq.trans hseg
    have hEq : c2Seg1 = seg := by
      rw [c2Seg1_def, rGetD_map_some_eq_getElem?, hpseg]
      rfl
    rw [c2Seg1Start_def, c2Seg1Bytes_def, hEq, f3TrialRxProg_code_len]
    exact ⟨hpseg, rfl, hperm, hal, hslen, hcontig, hbnd⟩

@[expose] noncomputable def c2CliSeg1Start : BitVec 64 :=
  ((ProofLib.Placed.Split.rGetD (cliElfImage.segments.map some) 1 none).getD c2EmptySeg).start

theorem c2Seg1Start_eq_cli : c2Seg1Start = c2CliSeg1Start := by
  rw [c2Seg1Start_def, c2Seg1_def]
  unfold c2CliSeg1Start
  rw [rGetD_map_some_eq_getElem?, rGetD_map_some_eq_getElem?, f3PatchedElf_seg1_eq]

private theorem checkSegSlice_self (seg : Snapshot.Region) :
    checkSegSlice seg seg.bytes.length seg.start seg.bytes = true := by
  unfold checkSegSlice
  rw [fastTake_eq_take, fastDrop_eq_drop, Nat.sub_self, List.drop_zero, List.take_length]
  simp

private theorem codeLoaded_of_contiguous_append
    {P1 P2 P : Program} {m : Memory}
    (hbase : P.base = P1.base)
    (hcode : P.code = P1.code ++ P2.code)
    (hcontig : P1.base.toNat + P1.code.length = P2.base.toNat)
    (hbnd : P1.base.toNat + P1.code.length + P2.code.length ≤ 2 ^ 64)
    (h1 : P1.CodeLoaded m) (h2 : P2.CodeLoaded m) :
    P.CodeLoaded m := by
  refine Program.CodeLoaded.intro (hbase ▸ h1.aligned)
    (by rw [hbase, hcode, List.length_append, ← Nat.add_assoc]; exact hbnd) fun i hi => ?_
  have hi' : i < (P1.code ++ P2.code).length := hcode ▸ hi
  rw [List.length_append] at hi'
  have hget : ∀ (c : List (BitVec 8)) (hc : P.code = c) (h : i < c.length),
      P.code[i] = c[i] := by
    rintro _ rfl _; rfl
  rw [hget _ hcode (by rw [List.length_append]; exact hi'), hbase]
  by_cases hi1 : i < P1.code.length
  · rw [List.getElem_append_left hi1]
    exact ⟨h1.byte_eq i hi1, h1.perm_eq i hi1, h1.isLazyFree_eq i hi1⟩
  · have hi2 : i - P1.code.length < P2.code.length := by omega
    rw [List.getElem_append_right (by omega)]
    have haddr : P1.base + BitVec.ofNat 64 i =
        P2.base + BitVec.ofNat 64 (i - P1.code.length) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [haddr]
    exact ⟨h2.byte_eq _ hi2, h2.perm_eq _ hi2, h2.isLazyFree_eq _ hi2⟩

private theorem codeLoaded_prefix_cell
    {P : Program} {code1 code2 : List (BitVec 8)} {m : Memory}
    (hcode : P.code = code1 ++ code2)
    (hL : P.CodeLoaded m) {i : Nat} (hi1 : i < code1.length) :
    m.read8 (P.base + BitVec.ofNat 64 i) = code1[i] ∧
    m.perm (P.base + BitVec.ofNat 64 i) = some Perm.rx ∧
    m.isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
  have hi : i < P.code.length := by rw [hcode, List.length_append]; omega
  have hget : ∀ (c : List (BitVec 8)) (hc : P.code = c) (h : i < c.length),
      P.code[i] = c[i] := by
    rintro _ rfl _; rfl
  have h0 : m.read8 (P.base + BitVec.ofNat 64 i) = P.code[i] ∧
      m.perm (P.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      m.isLazyFree (P.base + BitVec.ofNat 64 i) = false :=
    ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩
  rw [hget _ hcode (by rw [List.length_append]; omega), List.getElem_append_left hi1] at h0
  exact h0

private theorem codeLoaded_suffix_of_append
    {P P2 : Program} {code1 : List (BitVec 8)} {m : Memory}
    (hcode : P.code = code1 ++ P2.code)
    (hal2 : P2.base.toNat % 4 = 0)
    (hcontig : P.base.toNat + code1.length = P2.base.toNat)
    (hbnd : P.base.toNat + code1.length + P2.code.length ≤ 2 ^ 64)
    (hL : P.CodeLoaded m) :
    P2.CodeLoaded m := by
  refine Program.CodeLoaded.intro hal2 (by omega) fun j hj => ?_
  have hi : code1.length + j < P.code.length := by rw [hcode, List.length_append]; omega
  have hget : ∀ (c : List (BitVec 8)) (hc : P.code = c) (h : code1.length + j < c.length),
      P.code[code1.length + j] = c[code1.length + j] := by
    rintro _ rfl _; rfl
  have hLj : m.read8 (P.base + BitVec.ofNat 64 (code1.length + j)) = P.code[code1.length + j] ∧
      m.perm (P.base + BitVec.ofNat 64 (code1.length + j)) = some Perm.rx ∧
      m.isLazyFree (P.base + BitVec.ofNat 64 (code1.length + j)) = false :=
    ⟨hL.byte_eq _ hi, hL.perm_eq _ hi, hL.isLazyFree_eq _ hi⟩
  rw [hget _ hcode (by rw [List.length_append]; omega),
    List.getElem_append_right (Nat.le_add_right _ _)] at hLj
  have hsub : code1.length + j - code1.length = j := Nat.add_sub_cancel_left _ _
  simp only [hsub] at hLj
  have haddr : P.base + BitVec.ofNat 64 (code1.length + j) = P2.base + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rwa [← haddr]

private theorem codeLoaded_of_holdsBytes_rx
    (base : BitVec 64) (bytes : List (BitVec 8))
    (stubs : List (String × Nat)) (externs : String → Option (State → State))
    {m : Memory} (hal : base.toNat % 4 = 0) (hbnd : base.toNat + bytes.length ≤ 2 ^ 64)
    (hhb : HoldsBytes m base bytes (fun _ => Perm.rx)) :
    ({ base := base, code := bytes, symbols := [], stubs := stubs, externs := externs,
       overrides := fun _ => none, svc := Syscall.standard } : Program).CodeLoaded m :=
  Program.CodeLoaded.intro hal hbnd fun i hi => hhb i hi

/-- Under `F3CodeInv`, the contiguous `seg[1] ++ seg[2]` program `c2FmtProg` is `CodeLoaded` in
    unstripped memory `m`. -/
theorem c2FmtProg_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    c2FmtProg.CodeLoaded m := by
  obtain ⟨hseg1, _, hperm1, hal1, _, hcontig, hbnd⟩ := c2Seg1_some_and_geom
  obtain ⟨inputs, sLoad, hload, hkf⟩ := hInv.fromLoad
  rw [f3PatchedElf_eq_of_linkedAt hLs] at hload
  obtain ⟨hhb0, _, _⟩ :=
    holdsBytes_of_checkSegSlice f3PatchedElf_wellFormed hload hseg1 (checkSegSlice_self c2Seg1)
  rw [c2Seg1_start_eq, c2Seg1_bytes_eq] at hhb0
  have hhb_rx : HoldsBytes sLoad.mem c2Seg1Start c2Seg1Bytes (fun _ => Perm.rx) := by
    intro i hi
    have hi0 := hhb0 i hi
    dsimp only at hi0
    rwa [hperm1] at hi0
  have hcl_seg1_0 := codeLoaded_of_holdsBytes_rx c2Seg1Start c2Seg1Bytes
    c2FmtStubs c2FmtExterns hal1 (by omega) hhb_rx
  have hcl_seg1 := hcl_seg1_0.of_keepsFrozen hkf
  exact codeLoaded_of_contiguous_append
    (P1 := { base := c2Seg1Start, code := c2Seg1Bytes, symbols := [], stubs := c2FmtStubs,
             externs := c2FmtExterns, overrides := fun _ => none, svc := Syscall.standard })
    (P2 := f3TrialRxProg) (P := c2FmtProg) c2FmtProg_base c2FmtProg_code
    (by dsimp only; rwa [f3TrialRxProg_base])
    hbnd hcl_seg1 hInv.rxCode

/-- Recover `f3TrialRxProg.CodeLoaded m` from `c2FmtProg.CodeLoaded m` (`seg[2]` suffix). -/
theorem rxCode_of_c2FmtProg_codeLoaded {m : Memory} (hL : c2FmtProg.CodeLoaded m) :
    f3TrialRxProg.CodeLoaded m := by
  obtain ⟨_, _, _, _, _, hcontig, hbnd⟩ := c2Seg1_some_and_geom
  have hal2 : f3TrialRxProg.base.toNat % 4 = 0 := by rw [f3TrialRxProg_base]; decide
  exact codeLoaded_suffix_of_append (P := c2FmtProg) (P2 := f3TrialRxProg) (code1 := c2Seg1Bytes)
    c2FmtProg_code hal2
    (by rw [c2FmtProg_base, f3TrialRxProg_base]; exact hcontig)
    (by rw [c2FmtProg_base]; exact hbnd) hL

/-- Balanced `rGetD` / `rLen` / `rDrop` `seg[1]` block-walk checker. -/
@[expose] noncomputable def checkSeg1BlockWalk
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  match ProofLib.Placed.Split.rGetD (cliElfImage.segments.map some) 1 none with
  | none => false
  | some seg =>
    let blk := (lib.blockLib j).text
    let pl := lib.blockPlacement mpl j
    let len := ProofLib.Placed.Split.rLen blk.code
    let segLen := ProofLib.Placed.Split.rLen seg.bytes
    let off := (pl.base - seg.start).toNat
    decide (seg.perm.rwx = Perm.rx) &&
    Nat.beq (len % 4) 0 &&
    Nat.beq (pl.base.toNat % 4) 0 &&
    Nat.ble (pl.base.toNat + len) (2 ^ 64) &&
    decide (seg.start + BitVec.ofNat 64 off = pl.base) &&
    Nat.ble (off + len) segLen &&
    relocsSorted len 0 blk.relocs &&
    walkUnrelaxed blk pl 0 blk.relocs blk.code (ProofLib.Placed.Split.rDrop off seg.bytes)

/-- Recover `(lib.blockProgram mpl j).CodeLoaded m` from `checkSeg1BlockWalk` and
    `c2FmtProg.CodeLoaded m`. -/
theorem seg1_blockCodeLoaded_of_walk {lib : MultiPlacedLib} {mpl : MultiPlacement} {j : Nat}
    (hchk : checkSeg1BlockWalk lib mpl j = true)
    {m : Memory} (hL : c2FmtProg.CodeLoaded m)
    (hRel : (lib.blockPlacement mpl j).relax = fun _ => false := by rfl)
    (hB2b : (lib.blockPlacement mpl j).b2b = fun _ => false := by rfl)
    (hWeak : (lib.blockPlacement mpl j).undefWeak = fun _ => false := by rfl) :
    (lib.blockProgram mpl j).CodeLoaded m := by
  obtain ⟨_, hsegCli, _, _, _, _, _⟩ := c2Seg1_some_and_geom
  unfold checkSeg1BlockWalk at hchk
  rw [rGetD_map_some_eq_getElem?, hsegCli] at hchk
  dsimp only at hchk
  simp only [ProofLib.Placed.Split.rLen_eq, ProofLib.Placed.Split.rDrop_eq,
    Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, Nat.ble_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨_, halLen⟩, halBase⟩, hnowrap0⟩, hbaseEq⟩, hsliceBounds⟩, hwf⟩, hwalk⟩
  rw [c2Seg1_start_eq] at hbaseEq hsliceBounds hwalk
  rw [c2Seg1_bytes_eq] at hsliceBounds hwalk
  let blk := (lib.blockLib j).text
  let pl := lib.blockPlacement mpl j
  have hplen : (blk.patched pl).length = blk.code.length :=
    CodeBlock.length_patched_of_aligned pl halLen
  have hpre : (blk.patched pl).IsPrefix (c2Seg1Bytes.drop (pl.base - c2Seg1Start).toNat) :=
    walkUnrelaxed_isPrefix hRel hB2b hWeak blk.code _ 0 [] blk.relocs
      rfl rfl halLen rfl (fun _ hx => nomatch hx) hwf hwalk
  let off := (pl.base - c2Seg1Start).toNat
  refine Program.CodeLoaded.intro halBase
    (by change pl.base.toNat + (blk.patched pl).length ≤ 2 ^ 64; rw [hplen]; exact hnowrap0)
    fun k hk => ?_
  change k < (blk.patched pl).length at hk
  have hk_seg1 : off + k < c2Seg1Bytes.length := by
    change off + blk.code.length ≤ c2Seg1Bytes.length at hsliceBounds
    omega
  have hLk :=
    codeLoaded_prefix_cell (P := c2FmtProg) (code1 := c2Seg1Bytes) (code2 := f3TrialRxProg.code)
      c2FmtProg_code hL hk_seg1
  rw [c2FmtProg_base] at hLk
  have hbyte : c2Seg1Bytes[off + k] = (blk.patched pl)[k] := by
    have hd : (c2Seg1Bytes.drop off)[k]'(by rw [List.length_drop]; omega) = (blk.patched pl)[k] :=
      (hpre.getElem hk).symm
    rw [List.getElem_drop] at hd
    exact hd
  have haddr : c2Seg1Start + BitVec.ofNat 64 (off + k) = pl.base + BitVec.ofNat 64 k := by
    change c2Seg1Start + BitVec.ofNat 64 off = pl.base at hbaseEq
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hbaseEq]
  rw [haddr, hbyte] at hLk
  exact hLk

private theorem holdsBytes_rx_of_elfMaps_c2FmtProg {addr : BitVec 64} {bs : List (BitVec 8)}
    (hmaps : ElfMaps cliElfImage addr bs (· == Perm.rx))
    {m : Memory} (hL : c2FmtProg.CodeLoaded m) :
    HoldsBytes m addr bs (fun _ => Perm.rx) := by
  have hspine := cliElfImage_segments_rx_spine
  obtain ⟨_, hseg1_c, _, _, _, _, _⟩ := c2Seg1_some_and_geom
  have hseg2_c := rxProgram_cliElfImage_eq
  rcases hsegs : cliElfImage.segments with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | _⟩⟩⟩⟩ <;>
    rw [hsegs] at hspine <;> try cases hspine
  dsimp only at hspine
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hspine
  rcases hspine with ⟨⟨hs0_nrx, hs2_base⟩, hs3_nrx⟩
  have hs1_eq : s1 = c2Seg1 := by
    rw [hsegs] at hseg1_c
    exact Option.some.inj hseg1_c
  have hs2_bytes : s2.bytes = f3TrialRxProg.code := by
    rw [← hseg2_c]
    unfold StdBinaryLayout.rxProgram
    have hidx : f3StdLayout.rxSegIdx = 2 := rfl
    rw [hidx, hsegs]
    rfl
  have hRx := rxCode_of_c2FmtProg_codeLoaded hL
  unfold ElfMaps at hmaps
  intro k hk
  obtain ⟨p, hcell, hp_rx⟩ := hmaps k hk
  rw [beq_iff_eq] at hp_rx
  subst hp_rx
  rw [hsegs] at hcell
  by_cases h0 : (addr + BitVec.ofNat 64 k - s0.start).toNat < s0.bytes.length
  · rw [Obj.Interned.cellAt_cons_hit h0] at hcell
    injection hcell with hcell'
    have hp0 : s0.perm = Perm.rx := Option.some.inj (Prod.mk.inj hcell').1
    rw [hp0] at hs0_nrx
    cases hs0_nrx
  · rw [Obj.Interned.cellAt_cons_miss (Nat.not_lt.mp h0)] at hcell
    by_cases h1 : (addr + BitVec.ofNat 64 k - s1.start).toNat < s1.bytes.length
    · rw [Obj.Interned.cellAt_cons_hit h1] at hcell
      injection hcell with hcell'
      have hb1 : s1.bytes[(addr + BitVec.ofNat 64 k - s1.start).toNat] = bs[k] :=
        (Prod.mk.inj hcell').2
      have h1' : (addr + BitVec.ofNat 64 k - c2Seg1Start).toNat < c2Seg1Bytes.length := by
        simpa only [hs1_eq, c2Seg1_start_eq, c2Seg1_bytes_eq] using h1
      have hb1' : c2Seg1Bytes[(addr + BitVec.ofNat 64 k - c2Seg1Start).toNat] = bs[k] := by
        simpa only [hs1_eq, c2Seg1_start_eq, c2Seg1_bytes_eq] using hb1
      have hLa :=
        codeLoaded_prefix_cell (P := c2FmtProg) (code1 := c2Seg1Bytes) (code2 := f3TrialRxProg.code)
          c2FmtProg_code hL h1'
      rw [c2FmtProg_base] at hLa
      have ha_eq : c2Seg1Start + BitVec.ofNat 64 (addr + BitVec.ofNat 64 k - c2Seg1Start).toNat =
          addr + BitVec.ofNat 64 k := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        bv_omega
      rw [ha_eq, hb1'] at hLa
      exact hLa
    · rw [Obj.Interned.cellAt_cons_miss (Nat.not_lt.mp h1)] at hcell
      by_cases h2 : (addr + BitVec.ofNat 64 k - s2.start).toNat < s2.bytes.length
      · rw [Obj.Interned.cellAt_cons_hit h2] at hcell
        injection hcell with hcell'
        have hb2 : s2.bytes[(addr + BitVec.ofNat 64 k - s2.start).toNat] = bs[k] :=
          (Prod.mk.inj hcell').2
        let off2 := (addr + BitVec.ofNat 64 k - f3TrialRxProg.base).toNat
        have hoff2_lt : off2 < f3TrialRxProg.code.length := by
          dsimp only [off2]
          rwa [← hs2_base, ← hs2_bytes]
        have hRx_a : m.read8 (f3TrialRxProg.base + BitVec.ofNat 64 off2) =
              f3TrialRxProg.code[off2] ∧
            m.perm (f3TrialRxProg.base + BitVec.ofNat 64 off2) = some Perm.rx ∧
            m.isLazyFree (f3TrialRxProg.base + BitVec.ofNat 64 off2) = false :=
          ⟨hRx.byte_eq _ hoff2_lt, hRx.perm_eq _ hoff2_lt, hRx.isLazyFree_eq _ hoff2_lt⟩
        have ha_eq : f3TrialRxProg.base + BitVec.ofNat 64 off2 = addr + BitVec.ofNat 64 k := by
          dsimp only [off2]
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          bv_omega
        have hb2' : f3TrialRxProg.code[off2] = bs[k] := by
          have : (addr + BitVec.ofNat 64 k - s2.start).toNat = off2 := by rw [hs2_base]
          simpa [hs2_bytes, this] using hb2
        rw [ha_eq, hb2'] at hRx_a
        exact hRx_a
      · rw [Obj.Interned.cellAt_cons_miss (Nat.not_lt.mp h2)] at hcell
        by_cases h3 : (addr + BitVec.ofNat 64 k - s3.start).toNat < s3.bytes.length
        · rw [Obj.Interned.cellAt_cons_hit h3] at hcell
          injection hcell with hcell'
          have hp3 : s3.perm = Perm.rx := Option.some.inj (Prod.mk.inj hcell').1
          rw [hp3] at hs3_nrx
          cases hs3_nrx
        · rw [Obj.Interned.cellAt_cons_miss (Nat.not_lt.mp h3)] at hcell
          cases hcell

private theorem except_ok_inj {ε α : Type} {x y : α}
    (h : (Except.ok x : Except ε α) = Except.ok y) : x = y := by
  cases h
  rfl

/-- Every block of `libsignalSessionLib` is `CodeLoaded` in `m` whenever `c2FmtProg.CodeLoaded m`
    holds (proved algebraically from `LinkedAt cliElfBytes`, with zero per-block unfolding). -/
theorem ls_codeLoaded_of_c2FmtProg {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {m : Memory} (hL : c2FmtProg.CodeLoaded m) :
    libsignalSessionLib.CodeLoaded mpl m := by
  obtain ⟨img, hparse, hpl, hin⟩ := hLs
  have himg : img = cliElfImage := except_ok_inj (hparse.symm.trans cliElf_parse)
  rw [himg] at hin
  intro j hj
  have ht := (libsignalSessionLib.placeable_blockLib hj hpl).text
  let pl := libsignalSessionLib.blockPlacement mpl j
  let blk := (libsignalSessionLib.blockLib j).text
  have hlen : (blk.patched pl).length = blk.code.length :=
    CodeBlock.length_patched_of_aligned pl ht.len_aligned
  have hal : pl.base.toNat % 4 = 0 := by
    have h1 : 4 ∣ blk.align := Nat.dvd_of_mod_eq_zero ht.align_pos.2
    have h2 : blk.align ∣ pl.base.toNat := Nat.dvd_of_mod_eq_zero ht.base_aligned
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 h2)
  have hmaps : ElfMaps cliElfImage pl.base (blk.patched pl) (· == Perm.rx) := by
    simpa [blk, pl, libsignalSessionLib.blockLib_text hj, MultiPlacedLib.blockPlacement] using
      hin.blocks j hj
  have hhb := holdsBytes_rx_of_elfMaps_c2FmtProg hmaps hL
  exact Program.CodeLoaded.intro hal
    (by change pl.base.toNat + (blk.patched pl).length ≤ 2 ^ 64; rw [hlen]; exact ht.no_wrap)
    hhb

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code
