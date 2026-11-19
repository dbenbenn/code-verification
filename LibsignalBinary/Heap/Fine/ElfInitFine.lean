/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Loader
public import Arm64.Trusted.Process.Placed
public import ProofLib.Placed.Multi
public import ProofLib.StdStartup.StackInit
public import LibsignalBinary.Heap.Fine.CostModel
public import LibsignalBinary.Heap.Fine.Init
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.InitStack
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslStart
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# ELF Startup Bridge to `fineCostModel`

Bridges initial ELF memory (`ElfImage.loadState` on `cliProcessInputs` and
`musl` `_start → main` startup) to `MallocngInitResources` / `MallocngInitResourcesRo` and `mallocngBudgetPool_of_init`,
producing the initial `fineCostModel` budget pool token at `main` entry parametrically over
`CliElfMallocngLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.Process
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open LibsignalBinary.Heap
open CryptoVerification.SignalSession (Inputs cliProcessInputs processInputs)

/-! ## Static Intervals, `MallocngBrkStartWf`, and `StartupVmPreserved` -/

/-- Static virtual-memory interval list covering the initial user stack
    `[stackTop - stackSize, stackTop)` and every `PT_LOAD` segment of `elf`. -/
def elfStaticIvs (elf : ElfImage) (inputs : ProcessInputs) : List (BitVec 64 × Nat) :=
  (BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize), inputs.init.stackSize) ::
    elf.segments.map (fun r => (r.start, r.bytes.length))

/-- Specialization of `elfStaticIvs` to the CLI's 8 MiB stack (`cliProcessInputs`). -/
def cliElfStaticIvs (elf : ElfImage) : List (BitVec 64 × Nat) :=
  (BitVec.ofNat 64 CryptoVerification.SignalSession.InitStack.stackBase,
    CryptoVerification.SignalSession.InitStack.cliStackSize) ::
    elf.segments.map (fun r => (r.start, r.bytes.length))

theorem elfStaticIvs_cliProcessInputs (elf : ElfImage) (i : Inputs) :
    elfStaticIvs elf (cliProcessInputs i) = cliElfStaticIvs elf := rfl

theorem elfStaticIvs_length (elf : ElfImage) (inputs : ProcessInputs) :
    (elfStaticIvs elf inputs).length = elf.segments.length + 1 := by
  simp [elfStaticIvs]

theorem elfStaticIvs_sum (elf : ElfImage) (inputs : ProcessInputs) :
    ((elfStaticIvs elf inputs).map Prod.snd).sum =
      inputs.init.stackSize + (elf.segments.map (fun r => r.bytes.length)).sum := by
  simp [elfStaticIvs, List.map_map, Function.comp_def]

/-- Derive `MMAP_MIN_ADDR ≤ elf.brkStart.toNat` from any `PT_LOAD` segment `r ∈ elf.segments`
    placed at or above `MMAP_MIN_ADDR` (`65536`). -/
theorem brkStart_min_of_segment {elf : ElfImage}
    (hwf : elf.WellFormed = true) {r : Snapshot.Region}
    (hr : r ∈ elf.segments) (hrMin : MMAP_MIN_ADDR ≤ r.start.toNat) :
    MMAP_MIN_ADDR ≤ elf.brkStart.toNat := by
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have hseg := hwf.2 r hr
  omega

/-- Any `WellFormed` `ElfImage` with `MMAP_MIN_ADDR ≤ elf.brkStart.toNat ≤ 2 ^ 48` satisfies
    `MallocngBrkStartWf elf.brkStart`. -/
theorem mallocngBrkStartWf_of_elf {elf : ElfImage}
    (hwf : elf.WellFormed = true)
    (hmin : MMAP_MIN_ADDR ≤ elf.brkStart.toNat)
    (hhi : elf.brkStart.toNat ≤ 2 ^ 48) :
    MallocngBrkStartWf elf.brkStart := by
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true, beq_iff_eq] at hwf
  have hmod : elf.brkStart.toNat % PAGE_SIZE = 0 := hwf.1.2
  exact ⟨hmin, hmod, hhi⟩

/-- Startup virtual/physical memory preservation from ELF `loadState` `s0` to `main` entry `sm`:
    preserves `brkStart`, `brk`, `physMemAvail`, and `mem.perm`, while allowing `_start` /
    `__init_tp` to initialize `tpidrEl0` from `0` to `tp`. -/
def StartupVmPreserved (s0 sm : State) : Prop :=
  sm.brkStart = s0.brkStart ∧
  sm.brk = s0.brk ∧
  sm.physMemAvail = s0.physMemAvail ∧
  ∀ a : BitVec 64, sm.mem.perm a = s0.mem.perm a

theorem mallocngBudgetPoolInv_of_startupVmPreserved {lim : BudgetLimits}
    {staticIvs ivs : List (BitVec 64 × Nat)} {s0 sm : State}
    (hvm : StartupVmPreserved s0 sm)
    (hInv : mallocngBudgetPoolInv lim staticIvs ivs s0) :
    mallocngBudgetPoolInv lim staticIvs ivs sm := by
  rcases hvm with ⟨_, _, hphys, hperm⟩
  have hpprw : physPlusRw sm = physPlusRw s0 := by
    unfold physPlusRw
    rw [hphys, rwBytes_congr hperm]
  unfold mallocngBudgetPoolInv StaticMappedCover at *
  intro henf
  obtain ⟨⟨hcnt, hsum, hva, hcov⟩, hcap⟩ := hInv henf
  refine ⟨⟨hcnt, hsum, hva, fun a hmap => ?_⟩, ?_⟩
  · rw [hperm a] at hmap
    exact hcov a hmap
  · rwa [hpprw]

/-! ## `ElfImage.loadState` Mapped-Interval Cover -/

/-- Decompose a successful `ElfImage.loadState` into `WellFormed`, initial `brk`/`physMemAvail`
    fields, and `buildInitialStack`. -/
theorem elfLoadState_fields {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0) :
    elf.WellFormed = true ∧
    s0.brkStart = elf.brkStart ∧
    s0.brk = elf.brkStart ∧
    s0.physMemAvail = inputs.init.physMemAvail ∧
    ∃ sp stackRegion,
      buildInitialStack elf inputs = .ok (sp, stackRegion) ∧
      s0.sp = sp ∧
      s0.mem =
        (⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩ : Memory).mapZero
          (BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize))
          inputs.init.stackSize := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at hload
  split at hload
  · contradiction
  rename_i hwfNot
  have hwf : elf.WellFormed = true := by simpa using hwfNot
  split at hload
  · contradiction
  split at hload
  · contradiction
  generalize hb : buildInitialStack elf inputs = r at hload
  cases r with
  | error _ => contradiction
  | ok pair =>
    rcases pair with ⟨sp, stackRegion⟩
    cases hload
    exact ⟨hwf, rfl, rfl, rfl, sp, stackRegion, rfl, rfl, rfl⟩

private theorem do_if_err_ok {α ε : Type} {rest : Unit → Except ε α}
    {p : Prop} [Decidable p] {e : ε} {y : α}
    (h : (have __do_jp := rest;
          if p then Bind.bind (Except.error e) __do_jp else __do_jp ()) = Except.ok y) :
    ¬ p ∧ rest () = Except.ok y := by
  change (if p then Bind.bind (Except.error e) rest else rest ()) = Except.ok y at h
  by_cases hp : p
  · simp only [hp, ↓reduceIte, Bind.bind, Except.bind] at h; cases h
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩

private theorem flatMap_cstr_length (strs : List (List (BitVec 8))) :
    (strs.flatMap (· ++ [0#8])).length = (strs.map fun s => s.length + 1).sum := by
  induction strs with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_singleton,
      List.map_cons, List.sum_cons, ih]

private theorem foldl_len_eq_sum (strs : List (List (BitVec 8))) (acc : Nat) :
    strs.foldl (fun n s => n + s.length + 1) acc = acc + (strs.map fun s => s.length + 1).sum := by
  induction strs generalizing acc with
  | nil => simp
  | cons s tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

private theorem le_alignUp16 (n : Nat) : n ≤ alignUp16 n := by
  unfold alignUp16
  omega

/-- Every byte in the populated frame `stackRegion` produced by `buildInitialStack` lies within the
    user stack interval `[stackTop - stackSize, stackTop)` of length `inputs.init.stackSize`, and
    `elf.brkStart.toNat ≤ stackTop - stackSize`. -/
theorem buildInitialStack_sub_stack {elf : ElfImage} {inputs : ProcessInputs}
    {sp : BitVec 64} {stackRegion : Snapshot.Region}
    (hb : buildInitialStack elf inputs = .ok (sp, stackRegion))
    (htopLt : inputs.init.stackTop.toNat < 2 ^ 64) :
    elf.brkStart.toNat ≤ inputs.init.stackTop.toNat - inputs.init.stackSize ∧
    ∀ a : BitVec 64, (a - stackRegion.start).toNat < stackRegion.bytes.length →
      (a - BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)).toNat <
        inputs.init.stackSize := by
  unfold buildInitialStack at hb
  rcases do_if_err_ok hb with ⟨hrandNot, hb⟩
  have hrand : inputs.init.auxv.randomBytes.length = 16 := by simpa using hrandNot
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨hszLeTopNot, hb⟩
  rcases do_if_err_ok hb with ⟨hbrkNot, hb⟩
  rcases do_if_err_ok hb with ⟨hinfoLeNot, hb⟩
  simp only [ProofLib.StdStartup.packCStringList_spec] at hb
  rcases do_if_err_ok hb with ⟨htotLeNot, hb⟩
  change Except.ok _ = Except.ok (sp, stackRegion) at hb
  injection hb with hEq
  injection hEq with hspEq hsrEq
  have hbrkLe : elf.brkStart.toNat ≤ inputs.init.stackTop.toNat - inputs.init.stackSize := by
    change ¬ elf.brkStart.toNat > inputs.init.stackTop.toNat - inputs.init.stackSize at hbrkNot
    omega
  have hszLeTop : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
    change ¬ inputs.init.stackSize > inputs.init.stackTop.toNat at hszLeTopNot
    omega
  refine ⟨hbrkLe, fun a ha => ?_⟩
  have hstartEq (s : BitVec 64) (p : Perm) (bs : List (BitVec 8)) :
      ({ start := s, perm := p, bytes := bs } : Snapshot.Region).start = s := rfl
  have hbytesEq (s : BitVec 64) (p : Perm) (bs : List (BitVec 8)) :
      ({ start := s, perm := p, bytes := bs } : Snapshot.Region).bytes = bs := rfl
  rw [← hsrEq, hstartEq, hbytesEq] at ha
  clear hspEq hsrEq hb hbrkNot hszLeTopNot
  revert htotLeNot ha
  generalize List.flatMap (Obj.bytesLE 8) _ = tableBytes
  intro htotLe ha
  have hargvLen := flatMap_cstr_length inputs.argv
  have henvpLen := flatMap_cstr_length inputs.envp
  let upperRawLen :=
    8 + (inputs.argv.map fun s => s.length + 1).sum +
      (inputs.envp.map fun s => s.length + 1).sum + (inputs.execfn.length + 1) + 8
  have hfoldArgv :
      inputs.argv.foldl (fun n s => n + s.length + 1) 0 =
        (inputs.argv.map fun s => s.length + 1).sum := by
    rw [foldl_len_eq_sum inputs.argv 0, Nat.zero_add]
  have hfoldEnvp :
      inputs.envp.foldl (fun n s => n + s.length + 1) 0 =
        (inputs.envp.map fun s => s.length + 1).sum := by
    rw [foldl_len_eq_sum inputs.envp 0, Nat.zero_add]
  have hleAlign : upperRawLen ≤ alignUp16 upperRawLen :=
    le_alignUp16 upperRawLen
  let infoLen := 16 + alignUp16 upperRawLen
  simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate,
    Nat.zero_add, Nat.reduceAdd, hrand, hargvLen, henvpLen, hfoldArgv, hfoldEnvp] at hinfoLeNot htotLe ha
  clear hrandNot
  set tblLen := tableBytes.length
  dsimp only [infoLen, upperRawLen] at hleAlign ⊢
  have hinfoLe : infoLen ≤ inputs.init.stackSize := by
    dsimp only [infoLen, upperRawLen]
    omega
  have htotLe' : tblLen + infoLen ≤ inputs.init.stackSize := by
    dsimp only [infoLen, upperRawLen]
    omega
  have ha' :
      (a - BitVec.ofNat 64 (inputs.init.stackTop.toNat - infoLen - tblLen)).toNat <
        tblLen + infoLen := by
    dsimp only [infoLen, upperRawLen]
    omega
  set spNat := inputs.init.stackTop.toNat - infoLen - tblLen
  set stackBase := inputs.init.stackTop.toNat - inputs.init.stackSize
  have hspGeSb : stackBase ≤ spNat := by omega
  have hspTop : spNat + (tblLen + infoLen) = inputs.init.stackTop.toNat := by omega
  have hspLt : spNat < 2 ^ 64 := by omega
  have hsbLt : stackBase < 2 ^ 64 := by omega
  have hspToNat : (BitVec.ofNat 64 spNat).toNat = spNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspLt]
  have hsbToNat : (BitVec.ofNat 64 stackBase).toNat = stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsbLt]
  have haBounds : spNat ≤ a.toNat ∧ a.toNat < inputs.init.stackTop.toNat := by
    have ha64 := a.isLt
    rw [BitVec.toNat_sub, hspToNat] at ha'
    by_cases hge : spNat ≤ a.toNat
    · have hmod : (2 ^ 64 - spNat + a.toNat) % 2 ^ 64 = a.toNat - spNat := by
        have h1 : 2 ^ 64 - spNat + a.toNat = 2 ^ 64 + (a.toNat - spNat) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at ha'
      exact ⟨hge, by omega⟩
    · exfalso
      have hmod : (2 ^ 64 - spNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - spNat + a.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hmod] at ha'
      omega
  rw [BitVec.toNat_sub, hsbToNat]
  have hmodSb : (2 ^ 64 - stackBase + a.toNat) % 2 ^ 64 = a.toNat - stackBase := by
    have h1 : 2 ^ 64 - stackBase + a.toNat = 2 ^ 64 + (a.toNat - stackBase) := by omega
    have ha64 := a.isLt
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hmodSb]
  omega

/-- Every mapped byte of `elf.loadState inputs = .ok s0` (with `stackTop < 2 ^ 64`) lies in
    `elfStaticIvs elf inputs`. -/
theorem elfLoadState_mapped_in_staticIvs {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0)
    (htopLt : inputs.init.stackTop.toNat < 2 ^ 64)
    (a : BitVec 64) (hmap : (s0.mem.perm a).mapped = true) :
    MallocngInIntervals (elfStaticIvs elf inputs) a := by
  obtain ⟨_, _, _, _, sp, stackRegion, hb, _, hmem⟩ := elfLoadState_fields hload
  obtain ⟨_, hsub⟩ := buildInitialStack_sub_stack hb htopLt
  rw [hmem] at hmap
  set sb := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  set baseMem : Memory := ⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩
  by_cases hstk : (a - sb).toNat < inputs.init.stackSize
  · exact ⟨(sb, inputs.init.stackSize), List.Mem.head _, hstk⟩
  · have hbase : (baseMem.perm a).mapped = true := by
      unfold Memory.perm Memory.mapZero at hmap
      simp only [hstk, decide_false, Bool.false_and] at hmap
      exact hmap
    have hcellSome : Snapshot.loadCellAt (elf.segments ++ [stackRegion]) a ≠ none := by
      intro hnone
      dsimp only [baseMem, Memory.perm] at hbase
      rw [hnone] at hbase
      cases hbase
    unfold Snapshot.loadCellAt at hcellSome
    have hex : ∃ r ∈ elf.segments ++ [stackRegion], (a - r.start).toNat < r.bytes.length := by
      refine Classical.byContradiction fun hall => hcellSome ?_
      rw [List.findSome?_eq_none_iff]
      intro r hr
      dsimp only
      split
      · rename_i hlt
        exact False.elim (hall ⟨r, hr, hlt⟩)
      · rfl
    rcases hex with ⟨r, hr, hlt⟩
    rcases List.mem_append.mp hr with hrSeg | hrStk
    · exact ⟨(r.start, r.bytes.length),
        List.Mem.tail _ (List.mem_map.mpr ⟨r, hrSeg, rfl⟩), hlt⟩
    · rw [List.mem_singleton] at hrStk
      subst hrStk
      exact ⟨(sb, inputs.init.stackSize), List.Mem.head _, hsub a hlt⟩

private theorem buildInitialStack_stackSize_le {elf : ElfImage} {inputs : ProcessInputs}
    {sp : BitVec 64} {stackRegion : Snapshot.Region}
    (hb : buildInitialStack elf inputs = .ok (sp, stackRegion)) :
    inputs.init.stackSize ≤ inputs.init.stackTop.toNat := by
  unfold buildInitialStack at hb
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨_, hb⟩
  rcases do_if_err_ok hb with ⟨hszLeTopNot, _⟩
  change ¬ inputs.init.stackSize > inputs.init.stackTop.toNat at hszLeTopNot
  omega

/-- `mallocngBudgetPoolInv` holds on any `ElfImage.loadState` output whose static interval count,
    static byte sum, and physical memory cap fit `lim`. -/
theorem elfLoadState_poolInv {elf : ElfImage} {inputs : ProcessInputs}
    {lim : BudgetLimits} {s0 : State}
    (hload : elf.loadState inputs = .ok s0)
    (htopLe : inputs.init.stackTop.toNat ≤ Arm64.USER_VA_LIMIT)
    (hcnt : lim.enforced = true → elf.segments.length + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true →
      inputs.init.stackSize + (elf.segments.map (fun r => r.bytes.length)).sum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ inputs.init.physMemAvail) :
    mallocngBudgetPoolInv lim (elfStaticIvs elf inputs) [] s0 := by
  obtain ⟨hwf, _, _, havail, _, _, hb, _, _⟩ := elfLoadState_fields hload
  have hLim : Arm64.USER_VA_LIMIT = 2 ^ 48 := rfl
  have htopLt : inputs.init.stackTop.toNat < 2 ^ 64 := by omega
  obtain ⟨hbrkLe, _⟩ := buildInitialStack_sub_stack hb htopLt
  have hszLe := buildInitialStack_stackSize_le hb
  intro henf
  refine ⟨⟨?_, ?_, ?_, fun a hmap => Or.inl (elfLoadState_mapped_in_staticIvs hload htopLt a hmap)⟩, ?_⟩
  · rw [elfStaticIvs_length]
    exact hcnt henf
  · rw [elfStaticIvs_sum]
    exact hbytes henf
  · intro iv hiv
    simp only [elfStaticIvs, List.mem_cons, List.mem_map] at hiv
    rcases hiv with rfl | ⟨r, hr, rfl⟩
    · dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    · dsimp only
      unfold ElfImage.WellFormed at hwf
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
      have hseg := hwf.2 r hr
      omega
  · unfold physPlusRw
    have h1 := hphys henf
    omega

/-! ## Linux Auxiliary Vector (`MallocngAuxvAt`) -/

/-! ## `CliElfMallocngLayout`, `MallocngInitResources`, and Pool Initialization -/

/-- Parametric ELF layout and budget-fit hypotheses (`brkStart`, segment count, and segment byte
    sum) for `cliProcessInputs` (`1 GiB` physical RAM cap, `8 MiB` stack). -/
structure CliElfMallocngLayout (elf : ElfImage) (lim : BudgetLimits) : Prop where
  brkStart_min : MMAP_MIN_ADDR ≤ elf.brkStart.toNat
  staticCount_le : lim.enforced = true → elf.segments.length + 1 ≤ lim.staticCount
  staticBytes_le :
    lim.enforced = true →
      CryptoVerification.SignalSession.InitStack.cliStackSize +
        (elf.segments.map (fun r => r.bytes.length)).sum ≤ lim.staticBytes
  physCap_le : lim.enforced = true → lim.physCap ≤ 2 ^ 30

/-- Construct `CliElfMallocngLayout` from any `PT_LOAD` segment `r ∈ elf.segments` placed at or
    above `MMAP_MIN_ADDR` (`65536`). -/
theorem CliElfMallocngLayout.of_segment {elf : ElfImage} {lim : BudgetLimits}
    (hwf : elf.WellFormed = true) {r : Snapshot.Region}
    (hr : r ∈ elf.segments) (hrMin : MMAP_MIN_ADDR ≤ r.start.toNat)
    (hcnt : lim.enforced = true → elf.segments.length + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true →
      CryptoVerification.SignalSession.InitStack.cliStackSize +
        (elf.segments.map (fun r => r.bytes.length)).sum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30) :
    CliElfMallocngLayout elf lim where
  brkStart_min := brkStart_min_of_segment hwf hr hrMin
  staticCount_le := hcnt
  staticBytes_le := hbytes
  physCap_le := hphys

/-- Bundled post-`__init_libc` / `main`-entry `mallocng` initialization resources and VM budget
    invariants at state `s0`, placement `mpl`, budget limits `lim`, static interval cover
    `staticIvs`, and caller frame `R`. -/
structure MallocngInitResources
    (mpl : Obj.MultiPlacement) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State) : Prop where
  tp_lo : 0xa4 ≤ s0.tpidrEl0.toNat
  tp_hi : s0.tpidrEl0.toNat ≤ 2 ^ 48
  brk_eq : s0.brk = s0.brkStart
  brkStart_wf : MallocngBrkStartWf s0.brkStart
  poolInv : mallocngBudgetPoolInv lim staticIvs [] s0
  startup :
    ∃ auxvPtr : BitVec 64,
      s0.mem ⊨
        VerifiedLibraries.mallocngLib.dataInit mpl ∗
          MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
          (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr ∗ R

/-- Assemble `MallocngInitResources` at `main` entry (or any post-startup state satisfying
    `StartupVmPreserved sLoad s0`) from `elf.loadState (cliProcessInputs i) = .ok sLoad` and
    `CliElfMallocngLayout elf lim`. -/
theorem cliElf_mallocngInitResources
    {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    MallocngInitResources mpl lim (cliElfStaticIvs elf) R s0 := by
  obtain ⟨hwf, hbsLoad, hbrkLoad, _, _, _, hb, _, _⟩ := elfLoadState_fields hLoad
  have hinit : (cliProcessInputs i).init = { auxv := { hwcap := 0x1b#64 }, stackSize := 8388608 } := rfl
  have htopLt : (cliProcessInputs i).init.stackTop.toNat < 2 ^ 64 := by
    rw [hinit]; decide
  have htopLe : (cliProcessInputs i).init.stackTop.toNat ≤ Arm64.USER_VA_LIMIT := by
    rw [hinit]; decide
  obtain ⟨hbrkLeSb, _⟩ := buildInitialStack_sub_stack hb htopLt
  have hsbLe48 :
      (cliProcessInputs i).init.stackTop.toNat - (cliProcessInputs i).init.stackSize ≤ 2 ^ 48 := by
    rw [hinit]; decide
  have hBrkWfElf : MallocngBrkStartWf elf.brkStart :=
    mallocngBrkStartWf_of_elf hwf hLayout.brkStart_min (Nat.le_trans hbrkLeSb hsbLe48)
  have hInvLoad : mallocngBudgetPoolInv lim (cliElfStaticIvs elf) [] sLoad := by
    rw [← elfStaticIvs_cliProcessInputs elf i]
    exact elfLoadState_poolInv hLoad htopLe hLayout.staticCount_le hLayout.staticBytes_le
      hLayout.physCap_le
  have hbs0 : s0.brkStart = elf.brkStart := hVm.1.trans hbsLoad
  have hbrk0 : s0.brk = s0.brkStart := (hVm.2.1.trans hbrkLoad).trans hbs0.symm
  refine
    { tp_lo := htpLo
      tp_hi := htpHi
      brk_eq := hbrk0
      brkStart_wf := hbs0 ▸ hBrkWfElf
      poolInv := mallocngBudgetPoolInv_of_startupVmPreserved hVm hInvLoad
      startup := ⟨auxvPtr, hmem⟩ }

/-- Eliminate `MallocngInitResources` via `mallocngBudgetPool_of_init fineCostModelSound` into the
    initial `fineCostModel` budget pool token `(fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart).pool lim fineCostModel.init s0`. -/
theorem fineBudgetPool_of_initResources
    {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {staticIvs : List (BitVec 64 × Nat)} {R : SepProp} {s0 : State}
    (hInit : MallocngInitResources mpl lim staticIvs R s0) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R := by
  obtain ⟨auxvPtr, hmem⟩ := hInit.startup
  exact mallocngBudgetPool_of_init fineCostModelSound
    hInit.tp_lo hInit.tp_hi hInit.brk_eq hInit.brkStart_wf hInit.poolInv hmem

/-- Produce the initial `A.pool lim fineCostModel.init s0` token at `main` entry from
    `cliElf_mallocngInitResources` and `mallocngBudgetPool_of_init fineCostModelSound`. -/
theorem cliElf_fineBudgetPool_of_init
    {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R :=
  fineBudgetPool_of_initResources
    (cliElf_mallocngInitResources hLayout hLoad hVm htpLo htpHi hmem)

/-- Combined `main`-entry initializer pairing `cliElf_fineBudgetPool_of_init` with
    `RustCliAllocBudgetEntries fineCostModel A P thunkAddrs` (`__rust_{alloc,dealloc,realloc}`
    1-instruction `B`-thunks). -/
theorem cliElf_fineBudgetPool_and_entries_of_init
    {P : Program} {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hP : ProgContainsMallocng P mpl)
    (hThunks : VerifiedLibraries.RustStd.RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : VerifiedLibraries.RustStd.RustStdRdlShimCode P rdlAddrs.toRustStd
      (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs := by
  obtain ⟨γ, hPool⟩ :=
    cliElf_fineBudgetPool_of_init hLayout hLoad hVm htpLo htpHi hmem
  exact ⟨γ, hPool,
    fineRustCliAllocBudgetEntries_thunks hP γ s0.tpidrEl0 s0.brkStart hThunks hShims hMemcpy⟩

/-! ## Read-Only (`auxv`) Startup Initialization (`*_ro`) -/

/-- Read-only-`auxv` counterpart of `MallocngInitResources`: takes already-frozen
    `(((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr`
    so callers can duplicate `.ro` `auxv` access (e.g. for `getauxval` CPU probes) in `R`. -/
structure MallocngInitResourcesRo
    (mpl : Obj.MultiPlacement) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State) : Prop where
  tp_lo : 0xa4 ≤ s0.tpidrEl0.toNat
  tp_hi : s0.tpidrEl0.toNat ≤ 2 ^ 48
  brk_eq : s0.brk = s0.brkStart
  brkStart_wf : MallocngBrkStartWf s0.brkStart
  poolInv : mallocngBudgetPoolInv lim staticIvs [] s0
  startup :
    ∃ auxvPtr : BitVec 64,
      s0.mem ⊨
        VerifiedLibraries.mallocngLib.dataInit mpl ∗
          MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
          (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
          MallocngAuxvRoAt auxvPtr ∗ R

/-- Assemble `MallocngInitResourcesRo` at `main` entry (or any post-startup state satisfying
    `StartupVmPreserved sLoad s0`) from already-frozen `.ro` `__libc.auxv` and `MallocngAuxvRoAt`. -/
theorem cliElf_mallocngInitResources_ro
    {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
        MallocngAuxvRoAt auxvPtr ∗ R) :
    MallocngInitResourcesRo mpl lim (cliElfStaticIvs elf) R s0 := by
  obtain ⟨hwf, hbsLoad, hbrkLoad, _, _, _, hb, _, _⟩ := elfLoadState_fields hLoad
  have hinit : (cliProcessInputs i).init = { auxv := { hwcap := 0x1b#64 }, stackSize := 8388608 } := rfl
  have htopLt : (cliProcessInputs i).init.stackTop.toNat < 2 ^ 64 := by
    rw [hinit]; decide
  have htopLe : (cliProcessInputs i).init.stackTop.toNat ≤ Arm64.USER_VA_LIMIT := by
    rw [hinit]; decide
  obtain ⟨hbrkLeSb, _⟩ := buildInitialStack_sub_stack hb htopLt
  have hsbLe48 :
      (cliProcessInputs i).init.stackTop.toNat - (cliProcessInputs i).init.stackSize ≤ 2 ^ 48 := by
    rw [hinit]; decide
  have hBrkWfElf : MallocngBrkStartWf elf.brkStart :=
    mallocngBrkStartWf_of_elf hwf hLayout.brkStart_min (Nat.le_trans hbrkLeSb hsbLe48)
  have hInvLoad : mallocngBudgetPoolInv lim (cliElfStaticIvs elf) [] sLoad := by
    rw [← elfStaticIvs_cliProcessInputs elf i]
    exact elfLoadState_poolInv hLoad htopLe hLayout.staticCount_le hLayout.staticBytes_le
      hLayout.physCap_le
  have hbs0 : s0.brkStart = elf.brkStart := hVm.1.trans hbsLoad
  have hbrk0 : s0.brk = s0.brkStart := (hVm.2.1.trans hbrkLoad).trans hbs0.symm
  refine
    { tp_lo := htpLo
      tp_hi := htpHi
      brk_eq := hbrk0
      brkStart_wf := hbs0 ▸ hBrkWfElf
      poolInv := mallocngBudgetPoolInv_of_startupVmPreserved hVm hInvLoad
      startup := ⟨auxvPtr, hmem⟩ }

/-- Eliminate `MallocngInitResourcesRo` via `fineHeap_init_ro` into the initial `fineCostModel`
    budget pool token `(fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart).pool lim fineCostModel.init s0`. -/
theorem fineBudgetPool_of_initResources_ro
    {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {staticIvs : List (BitVec 64 × Nat)} {R : SepProp} {s0 : State}
    (hInit : MallocngInitResourcesRo mpl lim staticIvs R s0) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R := by
  obtain ⟨auxvPtr, hmem⟩ := hInit.startup
  obtain ⟨γ, hsat1⟩ := fineHeap_init_ro mpl s0.tpidrEl0 s0.brkStart auxvPtr R s0.mem
    hInit.tp_lo hInit.tp_hi hInit.brkStart_wf hmem
  rw [satisfies_bupd] at hsat1
  refine ⟨γ, ?_⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hsat1
  change FineHeapImpl γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart s0.brkStart
      fineCostModel.init [] ⊢
    mallocngBudgetPool fineCostModel fineCostModelIface γ mpl s0.tpidrEl0 s0.brkStart lim
      fineCostModel.init s0
  unfold mallocngBudgetPool mallocngBudgetPoolAt MallocngModelEnv
  rw [hInit.brk_eq]
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun stIvs => ∃∗ ivs : List (BitVec 64 × Nat),
        ⌜mallocngBudgetPoolInv lim stIvs ivs s0⌝ ∗
        (⌜s0.tpidrEl0 = s0.tpidrEl0 ∧ s0.brkStart = s0.brkStart⌝ ∗
          fineCostModelIface.HeapM γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart
            s0.brkStart fineCostModel.init ivs))
      staticIvs)
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List (BitVec 64 × Nat))
      (fun ivs =>
        ⌜mallocngBudgetPoolInv lim staticIvs ivs s0⌝ ∗
        (⌜s0.tpidrEl0 = s0.tpidrEl0 ∧ s0.brkStart = s0.brkStart⌝ ∗
          fineCostModelIface.HeapM γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart
            s0.brkStart fineCostModel.init ivs))
      [])
  exact Entails.pure_right hInit.poolInv
    (Entails.pure_right ⟨rfl, rfl⟩
      (Entails.refl (FineHeapImpl γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart
        s0.brkStart fineCostModel.init [])))

/-- Produce the initial `A.pool lim fineCostModel.init s0` token at `main` entry from already-frozen
    `.ro` `__libc.auxv` and `MallocngAuxvRoAt`. -/
theorem cliElf_fineBudgetPool_of_init_ro
    {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
        MallocngAuxvRoAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R :=
  fineBudgetPool_of_initResources_ro
    (cliElf_mallocngInitResources_ro hLayout hLoad hVm htpLo htpHi hmem)

/-- Combined `main`-entry initializer pairing `cliElf_fineBudgetPool_of_init_ro` with
    `RustCliAllocBudgetEntries fineCostModel A P thunkAddrs` (`__rust_{alloc,dealloc,realloc}`
    1-instruction `B`-thunks). -/
theorem cliElf_fineBudgetPool_and_entries_of_init_ro
    {P : Program} {elf : ElfImage} {mpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hP : ProgContainsMallocng P mpl)
    (hThunks : VerifiedLibraries.RustStd.RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : VerifiedLibraries.RustStd.RustStdRdlShimCode P rdlAddrs.toRustStd
      (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
        MallocngAuxvRoAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs := by
  obtain ⟨γ, hPool⟩ :=
    cliElf_fineBudgetPool_of_init_ro hLayout hLoad hVm htpLo htpHi hmem
  exact ⟨γ, hPool,
    fineRustCliAllocBudgetEntries_thunks hP γ s0.tpidrEl0 s0.brkStart hThunks hShims hMemcpy⟩

end LibsignalBinary.Heap.Fine
