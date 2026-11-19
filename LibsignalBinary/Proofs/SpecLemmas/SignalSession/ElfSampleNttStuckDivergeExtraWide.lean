/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.HookDischarge.Libc.Memset
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Wide-Keep Extra Ghost `StepsStrictAvoid` Engine (`ElfSampleNttStuckDivergeExtraWide`)

Shared untrusted (`Role::Proof`) engine for proving
`StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))`
on `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` across wide-keep `ExtraGhostTable` rows:

1. **`s5Addrs` & `addS5Trap` (`§1`):** installs `.Exception "hit S5"` extern traps at the 5
   `mlkemSampleNttSyms` entrypoints (`s5Addrs`), preserving `svc`, `CodeLoaded`, and all
   non-`s5Addrs` `externAt?` entries whenever `P.externs s5TrapSym = none`.
2. **`f3LoRxProg` & `keepLo` (`§2`):** low `32 KiB` prefix (`f3LoWordCount = 0x2000`) of
   `f3TrialRxProg` covering `memcpy`, `memset`, `mallocng`, and the `seg[2]` Rust allocator
   thunks/shims strictly below `s5Addrs`.
3. **`withExecFrozenBudget`, `nonZeroEquivLim`, & `f3LoRxProg → P` Lifters (`§3`):** lifts
   `memcpy`, `budgetMemcpy`, `memset`, `rustAllocShimVmSpec`, `budgetAllocShimSpec`, and the
   4 `fineHookRustCliAllocBudget` allocator entrypoints (`alloc`, `dealloc`, `realloc`,
   `alloc_zeroed`) onto any `Syscall.standard` program `P` loading `f3LoRxProg` with no externs in
   `keepLo` (including `addS5Trap P_sub`).
4. **Generic `avoidS5` Replay Combinators (`§4`):** exports `stubGuardedF3GhostRo_avoidS5`
   (consumed by `ElfSampleNttStuckDivergeExtraWideFmt`) and `f3LinkedCallHook_avoidS5`
   (consumed by `ElfSampleNttStuckDivergeExtraWideCrypto`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
  ProofLib.StdStartup
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv FitsEvents
   NullAllowed OomPreserved RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntriesBase
   RustLayoutOk StaticMappedCover VmMemPreserved VmPreserved allocMemcpyVmSpec
   mallocngBudgetPool mallocngBudgetPoolAt mallocngBudgetPoolInv
   rustAllocEvents rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase
   rustCliReallocBudgetSpecBase rustDeallocEvents rustReallocEvents zeroBudgetLimits)
open LibsignalBinary.Heap.Fine
  (allocMemsetVmSpec f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr
   f3RxWordCount f3StdLayout f3StubAddrs f3StubAzAddr fineCostModel fineCostModelIface
   fineHookRustCliAllocBudget rdlAllocZeroedInstrs)
open LibsignalBinary.Heap.MuslMemOpsRunsTo
  (BlockExternFree codeLoaded_pureWordsProg_of_hasWords
   subroutine_ok_lift_pureWords_blockExternFree)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (PoolMemTransport budgetAllocShim_of_vm budgetMemcpy_false_of_vm
   rustBudgetAlloc_of_cliBase rustBudgetRealloc_of_cliBase toRustAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit fineHookNoAesRustCliAllocBudget fineHookNoAesRustCliAllocBudgetEntries_thunks
   fineHookNoAesRustCliAllocZeroedBudget_thunk_ok instPoolAesInitSplitFineHook)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX CodeBlocksPermRXMem mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memset (memset_memsetRegionSpec_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
   satisfies_of_stripExecOutside satisfies_stripExecOutside standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (c2_mng_placeable c2_progContainsMallocng_f3TrialRxProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2Kyber1024DecapsAddr c2Kyber1024EncapsAddr c2Mlkem768DecapsAddr
   c2Mlkem768Encaps1Addr c2Mlkem768FromSeedAddr
   c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq c2_resolve_mlkem768Decaps_eq
   c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon
  (ActiveRealRunExact SpecPreservesFsTraceExact f3LinkedCallHookExact
   f3LinkedCallHookExact_activeF3CallPre_of_noException withRoMemGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostReplays
  (stubGuardedF3GhostRo)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg externOnlyStdProg_externAt externOnlyStdProg_svc)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique
   f3TrialElf f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base
   f3TrialRxProg_no_ext f3TrialRxProg_stubs f3TrialRxProg_symbols
   f3TrialRxWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
   f3Trial_progContainsMallocng f3Trial_rustStdThunkCode
   f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_stepsUntil_det)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs
  (ProgContainsMallocng ProgContainsMultiLib memRegion_entails_exists_pointsToBytes
   memcpySymWords memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_hasWords
   memcpy_pureWords_ok memcpySrc memcpy_sepwp)
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.RustStd
  (budgetAllocShimSpec budgetMemcpySpec fmtSrcBytes
   mallocngPlacedCAddrs rustBudgetAllocSpec rustBudgetReallocSpec)

/-! ## 1. `s5Addrs` & `addS5Trap` Program Transformer -/

/-- Resolved entry addresses of `mlkemSampleNttSyms`
    (`[lsKemEncapsSym, lsKemDecapsSym, lsMlkemFromSeedSym, lsMlkemEncaps1Sym, lsMlkemDecapsSym]`). -/
@[expose] def s5Addrs : List (BitVec 64) :=
  [c2Kyber1024EncapsAddr, c2Kyber1024DecapsAddr, c2Mlkem768FromSeedAddr,
   c2Mlkem768Encaps1Addr, c2Mlkem768DecapsAddr]

theorem s5Addrs_eq_of_linkedAt {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) = s5Addrs := by
  unfold mlkemSampleNttSyms s5Addrs
  simp only [List.map_cons, List.map_nil, c2_resolve_kyber1024Encaps_eq hLs,
    c2_resolve_kyber1024Decaps_eq hLs, c2_resolve_mlkem768FromSeed_eq hLs,
    c2_resolve_mlkem768Encaps1_eq hLs, c2_resolve_mlkem768Decaps_eq hLs]
  rfl

private theorem s5Addrs_order_bounds :
    c2Mlkem768FromSeedAddr.toNat ≤ c2Mlkem768Encaps1Addr.toNat ∧
    c2Mlkem768Encaps1Addr.toNat ≤ c2Mlkem768DecapsAddr.toNat ∧
    c2Mlkem768DecapsAddr.toNat ≤ c2Kyber1024DecapsAddr.toNat ∧
    c2Kyber1024DecapsAddr.toNat ≤ c2Kyber1024EncapsAddr.toNat := by
  decide

theorem s5Addrs_contains_false_of_lt {a : BitVec 64}
    (hlt : a.toNat < c2Mlkem768FromSeedAddr.toNat) :
    s5Addrs.contains a = false := by
  have hb := s5Addrs_order_bounds
  unfold s5Addrs
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; omega)

theorem s5Addrs_contains_false_of_gt {a : BitVec 64}
    (hgt : c2Kyber1024EncapsAddr.toNat < a.toNat) :
    s5Addrs.contains a = false := by
  have hb := s5Addrs_order_bounds
  unfold s5Addrs
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; omega)

theorem stepsStrictAvoid_one_of_lt_s5 {mpl : MultiPlacement} {P : Program} {u v : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hlt : u.pc.toNat < c2Mlkem768FromSeedAddr.toNat)
    (hstep : Step P u v) :
    StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      P u v := by
  refine .step (fun hmem => ?_) hstep (.refl v)
  rw [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hmem
  rw [s5Addrs_contains_false_of_lt hlt] at hmem
  cases hmem

/-- Reserved synthetic stub symbol name used by `addS5Trap`. -/
@[expose] def s5TrapSym : String := "__sntt_s5_trap__"

/-- Synthetic `.Exception "hit S5"` trap handler installed at `s5Addrs`. -/
@[expose] def s5TrapFn : State → State :=
  fun s => { s with status := .Exception "hit S5" }

/-- Install `.Exception "hit S5"` extern traps at the 5 `s5Addrs` offsets of `P`, preserving
    `P.base`, `P.code`, `P.svc`, `P.symbols`, `P.overrides`, and all non-`s5Addrs` `externAt?`
    entries whenever `P.externs s5TrapSym = none`. -/
@[expose] def addS5Trap (P : Program) : Program :=
  { P with
    stubs := s5Addrs.map (fun a => (s5TrapSym, (a - P.base).toNat)) ++
      P.stubs.filter (fun p => p.1 != s5TrapSym)
    externs := fun sym => if sym == s5TrapSym then some s5TrapFn else P.externs sym }

theorem addS5Trap_svc (P : Program) : (addS5Trap P).svc = P.svc := rfl

private theorem addS5Trap_base (P : Program) : (addS5Trap P).base = P.base := rfl
private theorem addS5Trap_symbols (P : Program) : (addS5Trap P).symbols = P.symbols := rfl
private theorem addS5Trap_overrides (P : Program) : (addS5Trap P).overrides = P.overrides := rfl
private theorem addS5Trap_stubs (P : Program) :
    (addS5Trap P).stubs =
      s5Addrs.map (fun a => (s5TrapSym, (a - P.base).toNat)) ++
        P.stubs.filter (fun p => p.1 != s5TrapSym) := rfl

private theorem addS5Trap_externs_trap (P : Program) :
    (addS5Trap P).externs s5TrapSym = some s5TrapFn := by
  change (if s5TrapSym == s5TrapSym then some s5TrapFn else P.externs s5TrapSym) = some s5TrapFn
  simp

private theorem addS5Trap_externs_of_ne (P : Program) {nm : String}
    (hnm : ¬(nm == s5TrapSym) = true) :
    (addS5Trap P).externs nm = P.externs nm := by
  change (if nm == s5TrapSym then some s5TrapFn else P.externs nm) = P.externs nm
  simp [hnm]

theorem addS5Trap_codeLoaded_iff (P : Program) (m : Memory) :
    (addS5Trap P).CodeLoaded m ↔ P.CodeLoaded m :=
  ⟨fun h => h.of_base_code rfl rfl, fun h => h.of_base_code rfl rfl⟩

private theorem findSome?_s5Stubs_of_mem (P : Program) {pc : BitVec 64} :
    ∀ {xs : List (BitVec 64)}, xs.contains pc = true →
      (xs.map (fun a => (s5TrapSym, (a - P.base).toNat))).findSome?
        (fun (name, stubOff) =>
          if stubOff == (pc - P.base).toNat then (addS5Trap P).externs name else none) =
        some s5TrapFn
  | [], h => by cases h
  | a :: tl, h => by
    simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.findSome?_cons, addS5Trap_externs_trap P]
    by_cases hoff : ((a - P.base).toNat == (pc - P.base).toNat) = true
    · simp only [hoff, ↓reduceIte]
    · rcases h with rfl | htl
      · exact absurd (beq_self_eq_true _) hoff
      · simp only [hoff, Bool.false_eq_true, ↓reduceIte]
        exact findSome?_s5Stubs_of_mem P (xs := tl) htl

private theorem findSome?_s5Stubs_of_not_mem {P : Program} {pc : BitVec 64}
    (hbnd : (pc - P.base).toNat < 2 ^ 64) :
    ∀ {xs : List (BitVec 64)}, xs.contains pc = false →
      (xs.map (fun a => (s5TrapSym, (a - P.base).toNat))).findSome?
        (fun (name, stubOff) =>
          if stubOff == (pc - P.base).toNat then (addS5Trap P).externs name else none) = none
  | [], _ => rfl
  | a :: tl, h => by
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    have hne_off : ((a - P.base).toNat == (pc - P.base).toNat) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      apply h.1
      have ha64 : (a - P.base).toNat < 2 ^ 64 := BitVec.isLt (a - P.base)
      have hbv : a - P.base = pc - P.base := BitVec.eq_of_toNat_eq heq
      bv_omega
    simp only [List.map_cons, List.findSome?_cons, hne_off, Bool.false_eq_true, ↓reduceIte]
    exact findSome?_s5Stubs_of_not_mem hbnd h.2

private theorem findSome?_filter_stubs_eq (P : Program) (off : Nat)
    (hTrapNone : P.externs s5TrapSym = none) :
    (P.stubs.filter (fun p => p.1 != s5TrapSym)).findSome?
      (fun (name, stubOff) =>
        if stubOff == off then (addS5Trap P).externs name else none) =
    P.stubs.findSome?
      (fun (name, stubOff) => if stubOff == off then P.externs name else none) := by
  induction P.stubs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨nm, stOff⟩
    by_cases hnm : (nm == s5TrapSym) = true
    · have hnm_eq : nm = s5TrapSym := beq_iff_eq.mp hnm
      subst hnm_eq
      have hne_false : (s5TrapSym != s5TrapSym) = false := by simp [bne]
      simp only [List.filter_cons, hne_false, Bool.false_eq_true, ↓reduceIte,
        List.findSome?_cons, hTrapNone, ite_self]
      exact ih
    · have hne_true : (nm != s5TrapSym) = true := by simpa [bne] using hnm
      simp only [List.filter_cons, hne_true, ↓reduceIte, List.findSome?_cons,
        addS5Trap_externs_of_ne P hnm, ih]

theorem addS5Trap_externAt_s5 (P : Program) {pc : BitVec 64}
    (hs5 : s5Addrs.contains pc = true) :
    (addS5Trap P).externAt? pc = some s5TrapFn := by
  unfold Program.externAt? Program.hookAtOff?
  rw [addS5Trap_base, addS5Trap_stubs, List.findSome?_append, findSome?_s5Stubs_of_mem P hs5]
  rfl

theorem addS5Trap_externAt_of_not_s5 (P : Program) {pc : BitVec 64}
    (hTrapNone : P.externs s5TrapSym = none)
    (hns5 : s5Addrs.contains pc = false) :
    (addS5Trap P).externAt? pc = P.externAt? pc := by
  unfold Program.externAt? Program.hookAtOff?
  rw [addS5Trap_base, addS5Trap_stubs, addS5Trap_symbols, addS5Trap_overrides,
    List.findSome?_append, findSome?_s5Stubs_of_not_mem (BitVec.isLt (pc - P.base)) hns5,
    Option.none_or, findSome?_filter_stubs_eq P (pc - P.base).toNat hTrapNone]

/-! ## 2. Low `rxSeg` Prefix `f3LoRxProg` & Symbolic Slices -/

/-- Word count (`5606` words = `0x5798` B) covering `.text.b_pre`, `memcpy`, `memset`, `mallocng`,
    and the `seg[2]` Rust allocator thunks/shims strictly below `.text.lib2` (`0x479798`). -/
@[expose] def f3LoWordCount : Nat := 0x15e6

/-- Low `32 KiB` prefix of `f3TrialRxProg` (`[f3RxSegBase, f3RxSegBase + 4 * f3LoWordCount)`), with
    `svc = Syscall.standard` and zero externs/stubs. -/
noncomputable def f3LoRxProg : Program :=
  { base := f3RxSegBase
    code := f3TrialRxProg.code.take (4 * f3LoWordCount)
    svc := Syscall.standard }

/-- Half-open interval `[f3RxSegBase, f3RxSegBase + 4 * f3LoWordCount)` matching `f3LoRxProg`. -/
@[expose] def keepLo (pc : BitVec 64) : Bool :=
  decide ((pc - f3RxSegBase).toNat < 4 * f3LoWordCount)

private theorem f3LoRxProg_base : f3LoRxProg.base = f3RxSegBase := rfl

private theorem f3LoRxProg_code :
    f3LoRxProg.code = f3TrialRxProg.code.take (4 * f3LoWordCount) := rfl

private theorem f3LoRxProg_hookFree (off len : Nat) : f3LoRxProg.hookFree off len :=
  ⟨rfl, rfl⟩

private theorem f3TrialRxProg_code_len :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

private theorem f3LoRxProg_code_len :
    f3LoRxProg.code.length = 4 * f3LoWordCount := by
  rw [f3LoRxProg_code, List.length_take, f3TrialRxProg_code_len]
  have hle : 4 * f3LoWordCount ≤ 4 * f3RxWordCount := by decide
  exact Nat.min_eq_left hle

private theorem f3LoRxProg_no_ext (pc : BitVec 64) : f3LoRxProg.externAt? pc = none := rfl

theorem keepLo_s5_false {pc : BitVec 64} (hk : keepLo pc = true) :
    s5Addrs.contains pc = false := by
  unfold keepLo at hk
  rw [decide_eq_true_eq] at hk
  apply s5Addrs_contains_false_of_lt
  have hbound : f3RxSegBase.toNat + 4 * f3LoWordCount ≤ c2Mlkem768FromSeedAddr.toNat := by decide
  by_contra hge
  have hbase_le : f3RxSegBase.toNat ≤ pc.toNat := by omega
  have hsub : (pc - f3RxSegBase).toNat = pc.toNat - f3RxSegBase.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hbase_le)
  omega

private theorem list_getElem_of_eq_take {α : Type} {xs ys : List α} {n i : Nat}
    (h : xs = ys.take n) (hi : i < xs.length) (hi_ys : i < ys.length) :
    xs[i]'hi = ys[i]'hi_ys := by
  subst h
  exact List.getElem_take

theorem f3LoRxProg_codeLoaded_of_f3Trial {m : Memory}
    (hcl : f3TrialRxProg.CodeLoaded m) :
    f3LoRxProg.CodeLoaded m := by
  have hlen_le : f3LoRxProg.code.length ≤ f3TrialRxProg.code.length := by
    rw [f3LoRxProg_code_len, f3TrialRxProg_code_len]
    decide
  have hbase : f3LoRxProg.base = f3TrialRxProg.base := f3TrialRxProg_base.symm
  refine Program.CodeLoaded.intro (hbase ▸ hcl.aligned)
    (Nat.le_trans (by rw [hbase]; omega) hcl.no_wrap) fun i hi => ?_
  have hi_full : i < f3TrialRxProg.code.length := Nat.lt_of_lt_of_le hi hlen_le
  rw [hbase]
  have hbyte : f3LoRxProg.code[i]'hi = f3TrialRxProg.code[i]'hi_full :=
    list_getElem_of_eq_take f3LoRxProg_code hi hi_full
  exact ⟨(hcl.byte_eq i hi_full).trans hbyte.symm, hcl.perm_eq i hi_full,
    hcl.isLazyFree_eq i hi_full⟩

private theorem f3LoRxProg_read8_eq_of_codeLoaded {m1 m2 : Memory}
    (hLo : f3LoRxProg.CodeLoaded m1) (hFull : f3TrialRxProg.CodeLoaded m2)
    (off : Nat) (hoff_lt : off < f3LoRxProg.code.length)
    (hoff_full : off < f3TrialRxProg.code.length) :
    m1.read8 (f3LoRxProg.base + BitVec.ofNat 64 off) =
      m2.read8 (f3TrialRxProg.base + BitVec.ofNat 64 off) := by
  have hbyte : f3LoRxProg.code[off]'hoff_lt = f3TrialRxProg.code[off]'hoff_full :=
    list_getElem_of_eq_take f3LoRxProg_code hoff_lt hoff_full
  exact (hLo.byte_eq off hoff_lt).trans (hbyte.trans (hFull.byte_eq off hoff_full).symm)

theorem f3LoRxProg_codeLoaded_of_f3CodeInv {mpl mmpl : MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    f3LoRxProg.CodeLoaded m :=
  f3LoRxProg_codeLoaded_of_f3Trial hInv.rxCode

private theorem take_drop_prefix_four (xs : List (BitVec 8)) {off n : Nat}
    (hbnd : off + 4 ≤ n) :
    (match (xs.take n).drop off with
     | b0 :: b1 :: b2 :: b3 :: _ => some (b3 ++ b2 ++ b1 ++ b0)
     | _ => none) =
    (match xs.drop off with
     | b0 :: b1 :: b2 :: b3 :: _ => some (b3 ++ b2 ++ b1 ++ b0)
     | _ => none) := by
  have hn_eq : n = off + (n - off) := by omega
  rw [hn_eq, ← List.take_drop]
  have hge : 4 ≤ n - off := by omega
  cases hd : xs.drop off with
  | nil => simp
  | cons b0 r0 =>
    cases r0 with
    | nil =>
      cases hn : n - off with
      | zero => omega
      | succ k => simp
    | cons b1 r1 =>
      cases r1 with
      | nil =>
        cases hn : n - off with
        | zero => omega
        | succ k => cases k <;> simp
      | cons b2 r2 =>
        cases r2 with
        | nil =>
          cases hn : n - off with
          | zero => omega
          | succ k =>
            cases k with
            | zero => omega
            | succ k1 => cases k1 <;> simp
        | cons b3 r3 =>
          obtain ⟨d, hd_eq⟩ : ∃ d, n - off = d + 4 := ⟨n - off - 4, by omega⟩
          rw [hd_eq]
          rfl

private theorem f3LoRxProg_readWordOff_eq {off : Nat}
    (hbnd : off + 4 ≤ 4 * f3LoWordCount) :
    f3LoRxProg.readWordOff off = f3TrialRxProg.readWordOff off := by
  unfold Program.readWordOff
  by_cases hmod : off % 4 ≠ 0
  · simp [hmod]
  · simp only [hmod, ↓reduceIte, f3LoRxProg_code]
    exact take_drop_prefix_four f3TrialRxProg.code hbnd

private theorem f3Lo_hasWords_of_f3Trial {addr : BitVec 64} {words : List (BitVec 32)}
    (hw : f3TrialRxProg.hasWords addr words)
    (hfit : (addr - f3RxSegBase).toNat + 4 * words.length ≤ 4 * f3LoWordCount) :
    f3LoRxProg.hasWords addr words := by
  unfold Program.hasWords Program.hasWordsOff at hw ⊢
  rw [f3TrialRxProg_base] at hw
  rw [f3LoRxProg_base]
  refine ⟨hw.1, fun i hi => ?_, f3LoRxProg_hookFree _ _⟩
  rw [← hw.2.1 i hi]
  exact f3LoRxProg_readWordOff_eq (by omega)

private theorem f3Lo_hasInstrs_of_f3Trial {addr : BitVec 64} {instrs : List Instr}
    (hi : hasInstrs f3TrialRxProg addr instrs)
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + 4 * instrs.length ≤ f3RxSegBase.toNat + 4 * f3LoWordCount) :
    hasInstrs f3LoRxProg addr instrs := by
  intro k hk
  have hprev := hi k hk
  unfold Program.fetch at hprev ⊢
  have hext_lo : (f3LoRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k))).isSome = false := rfl
  have hext_tr : (f3TrialRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k))).isSome = false := by
    have he : f3TrialRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k)) = none :=
      f3TrialRxProg_no_ext _
    simp [he]
  rw [hext_lo]
  rw [hext_tr] at hprev
  simp only [Bool.false_eq_true, ↓reduceIte] at hprev ⊢
  have hbase : f3LoRxProg.base = f3RxSegBase := rfl
  rw [hbase]
  rw [f3TrialRxProg_base] at hprev
  have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
  have hk64 : 4 * k < 2 ^ 64 := by omega
  have hpc_nat : (addr + BitVec.ofNat 64 (4 * k)).toNat = addr.toNat + 4 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (by omega)]
  have hoff_nat : ((addr + BitVec.ofNat 64 (4 * k)) - f3RxSegBase).toNat =
      addr.toNat + 4 * k - f3RxSegBase.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hpc_nat]
  rw [f3LoRxProg_readWordOff_eq (by omega)]
  exact hprev

private theorem f3Trial_memcpy_hasWords_local :
    f3TrialRxProg.hasWords f3StdLayout.memcpyAddr memcpySymWords := by
  have hoff_lt : (f3StdLayout.memcpyAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memcpySymWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memcpyAddr - f3RxSegBase).toNat memcpySymWords = true)

theorem f3Lo_memcpy_hasWords :
    f3LoRxProg.hasWords f3StdLayout.memcpyAddr memcpySymWords := by
  have hlen : 4 * memcpySymWords.length = 396 := by rfl_kernel
  exact f3Lo_hasWords_of_f3Trial f3Trial_memcpy_hasWords_local (by rw [hlen]; decide)

private theorem f3Trial_memset_hasWords_local :
    f3TrialRxProg.hasWords f3StdLayout.memsetAddr memsetWords := by
  have hoff_lt : (f3StdLayout.memsetAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memsetWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true
      (by rfl_kernel : Nat.ble memsetWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memsetAddr - f3RxSegBase).toNat memsetWords = true)

theorem f3Lo_memset_hasWords :
    f3LoRxProg.hasWords f3StdLayout.memsetAddr memsetWords := by
  have hlen : 4 * memsetWords.length = 260 := by rfl_kernel
  exact f3Lo_hasWords_of_f3Trial f3Trial_memset_hasWords_local (by rw [hlen]; decide)

private theorem c2_mng_inElf_local (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem c2_mng_fnAddr_eq_local (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (name : String) :
    mallocngLib.fnAddr mmpl name = mallocngLib.fnAddr f3MallocngMpl name := by
  unfold MultiPlacedLib.fnAddr
  cases hlk : lookupBlockSym name mallocngLib.blocks with
  | none =>
    exact (f3CliElf_mallocng_linkedAt_unique hMm).1 0 (Nat.zero_lt_succ 23)
  | some p =>
    rcases p with ⟨i, _⟩
    dsimp only
    rw [(f3CliElf_mallocng_linkedAt_unique hMm).1 i (lookupBlockSym_lt hlk)]

private theorem c2_mng_cAddrs_eq_local (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [c2_mng_fnAddr_eq_local mmpl hMm]

theorem c2_keepLo_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → keepLo a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((c2_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, _, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable mmpl hMm) (c2_mng_inElf_local mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hhi_lo : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3LoWordCount := by decide
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    unfold keepLo
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    exact decide_eq_true (by omega)

theorem f3Lo_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3LoRxProg mmpl := by
  have hPl1 := c2_mng_placeable mmpl hMm
  have hIn1 := c2_mng_inElf_local mmpl hMm
  have hal_trial : f3TrialRxProg.base.toNat % 4 = 0 := by
    rw [f3TrialRxProg_base]; decide
  have hnw_trial : f3TrialRxProg.base.toNat + f3TrialRxProg.code.length ≤ 2 ^ 64 := by
    rw [f3TrialRxProg_base, f3TrialRxProg_code_len]; decide
  have hm0_cl : f3TrialRxProg.CodeLoaded (loadCodeMem f3TrialRxProg Memory.empty) :=
    codeLoaded_loadCodeMem (prog := f3TrialRxProg) Memory.empty hal_trial hnw_trial
  have hTrialMng := c2_progContainsMallocng_f3TrialRxProg mmpl hMm
  refine ProgContainsMultiLib.of_noExterns hPl1 rfl (fun m hLo i hi => ?_) f3LoRxProg_no_ext
  have hm0_blk := hTrialMng.codeLoaded (loadCodeMem f3TrialRxProg Memory.empty) hm0_cl i hi
  obtain ⟨_, _, hm_lo, hm_hi⟩ :=
    f3CliElf_mallocng_code_bounds_of_inElf hPl1 hIn1 i hi
  have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
  have hhi_lo : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3LoWordCount := by decide
  have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
  have hlen_i : (mallocngLib.blockProgram mmpl i).code.length =
      mallocngLib.blocks[i].code.length := by
    simp only [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
    exact CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hbase_i : (mallocngLib.blockProgram mmpl i).base = mmpl.base i := rfl
  refine Program.CodeLoaded.intro hm0_blk.aligned hm0_blk.no_wrap fun k hk => ?_
  have hk_raw : k < mallocngLib.blocks[i].code.length := by rwa [← hlen_i]
  have hoff_lt : (mmpl.base i).toNat + k - f3RxSegBase.toNat < f3LoRxProg.code.length := by
    rw [f3LoRxProg_code_len]; omega
  have hoff_full : (mmpl.base i).toNat + k - f3RxSegBase.toNat < f3TrialRxProg.code.length := by
    rw [f3TrialRxProg_code_len]
    have hle_words : 4 * f3LoWordCount ≤ 4 * f3RxWordCount := by decide
    omega
  have haddr_lo : (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k =
      f3LoRxProg.base + BitVec.ofNat 64 ((mmpl.base i).toNat + k - f3RxSegBase.toNat) := by
    rw [hbase_i, f3LoRxProg_base]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have haddr_trial : (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k =
      f3TrialRxProg.base + BitVec.ofNat 64 ((mmpl.base i).toNat + k - f3RxSegBase.toNat) := by
    rw [haddr_lo, f3LoRxProg_base, f3TrialRxProg_base]
  have hb_m0 := hm0_blk.byte_eq k hk
  rw [haddr_trial] at hb_m0
  rw [haddr_lo]
  exact ⟨(f3LoRxProg_read8_eq_of_codeLoaded hLo hm0_cl _ hoff_lt hoff_full).trans hb_m0,
    hLo.perm_eq _ hoff_lt, hLo.isLazyFree_eq _ hoff_lt⟩

private theorem f3Lo_rustStdThunkCode :
    VerifiedLibraries.RustStd.RustStdThunkCode f3LoRxProg
      f3StubAddrs.toRustStd f3RdlAddrs.toRustStd where
  alloc_thunk := f3Lo_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.alloc_thunk
    (by decide) (by decide)
  dealloc_thunk := f3Lo_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.dealloc_thunk
    (by decide) (by decide)
  realloc_thunk := f3Lo_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.realloc_thunk
    (by decide) (by decide)

private theorem f3Lo_rdlShims :
    VerifiedLibraries.RustStd.RustStdRdlShimCode f3LoRxProg
      f3RdlAddrs.toRustStd (mallocngPlacedCAddrs f3MallocngMpl) f3StdLayout.memcpyAddr where
  alloc_instrs := f3Lo_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.alloc_instrs
    (by decide) (by decide)
  dealloc_instrs := f3Lo_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.dealloc_instrs
    (by decide) (by decide)
  realloc_instrs := f3Lo_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.realloc_instrs
    (by decide) (by decide)

private theorem f3Lo_stubAz_hasInstrs :
    hasInstrs f3LoRxProg f3StubAzAddr
      [.b (f3RdlAzAddr - f3StubAzAddr)] :=
  f3Lo_hasInstrs_of_f3Trial f3Trial_stubAz_hasInstrs (by decide) (by decide)

private theorem f3Lo_allocZeroedInstrs :
    hasInstrs f3LoRxProg f3RdlAzAddr
      (rdlAllocZeroedInstrs f3RdlAzAddr
        (mallocngLib.fnAddr f3MallocngMpl "calloc")
        (mallocngPlacedCAddrs f3MallocngMpl).posixMemalign f3StdLayout.memsetAddr) :=
  f3Lo_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.allocZeroedInstrs (by decide) (by decide)

private theorem f3Lo_noAllocShimV2 :
    hasInstrs f3LoRxProg f3NoShimV2Addr [.ret .x30] :=
  f3Lo_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.noAllocShimV2 (by decide) (by decide)

/-! ## 3. `withExecFrozenBudget`, `nonZeroEquivLim`, & Generic `f3LoRxProg → P` Lifters -/

/-- Strengthen `A : RustCliAllocBudget M` with `⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝` so
    subroutine proofs on `addS5Trap P_sub` can lift allocator calls out of `f3LoRxProg` via
    `stripExecOutside keepLo` without requiring `HooksUnfetched` at `s5Addrs`. -/
@[expose] def withExecFrozenBudget {M : AllocCostModel} (A : RustCliAllocBudget M) :
    RustCliAllocBudget M where
  pool lim st s := A.pool lim st s ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝
  live := A.live
  block_valid := A.block_valid
  pool_transport lim st s s' hvm := by
    have hp := A.pool_transport lim st s s' hvm
    have hfr : ExecFrozen s'.mem = ExecFrozen s.mem :=
      propext ⟨fun h => ExecFrozen.of_perm_eq h (fun a => (hvm.perm_eq a).symm),
        fun h => ExecFrozen.of_perm_eq h hvm.perm_eq⟩
    simp only [hp, hfr]
  pool_zero_transport st s s' hp := by
    have hp0 := A.pool_zero_transport st s s' hp
    simp only [hp0, ne_eq, not_true_eq_false, IsEmpty.forall_iff]

@[simp]
theorem withExecFrozenBudget_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withExecFrozenBudget A).repAlloc = A.repAlloc := rfl

instance instPoolMemTransportWithExecFrozenBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    [PoolMemTransport A] : PoolMemTransport (withExecFrozenBudget A) where
  pool_transport_mem lim st {_s _s'} hvm := by
    have hp := PoolMemTransport.pool_transport_mem (A := A) lim st hvm
    have hfr : ExecFrozen _s'.mem = ExecFrozen _s.mem :=
      propext ⟨fun h => ExecFrozen.of_perm_eq h (fun a => (hvm.2.2 a).symm),
        fun h => ExecFrozen.of_perm_eq h hvm.2.2⟩
    dsimp only [withExecFrozenBudget]
    rw [hp, hfr]

noncomputable instance instPoolAesInitSplitWithExecFrozenBudget
    (γ : GhostName) (mmpl : MultiPlacement) (tp brkStart : BitVec 64) :
    PoolAesInitSplit (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
      (brkStart - 8160#64) :=
  (instPoolAesInitSplitFineHook γ mmpl tp brkStart).liftPure
    (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart))
    (fun lim s => lim ≠ zeroBudgetLimits → ExecFrozen s.mem)
    rfl
    (fun _ _ _ => rfl)
    (fun _ _ _ => rfl)
    (fun _ _ _ hp hfr hlim =>
      ExecFrozen.of_perm_eq (hfr hlim) hp.vmPreserved.perm_eq)

/-- Prepend pure `⌜ExecFrozen s0.mem⌝` to `spec.pre`. -/
@[expose] def withExecFrozenSpec {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜ExecFrozen s0.mem⌝ ∗ spec.pre x s0 }

/-- Unenforced `BudgetLimits` witness syntactically distinct from `zeroBudgetLimits`. -/
def dummyUnenforcedLim : BudgetLimits :=
  { staticCount := 1, staticBytes := 0, physCap := 0, enforced := false }

private theorem dummyUnenforcedLim_ne_zero : dummyUnenforcedLim ≠ zeroBudgetLimits := by
  decide

/-- Replace `zeroBudgetLimits` (`enforced = false, staticCount = 0`) with an equivalent
    unenforced `BudgetLimits` value that is syntactically `≠ zeroBudgetLimits`. -/
@[expose] def nonZeroEquivLim (lim : BudgetLimits) : BudgetLimits :=
  if lim = zeroBudgetLimits then dummyUnenforcedLim else lim

theorem nonZeroEquivLim_ne_zero (lim : BudgetLimits) :
    nonZeroEquivLim lim ≠ zeroBudgetLimits := by
  unfold nonZeroEquivLim
  split
  · exact dummyUnenforcedLim_ne_zero
  · assumption

theorem fitsEvents_nonZeroEquivLim (M : AllocCostModel)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) :
    FitsEvents M (nonZeroEquivLim lim) st evs = FitsEvents M lim st evs := by
  unfold nonZeroEquivLim
  split
  · rename_i h; subst h
    cases evs with
    | nil => rfl
    | cons ev rest =>
      apply propext
      constructor <;> (rintro ⟨⟨_, henf, _⟩, _⟩; cases henf)
  · rfl

theorem fitsEnv_nonZeroEquivLim (M : AllocCostModel)
    (lim : BudgetLimits) (st : M.σ) (E : List AllocEvent → Prop) :
    FitsEnv M (nonZeroEquivLim lim) st E = FitsEnv M lim st E := by
  dsimp only [FitsEnv]
  simp only [fitsEvents_nonZeroEquivLim]

theorem fineHookPool_nonZeroEquivLim (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (fineHookRustCliAllocBudget γ mpl tp brkStart).pool (nonZeroEquivLim lim) st s =
      (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s := by
  unfold nonZeroEquivLim
  split
  · rename_i h; subst h
    have hinv : ∀ staticIvs ivs u,
        mallocngBudgetPoolInv dummyUnenforcedLim staticIvs ivs u =
          mallocngBudgetPoolInv zeroBudgetLimits staticIvs ivs u := by
      intro _ _ _; apply propext; constructor <;> (intro _ henf; cases henf)
    have hrx : ∀ u,
        (dummyUnenforcedLim.enforced = true → CodeBlocksPermRX mpl u) =
        (zeroBudgetLimits.enforced = true → CodeBlocksPermRX mpl u) := by
      intro _; rfl
    dsimp only [fineHookRustCliAllocBudget, mallocngHookRustCliAllocBudget,
      mallocngHookBudgetPool, mallocngBudgetPool, mallocngBudgetPoolAt]
    simp only [hinv, hrx]
  · rfl

theorem withExecFrozenBudget_pool_entails (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (withExecFrozenBudget (fineHookRustCliAllocBudget γ mpl tp brkStart)).pool
        (nonZeroEquivLim lim) st s ⊢
      (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s := by
  dsimp only [withExecFrozenBudget]
  rw [fineHookPool_nonZeroEquivLim, sepConj_comm]
  exact Entails.pure_left fun _ => Entails.refl _

private theorem execFrozen_stripExecOutside {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) :
    ExecFrozen (stripExecOutside keep m) := by
  intro a hx
  obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
  rw [strip_perm_of_keep hk]
  exact hfr a hx_m

private theorem stripS_mem_eq_local (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl

private theorem stripS_pc_eq_local (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl

private theorem stripS_sp_eq_local (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl

private theorem stripS_status_eq_local (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl

private theorem stripS_r64_eq_local (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl

private theorem strip_read32_eq_local (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by simp [Memory.read32, strip_read8]

private theorem step_status_running_local {P : Program} {u v : State} (h : Step P u v) :
    u.status = .Running := by cases h <;> assumption

private theorem steps_preserves_halted_local {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all

private theorem steps_preserves_exception_local {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all

private theorem blockExternFree_of_keepLo {P : Program} {addr : BitVec 64} {len : Nat}
    (hext_lo : ∀ pc, keepLo pc = true → P.externAt? pc = none)
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + len ≤ f3RxSegBase.toNat + 4 * f3LoWordCount) :
    BlockExternFree P addr len := by
  intro a ha
  apply hext_lo
  unfold keepLo
  have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
  have ha_off : (a - addr).toNat < len := ha
  have heq_a : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have ht : (addr + BitVec.ofNat 64 (a - addr).toNat).toNat = addr.toNat + (a - addr).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [heq_a] at ht
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  exact decide_eq_true (by omega)

private theorem fmtSrcBytes_eq_memcpySrc_local (ro : Bool) (src : BitVec 64)
    (bs : List (BitVec 8)) :
    fmtSrcBytes ro src bs = memcpySrc ro src bs := by
  cases ro <;> rfl

private theorem budgetMemcpy_len_le_2pow63_local {m : Memory} {ro : Bool} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ fmtSrcBytes ro src bs) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    cases ro <;> simp only [fmtSrcBytes, Bool.false_eq_true, ↓reduceIte] at h
    · refine Satisfies.pointsToBytes_to_ro ?_
      rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
    · rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

private theorem memcpy_pureWords_ro_ok_local (ro : Bool) (addr dst src : BitVec 64)
    (dstBs srcBs : List (BitVec 8)) (n : BitVec 64)
    (hdstLen : dstBs.length = n.toNat) (hsrcLen : srcBs.length = n.toNat)
    (hn63 : n.toNat ≤ 2 ^ 63) :
    subroutine_ok (pureWordsProg addr memcpySymWords) addr
      { pre := fun (_ : Unit) s =>
          ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ s.readReg64 .x2 = n⌝ ∗
          (dst ↦ₛ dstBs) ∗ memcpySrc ro src srcBs
        post := fun _ s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab ∧ sf.readReg64 .x0 = dst⌝ ∗
          (dst ↦ₛ srcBs) ∗ memcpySrc ro src srcBs } := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(dst ↦ₛ dstBs) ∗ memcpySrc ro src srcBs, by rwa [sepConj_assoc], ?_⟩
  refine SepWP.mono (memcpy_sepwp ro (pureWordsProg addr memcpySymWords) addr
    (memcpy_pureWords_hasWords addr) s0
    dst src n dstBs srcBs hpc hrun hx0 hx1 hx2 hdstLen hsrcLen hn63) ?_
  intro sf P_f _ _ ⟨⟨hx0f, hspf, hcsf, _hfs, _htr, _htp, _hbrks, horc, hsym, _hsig, _hbrk⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
  exact ⟨⟨horc, hsym, hx0f⟩, hm'⟩

theorem c2_memcpy_f3Lo_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StdLayout.memcpyAddr allocMemcpyVmSpec := by
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
      (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords (hcl m hm) f3Lo_memcpy_hasWords (by decide)
  have hlen_w : 4 * memcpySymWords.length = 396 := by rfl_kernel
  have hext : BlockExternFree P f3StdLayout.memcpyAddr (4 * memcpySymWords.length) :=
    blockExternFree_of_keepLo hext_lo (by decide) (by rw [hlen_w]; decide)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpyVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 :=
    budgetMemcpy_len_le_2pow63_local (ro := false) (Nat.le_of_lt hlt)
      (by simpa [fmtSrcBytes] using hm_assoc)
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt))) hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_blockExternFree
    (P := P)
    (memcpy_pureWords_ok f3StdLayout.memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    hsvc
    (memcpy_allInstrs_noSvc_noMsr f3StdLayout.memcpyAddr)
    hcl_pure hext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
      rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem c2_budgetMemcpy_f3Lo_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    ∀ ro : Bool, subroutine_ok P f3StdLayout.memcpyAddr (budgetMemcpySpec ro) := by
  intro ro
  cases ro with
  | false => exact budgetMemcpy_false_of_vm (c2_memcpy_f3Lo_ok hsvc hcl hext_lo)
  | true =>
    have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
        (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords).CodeLoaded m :=
      fun m hm => codeLoaded_pureWordsProg_of_hasWords (hcl m hm) f3Lo_memcpy_hasWords (by decide)
    have hlen_w : 4 * memcpySymWords.length = 396 := by rfl_kernel
    have hext : BlockExternFree P f3StdLayout.memcpyAddr (4 * memcpySymWords.length) :=
      blockExternFree_of_keepLo hext_lo (by decide) (by rw [hlen_w]; decide)
    apply subroutine_ok.of_codeLoaded
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
    simp only [budgetMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
    have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ fmtSrcBytes true src bs) ∗ R := by
      rwa [← sepConj_assoc] at hm
    have hn63 : bs.length ≤ 2 ^ 63 := budgetMemcpy_len_le_2pow63_local (Nat.le_of_lt hlt) hm_assoc
    have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hm_ex : s0.mem ⊨
        (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
          (fmtSrcBytes true src bs ∗ R) :=
      Satisfies.mono
        (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt)))
        hm
    rw [sepExists_sepConj_left] at hm_ex
    obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
    obtain ⟨hdstLen, hm_pts⟩ := hm_dst
    have hLift := subroutine_ok_lift_pureWords_blockExternFree
      (P := P)
      (memcpy_pureWords_ro_ok_local true f3StdLayout.memcpyAddr dst src dstBs bs
        (BitVec.ofNat 64 bs.length) (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
      hsvc
      (memcpy_allInstrs_noSvc_noMsr f3StdLayout.memcpyAddr)
      hcl_pure hext
      (h_pre_mem := fun _ _ _ => rfl)
      (h_post_mem := fun _ _ _ _ _ => rfl)
    refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
    · simp only [sepConj_assoc, satisfies_pure_sepConj, ← fmtSrcBytes_eq_memcpySrc_local]
      exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
    · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        refine Satisfies.mono (sepConj_mono_left ?_) hpost
        dsimp only [budgetMemcpySpec]
        rw [← fmtSrcBytes_eq_memcpySrc_local]
        refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
        rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
        exact Entails.pure_right
          ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
            ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm⟩⟩
          (Entails.refl _)
      · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem c2_memset_f3Lo_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StdLayout.memsetAddr allocMemsetVmSpec := by
  let memsetAddr := f3StdLayout.memsetAddr
  let prog₀ := pureWordsProg memsetAddr memsetWords
  have hpure_hw : prog₀.hasWords memsetAddr memsetWords :=
    pureWordsProg_hasWords
      (Nat.le_of_ble_eq_true
        (by rfl_kernel : Nat.ble (4 * memsetWords.length) (2 ^ 64) = true))
      (by rfl_kernel :
        ((List.range memsetWords.length).all fun i =>
          (pureWordsProg 0#64 memsetWords).readWordOff (4 * i) ==
            memsetWords[i]?) = true)
  have hpure_nosvc :
      prog₀.allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
    Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 memsetWords) rfl
      (by rfl_kernel :
        (pureWordsProg 0#64 memsetWords).allInstrs
          (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
  have hpure : subroutine_ok prog₀ memsetAddr
      { ProofLib.memsetRegionSpec with
        post := fun x s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab⌝ ∗
            ProofLib.memsetRegionSpec.post x s0 sf } := by
    apply subroutine_ok_of_steps_outcome
    intro x R s0 hpc hrun hpre hsp hL
    obtain ⟨sf, hsteps, hout⟩ :=
      subroutine_ok_elim_steps_outcome
        (memset_memsetRegionSpec_ok hpure_hw)
        x R s0 hpc hrun hpre hsp hL
    have horc : sf.oracle = s0.oracle :=
      Steps.oracle_eq_of_standard rfl
        (fun pc => by
          simp [prog₀, pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?])
        hsteps
    have hsym : sf.symtab = s0.symtab := hsteps.symtab_eq
    refine ⟨sf, hsteps, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨horc, hsym⟩, hpost⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m → prog₀.CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords (hcl m hm) f3Lo_memset_hasWords (by decide)
  have hlen_w : 4 * memsetWords.length = 260 := by rfl_kernel
  have hext : BlockExternFree P memsetAddr (4 * memsetWords.length) :=
    blockExternFree_of_keepLo hext_lo (by decide) (by dsimp [memsetAddr]; rw [hlen_w]; decide)
  have hlift := subroutine_ok_lift_pureWords_blockExternFree
    (P := P) hpure hsvc hpure_nosvc hcl_pure hext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ptr, c, n⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemsetVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hn_nat : (s0.readReg64 .x2).toNat = n := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine hlift.mono_outcome (ptr, c, n) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [ProofLib.memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hn_nat, Nat.le_of_lt hlt⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [ProofLib.memsetRegionSpec, allocMemsetVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym⟩ =>
        Entails.pure_left fun hx0f => ?_
      obtain ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩ := hpf
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

private theorem hasInstrs_P_of_f3Lo {P : Program} {addr : BitVec 64} {instrs : List Instr}
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none)
    (hi_lo : hasInstrs f3LoRxProg addr instrs)
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + 4 * instrs.length ≤ f3RxSegBase.toNat + 4 * f3LoWordCount) :
    ∀ m : Memory, P.CodeLoaded m →
      ∀ (k : Nat) (hk : k < instrs.length),
        P.fetchMem m (addr + BitVec.ofNat 64 (4 * k)) = some (instrs[k]'hk) := by
  intro m hPm k hk
  have hLom := hcl m hPm
  have hfk := hi_lo k hk
  have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
  have hk64 : 4 * k < 2 ^ 64 := by omega
  have hpc_nat : (addr + BitVec.ofNat 64 (4 * k)).toNat = addr.toNat + 4 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (by omega)]
  have hkp : keepLo (addr + BitVec.ofNat 64 (4 * k)) = true := by
    unfold keepLo
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hpc_nat]
    exact decide_eq_true (by omega)
  have hfm_lo : f3LoRxProg.fetchMem m (addr + BitVec.ofNat 64 (4 * k)) = some (instrs[k]'hk) :=
    Program.fetchMem_of_fetch hLom hfk
  unfold Program.fetchMem at hfm_lo ⊢
  rw [hext_lo _ hkp]
  have he_lo : f3LoRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k)) = none := rfl
  rw [he_lo] at hfm_lo
  exact hfm_lo

theorem c2_shim_f3Lo_ok {P : Program}
    (_hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3NoShimV2Addr rustAllocShimVmSpec := by
  apply subroutine_ok_of_steps_outcome
  intro () R s0 hpc hrun hpre _hsp hPm
  dsimp only [rustAllocShimVmSpec] at hpre
  rw [emp_sepConj] at hpre
  have hfm0 := hasInstrs_P_of_f3Lo hcl hext_lo f3Lo_noAllocShimV2 (by decide) (by decide)
    s0.mem hPm 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, List.getElem_cons_zero] at hfm0
  rw [← hpc] at hfm0
  have hstep : Step P s0 (P.evalInst (.ret .x30) s0) := Step.exec hrun hfm0
  have hev : P.evalInst (.ret .x30) s0 = s0.setPC (s0.readReg64 .x30) := by
    simp only [Program.evalInst, execInstWithSvc]
  rw [hev] at hstep
  refine ⟨s0.setPC (s0.readReg64 .x30), Steps.step hstep (Steps.refl _),
    Or.inl ⟨⟨rfl, rfl, hrun⟩, ?_, ?_⟩⟩
  · rw [CallingConventionPreserved_setPC]
    exact CallingConventionPreserved.rfl s0
  · dsimp only [rustAllocShimVmSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨⟨rfl, rfl, rfl⟩, by cases s0; rfl, fun _ => by cases s0; rfl,
        fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

theorem c2_budgetAllocShim_f3Lo_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3NoShimV2Addr budgetAllocShimSpec :=
  budgetAllocShim_of_vm (c2_shim_f3Lo_ok hsvc hcl hext_lo)

/-! ### 3b. `f3LoRxProg → P` Generic Subroutine Lifter & `withExecFrozenBudget` Allocator Contracts -/

private theorem f3LoRxProg_codeLoaded_stripKeepLo {m : Memory}
    (hcl : f3LoRxProg.CodeLoaded m) :
    f3LoRxProg.CodeLoaded (stripExecOutside keepLo m) := by
  have hlen : f3LoRxProg.code.length = 4 * f3LoWordCount := f3LoRxProg_code_len
  have hbase : f3LoRxProg.base = f3RxSegBase := rfl
  have htop : f3RxSegBase.toNat + 4 * f3LoWordCount < 2 ^ 64 := by decide
  refine Program.CodeLoaded.intro hcl.aligned hcl.no_wrap fun i hi => ?_
  have hi_lt : i < 4 * f3LoWordCount := by rwa [← hlen]
  have hk : keepLo (f3LoRxProg.base + BitVec.ofNat 64 i) = true := by
    rw [hbase]
    unfold keepLo
    have hsub : (f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase).toNat = i := by
      rw [show f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase = BitVec.ofNat 64 i by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    exact decide_eq_true hi_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8]; exact hcl.byte_eq i hi
  · rw [strip_perm_of_keep hk]; exact hcl.perm_eq i hi
  · rw [strip_isLazyFree]; exact hcl.isLazyFree_eq i hi

private theorem steps_lift_of_stripS_keepLo {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none)
    {sa' sf' : State} (hsteps : Steps f3LoRxProg sa' sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ sa : State, sa' = stripS keepLo sa → ExecFrozen sa.mem →
      ∃ sf : State, Steps P sa sf ∧ sf' = stripS keepLo sf ∧ ExecFrozen sf.mem := by
  induction hsteps with
  | refl _ =>
    intro sa hsa hfra
    exact ⟨sa, .refl sa, hsa, hfra⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt' (steps_preserves_halted_local hrest rfl))
    | extern _ he' _ _ =>
      cases he'
    | extern_fault _ he' _ =>
      cases he'
    | @exec inst hr' hfm' =>
      have hra : sa.status = .Running := by
        rw [hsa, stripS_status_eq_local] at hr'; exact hr'
      rw [hsa, stripS_pc_eq_local, stripS_mem_eq_local] at hfm'
      unfold Program.fetchMem at hfm'
      have he_lo : (f3LoRxProg.externAt? sa.pc).isSome = false := rfl
      rw [he_lo] at hfm'
      simp only [Bool.false_eq_true, ↓reduceIte] at hfm'
      by_cases hal_pc : sa.pc.toNat % 4 = 0
      · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
        by_cases hce' : (stripExecOutside keepLo sa.mem).canExec sa.pc 4 = true
        · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
          have hx4 :
              ((stripExecOutside keepLo sa.mem).perm sa.pc).x = true ∧
              ((stripExecOutside keepLo sa.mem).perm (sa.pc + 1#64)).x = true ∧
              ((stripExecOutside keepLo sa.mem).perm (sa.pc + 2#64)).x = true ∧
              ((stripExecOutside keepLo sa.mem).perm (sa.pc + 3#64)).x = true := by
            simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
          obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
          obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
          obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
          obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
          have hce : sa.mem.canExec sa.pc 4 = true := by
            simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
          rw [strip_read32_eq_local] at hfm'
          have hextP : P.externAt? sa.pc = none := hext_lo sa.pc hkp0
          have hfmP : P.fetchMem sa.mem sa.pc = some inst := by
            unfold Program.fetchMem; simp [hextP, hal_pc, hce, hfm']
          by_cases hsvc0 : inst.isSvc0 = true
          · have hinst : inst = .system false 0#16 := by
              cases inst <;> simp [Instr.isSvc0] at hsvc0
              rcases hsvc0 with ⟨rfl, rfl⟩; rfl
            subst hinst
            obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keepLo) hfra
            have hev_strip :
                f3LoRxProg.evalInst (.system false 0#16) (stripS keepLo sa) =
                  stripS keepLo (Syscall.standard sa) := by
              simp [f3LoRxProg, Program.evalInst, execInstWithSvc, hcomm]
            have hevP : P.evalInst (.system false 0#16) sa = Syscall.standard sa := by
              simp [Program.evalInst, execInstWithSvc, hsvc]
            have hstepP : Step P sa (Syscall.standard sa) := hevP ▸ Step.exec hra hfmP
            rw [hsa, hev_strip] at hrest ih
            obtain ⟨sf, hsteps_rest, hsf_eq, hfr_sf⟩ :=
              ih hnhalt' (Syscall.standard sa) rfl hfr_sb
            exact ⟨sf, .step hstepP hsteps_rest, hsf_eq, hfr_sf⟩
          · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
            have hev_strip :
                f3LoRxProg.evalInst inst (stripS keepLo sa) =
                  stripS keepLo (execInst inst sa) := by
              rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0, execInst_stripS hnsvc0]
            have hevP : P.evalInst inst sa = execInst inst sa :=
              evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 sa
            have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
            have hfr_sb : ExecFrozen (execInst inst sa).mem :=
              ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
            have hstepP : Step P sa (execInst inst sa) := hevP ▸ Step.exec hra hfmP
            rw [hsa, hev_strip] at hrest ih
            obtain ⟨sf, hsteps_rest, hsf_eq, hfr_sf⟩ :=
              ih hnhalt' (execInst inst sa) rfl hfr_sb
            exact ⟨sf, .step hstepP hsteps_rest, hsf_eq, hfr_sf⟩
        · simp [hce'] at hfm'
      · simp [hal_pc] at hfm'

theorem lift_f3LoRxProg_subroutine_ok {α : Type} {P : Program} {entry : BitVec 64}
    {spec0 specF : Spec α}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none)
    (hOk0 : subroutine_ok f3LoRxProg entry spec0)
    (hPre : ∀ (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ specF.pre x s0 ∗ R) →
      ExecFrozen s0.mem ∧ ((stripS keepLo s0).mem ⊨ spec0.pre x (stripS keepLo s0) ∗ R))
    (hOut : ∀ (x : α) (R : SepProp) (s0 sf : State),
      ExecFrozen sf.mem →
      SubroutineOutcome spec0 x R (stripS keepLo s0) (stripS keepLo sf) →
      SubroutineOutcome specF x R s0 sf) :
    subroutine_ok P entry specF := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hpreF hsp hPm
  obtain ⟨hFr0, hpre0'⟩ := hPre x R s0 hpreF
  have hcl_lo' : f3LoRxProg.CodeLoaded (stripS keepLo s0).mem :=
    f3LoRxProg_codeLoaded_stripKeepLo (hcl s0.mem hPm)
  obtain ⟨sf', hsteps', hout0'⟩ :=
    subroutine_ok_elim_steps_outcome hOk0 x R (stripS keepLo s0)
      (by rw [stripS_pc_eq_local]; exact hpc)
      (by rw [stripS_status_eq_local]; exact hrun)
      hpre0'
      (by cases s0; exact hsp)
      hcl_lo'
  have hnhalt' : sf'.status ≠ .Halted := by
    rcases hout0' with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
      (rw [hst]; nofun)
  obtain ⟨sf, hstepsP, hsf_eq, hFr_sf⟩ :=
    steps_lift_of_stripS_keepLo hsvc hext_lo hsteps' hnhalt' s0 rfl hFr0
  rw [hsf_eq] at hout0'
  exact ⟨sf, hstepsP, hOut x R s0 sf hFr_sf hout0'⟩

private theorem allocCallPreserved_stripS_eq (keep : BitVec 64 → Bool) (s0 sf : State) :
    AllocCallPreserved (stripS keep s0) (stripS keep sf) = AllocCallPreserved s0 sf := by
  cases s0; cases sf; rfl

private theorem oomPreserved_stripS_eq (keep : BitVec 64 → Bool) (s0 sf : State) :
    OomPreserved (stripS keep s0) (stripS keep sf) = OomPreserved s0 sf := by
  cases s0; cases sf; rfl

private theorem lift_allocBase_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart entry : BitVec 64) {lim : BudgetLimits} (zeroed : Bool)
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none)
    (hOk0 : subroutine_ok f3LoRxProg entry
      (rustCliAllocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed)) :
    subroutine_ok P entry
      (rustCliAllocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim zeroed) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepLo_mallocng mmpl hMm
  refine lift_f3LoRxProg_subroutine_ok hsvc hcl hext_lo hOk0 ?_ ?_
  · rintro ⟨size, align, st⟩ R s0 hpreF
    dsimp only [rustCliAllocBudgetSpecBase, withExecFrozenBudget] at hpreF
    have hRearr :
        (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align⌝ ∗
          (A₀.pool lim st s0 ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝) ∗
          stackAt s0.sp allocHookStack) ∗ R =
        ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝ ∗
          ((⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
              RustLayoutOk size align⌝ ∗
            A₀.pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hRearr, satisfies_pure_sepConj] at hpreF
    rcases hpreF with ⟨himp, hpre0⟩
    have hFr0 : ExecFrozen s0.mem := himp hlim
    refine ⟨hFr0, ?_⟩
    have hsat := satisfies_stripExecOutside keepLo hpre0
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [stripS_r64_eq_local, stripS_r64_eq_local, stripS_sp_eq_local,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim st s0]
    exact hsat
  · rintro ⟨size, align, st⟩ R s0 sf hFr_sf hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨by cases s0; cases sf; exact hret', by cases s0; cases sf; exact hcc', ?_⟩
      dsimp only [rustCliAllocBudgetSpecBase] at hpost' ⊢
      rw [stripS_r64_eq_local, allocCallPreserved_stripS_eq, stripS_sp_eq_local,
        fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim _ sf] at hpost'
      have hpost0 : sf.mem ⊨
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A₀.pool lim
              (if sf.readReg64 .x0 = 0 then st
               else fineCostModel.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
             else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
               A₀.live (sf.readReg64 .x0) size align ∗
               (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                else memRegion (sf.readReg64 .x0) size))) ∗ R :=
        satisfies_of_stripExecOutside hFr_sf hpost'
      dsimp only [withExecFrozenBudget]
      exact Satisfies.mono
        (Entails.trans (Entails.pure_right (fun (_ : lim ≠ zeroBudgetLimits) => hFr_sf) (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl)))
        hpost0
    · exact False.elim (not_satisfies_false_sepConj hpan')
    · exact False.elim (not_satisfies_false_sepConj hex')
    · refine Or.inr (Or.inr (Or.inr ⟨by rw [stripS_status_eq_local] at ho'; exact ho', ?_⟩))
      dsimp only [rustCliAllocBudgetSpecBase] at hoom' ⊢
      rw [oomPreserved_stripS_eq] at hoom'
      exact satisfies_of_stripExecOutside hFr_sf hoom'

private theorem f3Lo_allocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) f3LoRxProg f3StubAddrs :=
  fineHookRustCliAllocBudgetEntries_thunks
    (f3Lo_progContainsMallocng mmpl hMm) γ tp brkStart f3Lo_rustStdThunkCode
    (c2_mng_cAddrs_eq_local mmpl hMm ▸ f3Lo_rdlShims)
    (c2_memcpy_f3Lo_ok rfl (fun _ h => h) (fun _ _ => rfl))

theorem c2_alloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.alloc
      (rustCliAllocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim false) :=
  lift_allocBase_withExecFrozen_ok hMm γ tp brkStart f3StubAddrs.alloc false hlim hsvc hcl hext_lo
    ((f3Lo_allocEntries mmpl hMm γ tp brkStart).alloc lim)

theorem c2_allocZeroed_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAzAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  lift_allocBase_withExecFrozen_ok hMm γ tp brkStart f3StubAzAddr true hlim hsvc hcl hext_lo
    (fineHookRustCliAllocZeroedBudget_thunk_ok
      (f3Lo_progContainsMallocng mmpl hMm) γ tp brkStart f3StubAzAddr f3RdlAzAddr
      f3StdLayout.memsetAddr lim f3Lo_stubAz_hasInstrs
      (by
        rw [c2_mng_fnAddr_eq_local mmpl hMm, c2_mng_cAddrs_eq_local mmpl hMm]
        exact f3Lo_allocZeroedInstrs)
      (c2_memset_f3Lo_ok rfl (fun _ h => h) (fun _ _ => rfl)))

theorem c2_dealloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.dealloc
      (rustCliDeallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepLo_mallocng mmpl hMm
  refine lift_f3LoRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3Lo_allocEntries mmpl hMm γ tp brkStart).dealloc lim) ?_ ?_
  · rintro ⟨p, size, align, st⟩ R s0 hpreF
    dsimp only [rustCliDeallocBudgetSpecBase, withExecFrozenBudget] at hpreF
    have hRearr :
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
            (s0.readReg64 .x2).toNat = align⌝ ∗
          (A₀.pool lim st s0 ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝) ∗
          A₀.live p size align ∗ memRegion p size ∗ stackAt s0.sp allocHookStack) ∗ R =
        ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝ ∗
          ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
              (s0.readReg64 .x2).toNat = align⌝ ∗
            A₀.pool lim st s0 ∗ A₀.live p size align ∗ memRegion p size ∗
            stackAt s0.sp allocHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hRearr, satisfies_pure_sepConj] at hpreF
    rcases hpreF with ⟨himp, hpre0⟩
    have hFr0 : ExecFrozen s0.mem := himp hlim
    refine ⟨hFr0, ?_⟩
    have hsat := satisfies_stripExecOutside keepLo hpre0
    dsimp only [rustCliDeallocBudgetSpecBase]
    rw [stripS_r64_eq_local, stripS_r64_eq_local, stripS_r64_eq_local, stripS_sp_eq_local,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim st s0]
    exact hsat
  · rintro ⟨p, size, align, st⟩ R s0 sf hFr_sf hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨_, hoom'⟩
    · refine Or.inl ⟨by cases s0; cases sf; exact hret', by cases s0; cases sf; exact hcc', ?_⟩
      dsimp only [rustCliDeallocBudgetSpecBase] at hpost' ⊢
      rw [allocCallPreserved_stripS_eq, stripS_sp_eq_local,
        fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim _ sf] at hpost'
      have hpost0 : sf.mem ⊨
          (⌜AllocCallPreserved s0 sf ∧
              fineCostModel.liveBytes (fineCostModel.stepEvents (rustDeallocEvents size align) st) ≤
                fineCostModel.liveBytes st⌝ ∗
            A₀.pool lim (fineCostModel.stepEvents (rustDeallocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack) ∗ R :=
        satisfies_of_stripExecOutside hFr_sf hpost'
      dsimp only [withExecFrozenBudget]
      exact Satisfies.mono
        (Entails.trans (Entails.pure_right (fun (_ : lim ≠ zeroBudgetLimits) => hFr_sf) (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl)))
        hpost0
    · exact False.elim (not_satisfies_false_sepConj hpan')
    · exact False.elim (not_satisfies_false_sepConj hex')
    · exact False.elim (not_satisfies_false_sepConj hoom')

private theorem strip_countPerm_rw_local (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).countPerm (· == some Perm.rw) a n =
        m.countPerm (· == some Perm.rw) a n
  | _, 0 => rfl
  | a, n + 1 => by
    have hrw :
        ((stripExecOutside keep m).perm a == some Perm.rw) = (m.perm a == some Perm.rw) := by
      cases h1 : (stripExecOutside keep m).perm a == some Perm.rw <;>
        cases h2 : m.perm a == some Perm.rw
      · rfl
      · exfalso
        exact Bool.eq_false_iff.mp h1
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mpr (beq_iff_eq.mp h2)))
      · exfalso
        exact Bool.eq_false_iff.mp h2
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mp (beq_iff_eq.mp h1)))
      · rfl
    simp only [Memory.countPerm, hrw, strip_countPerm_rw_local keep m (a + 1#64) n]

private theorem fineHookNoAesRustCliAllocBudget_pool_stripS_local
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart).pool lim st (stripS keep s) =
      (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart).pool lim st s := by
  have hPermRX : CodeBlocksPermRX mmpl (stripS keep s) = CodeBlocksPermRX mmpl s := by
    apply propext
    unfold CodeBlocksPermRX CodeBlocksPermRXMem
    constructor <;> intro h a ha
    · have ha' := h a ha
      rwa [stripS_mem_eq_local, strip_perm_of_keep (hKeepMallocng a ha)] at ha'
    · rw [stripS_mem_eq_local, strip_perm_of_keep (hKeepMallocng a ha)]
      exact h a ha
  have hpma : (stripS keep s).physMemAvail = s.physMemAvail := by cases s; rfl
  have hbrks : (stripS keep s).brkStart = s.brkStart := by cases s; rfl
  have hbrk : (stripS keep s).brk = s.brk := by cases s; rfl
  have hrw : ProofLib.rwBytes (stripExecOutside keep s.mem) = ProofLib.rwBytes s.mem := by
    unfold ProofLib.rwBytes Memory.countRw
    exact strip_countPerm_rw_local keep s.mem 0#64 (2 ^ 64)
  have hphys : ProofLib.physPlusRw (stripS keep s) = ProofLib.physPlusRw s := by
    unfold ProofLib.physPlusRw
    simp only [hpma, stripS_mem_eq_local, hrw]
  have hcov : ∀ staticIvs ivs,
      StaticMappedCover lim staticIvs ivs (stripExecOutside keep s.mem) =
        StaticMappedCover lim staticIvs ivs s.mem := by
    intro staticIvs ivs
    apply propext
    unfold StaticMappedCover
    simp only [(strip_perm_props keep s.mem _).2.2.1]
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs (stripS keep s) =
        mallocngBudgetPoolInv lim staticIvs ivs s := by
    intro staticIvs ivs
    apply propext
    unfold mallocngBudgetPoolInv
    simp only [stripS_mem_eq_local, hcov, hphys]
  have hpool :
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st (stripS keep s) =
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st s := by
    unfold mallocngBudgetPoolAt LibsignalBinary.Heap.MallocngModelEnv
    simp only [hinv, hbrks, hbrk]
    cases s; rfl
  change mallocngLib.codeRO mmpl ∗
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st (stripS keep s) ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mmpl (stripS keep s)⌝ =
    mallocngLib.codeRO mmpl ∗
      mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
        tp brkStart lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝
  rw [hpool, hPermRX]

private theorem f3Lo_noAesAllocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart) f3LoRxProg f3StubAddrs :=
  fineHookNoAesRustCliAllocBudgetEntries_thunks
    (f3Lo_progContainsMallocng mmpl hMm) γ tp brkStart f3Lo_rustStdThunkCode
    (c2_mng_cAddrs_eq_local mmpl hMm ▸ f3Lo_rdlShims)
    (c2_memcpy_f3Lo_ok rfl (fun _ h => h) (fun _ _ => rfl))

theorem c2_allocZeroed_noAes_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAzAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepLo_mallocng mmpl hMm
  have hOk0 : subroutine_ok f3LoRxProg f3StubAzAddr
      (rustCliAllocBudgetSpecBase fineCostModel A₀ lim true) :=
    fineHookNoAesRustCliAllocZeroedBudget_thunk_ok
      (f3Lo_progContainsMallocng mmpl hMm) γ tp brkStart f3StubAzAddr f3RdlAzAddr
      f3StdLayout.memsetAddr lim f3Lo_stubAz_hasInstrs
      (by
        rw [c2_mng_fnAddr_eq_local mmpl hMm, c2_mng_cAddrs_eq_local mmpl hMm]
        exact f3Lo_allocZeroedInstrs)
      (c2_memset_f3Lo_ok rfl (fun _ h => h) (fun _ _ => rfl))
  change subroutine_ok P f3StubAzAddr
    (rustCliAllocBudgetSpecBase fineCostModel (withExecFrozenBudget A₀) lim true)
  refine lift_f3LoRxProg_subroutine_ok hsvc hcl hext_lo hOk0 ?_ ?_
  · rintro ⟨size, align, st⟩ R s0 hpreF
    dsimp only [rustCliAllocBudgetSpecBase, withExecFrozenBudget] at hpreF
    have hRearr :
        (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align⌝ ∗
          (A₀.pool lim st s0 ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝) ∗
          stackAt s0.sp allocHookStack) ∗ R =
        ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝ ∗
          ((⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
              RustLayoutOk size align⌝ ∗
            A₀.pool lim st s0 ∗ stackAt s0.sp allocHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hRearr, satisfies_pure_sepConj] at hpreF
    rcases hpreF with ⟨himp, hpre0⟩
    have hFr0 : ExecFrozen s0.mem := himp hlim
    refine ⟨hFr0, ?_⟩
    have hsat := satisfies_stripExecOutside keepLo hpre0
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [stripS_r64_eq_local, stripS_r64_eq_local, stripS_sp_eq_local,
      fineHookNoAesRustCliAllocBudget_pool_stripS_local γ mmpl tp brkStart hKeepM lim st s0]
    exact hsat
  · rintro ⟨size, align, st⟩ R s0 sf hFr_sf hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨by cases s0; cases sf; exact hret', by cases s0; cases sf; exact hcc', ?_⟩
      dsimp only [rustCliAllocBudgetSpecBase] at hpost' ⊢
      rw [stripS_r64_eq_local, allocCallPreserved_stripS_eq, stripS_sp_eq_local,
        fineHookNoAesRustCliAllocBudget_pool_stripS_local γ mmpl tp brkStart hKeepM lim _ sf] at hpost'
      have hpost0 : sf.mem ⊨
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A₀.pool lim
              (if sf.readReg64 .x0 = 0 then st
               else fineCostModel.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
             else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
               A₀.live (sf.readReg64 .x0) size align ∗
               (if true then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                else memRegion (sf.readReg64 .x0) size))) ∗ R :=
        satisfies_of_stripExecOutside hFr_sf hpost'
      dsimp only [withExecFrozenBudget]
      exact Satisfies.mono
        (Entails.trans (Entails.pure_right (fun (_ : lim ≠ zeroBudgetLimits) => hFr_sf) (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl)))
        hpost0
    · exact False.elim (not_satisfies_false_sepConj hpan')
    · exact False.elim (not_satisfies_false_sepConj hex')
    · refine Or.inr (Or.inr (Or.inr ⟨by rw [stripS_status_eq_local] at ho'; exact ho', ?_⟩))
      dsimp only [rustCliAllocBudgetSpecBase] at hoom' ⊢
      rw [oomPreserved_stripS_eq] at hoom'
      exact satisfies_of_stripExecOutside hFr_sf hoom'

theorem c2_dealloc_noAes_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.dealloc
      (rustCliDeallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepLo_mallocng mmpl hMm
  refine lift_f3LoRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3Lo_noAesAllocEntries mmpl hMm γ tp brkStart).dealloc lim) ?_ ?_
  · rintro ⟨p, size, align, st⟩ R s0 hpreF
    dsimp only [rustCliDeallocBudgetSpecBase, withExecFrozenBudget] at hpreF
    have hRearr :
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
            (s0.readReg64 .x2).toNat = align⌝ ∗
          (A₀.pool lim st s0 ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝) ∗
          A₀.live p size align ∗ memRegion p size ∗ stackAt s0.sp allocHookStack) ∗ R =
        ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝ ∗
          ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
              (s0.readReg64 .x2).toNat = align⌝ ∗
            A₀.pool lim st s0 ∗ A₀.live p size align ∗ memRegion p size ∗
            stackAt s0.sp allocHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hRearr, satisfies_pure_sepConj] at hpreF
    rcases hpreF with ⟨himp, hpre0⟩
    have hFr0 : ExecFrozen s0.mem := himp hlim
    refine ⟨hFr0, ?_⟩
    have hsat := satisfies_stripExecOutside keepLo hpre0
    dsimp only [rustCliDeallocBudgetSpecBase]
    rw [stripS_r64_eq_local, stripS_r64_eq_local, stripS_r64_eq_local, stripS_sp_eq_local,
      fineHookNoAesRustCliAllocBudget_pool_stripS_local γ mmpl tp brkStart hKeepM lim st s0]
    exact hsat
  · rintro ⟨p, size, align, st⟩ R s0 sf hFr_sf hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨_, hoom'⟩
    · refine Or.inl ⟨by cases s0; cases sf; exact hret', by cases s0; cases sf; exact hcc', ?_⟩
      dsimp only [rustCliDeallocBudgetSpecBase] at hpost' ⊢
      rw [allocCallPreserved_stripS_eq, stripS_sp_eq_local,
        fineHookNoAesRustCliAllocBudget_pool_stripS_local γ mmpl tp brkStart hKeepM lim _ sf] at hpost'
      have hpost0 : sf.mem ⊨
          (⌜AllocCallPreserved s0 sf ∧
              fineCostModel.liveBytes (fineCostModel.stepEvents (rustDeallocEvents size align) st) ≤
                fineCostModel.liveBytes st⌝ ∗
            A₀.pool lim (fineCostModel.stepEvents (rustDeallocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack) ∗ R :=
        satisfies_of_stripExecOutside hFr_sf hpost'
      dsimp only [withExecFrozenBudget]
      exact Satisfies.mono
        (Entails.trans (Entails.pure_right (fun (_ : lim ≠ zeroBudgetLimits) => hFr_sf) (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl)))
        hpost0
    · exact False.elim (not_satisfies_false_sepConj hpan')
    · exact False.elim (not_satisfies_false_sepConj hex')
    · exact False.elim (not_satisfies_false_sepConj hoom')

theorem c2_realloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.realloc
      (rustCliReallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepLo_mallocng mmpl hMm
  refine lift_f3LoRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3Lo_allocEntries mmpl hMm γ tp brkStart).realloc lim) ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 hpreF
    dsimp only [rustCliReallocBudgetSpecBase, withExecFrozenBudget] at hpreF
    have hRearr :
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
          (A₀.pool lim st s0 ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝) ∗
          A₀.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack) ∗ R =
        ⌜lim ≠ zeroBudgetLimits → ExecFrozen s0.mem⌝ ∗
          ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
              (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
              RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
            A₀.pool lim st s0 ∗ A₀.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackAt s0.sp allocHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hRearr, satisfies_pure_sepConj] at hpreF
    rcases hpreF with ⟨himp, hpre0⟩
    have hFr0 : ExecFrozen s0.mem := himp hlim
    refine ⟨hFr0, ?_⟩
    have hsat := satisfies_stripExecOutside keepLo hpre0
    dsimp only [rustCliReallocBudgetSpecBase]
    rw [stripS_r64_eq_local, stripS_r64_eq_local, stripS_r64_eq_local, stripS_r64_eq_local,
      stripS_sp_eq_local, fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim st s0]
    exact hsat
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hFr_sf hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨by cases s0; cases sf; exact hret', by cases s0; cases sf; exact hcc', ?_⟩
      dsimp only [rustCliReallocBudgetSpecBase] at hpost' ⊢
      rw [stripS_r64_eq_local, allocCallPreserved_stripS_eq, stripS_sp_eq_local,
        fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepM lim _ sf] at hpost'
      have hpost0 : sf.mem ⊨
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A₀.pool lim
              (if sf.readReg64 .x0 = 0 then st
               else fineCostModel.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (if sf.readReg64 .x0 = 0 then
              ⌜NullAllowed new align⌝ ∗ A₀.live p old align ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
             else
              ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
                A₀.live (sf.readReg64 .x0) new align ∗
                (sf.readReg64 .x0 ↦ₛ bs) ∗
                memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R :=
        satisfies_of_stripExecOutside hFr_sf hpost'
      dsimp only [withExecFrozenBudget]
      exact Satisfies.mono
        (Entails.trans (Entails.pure_right (fun (_ : lim ≠ zeroBudgetLimits) => hFr_sf) (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl)))
        hpost0
    · exact False.elim (not_satisfies_false_sepConj hpan')
    · exact False.elim (not_satisfies_false_sepConj hex')
    · refine Or.inr (Or.inr (Or.inr ⟨by rw [stripS_status_eq_local] at ho'; exact ho', ?_⟩))
      dsimp only [rustCliReallocBudgetSpecBase] at hoom' ⊢
      rw [oomPreserved_stripS_eq] at hoom'
      exact satisfies_of_stripExecOutside hFr_sf hoom'

theorem c2_rustBudgetAlloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.alloc
      (rustBudgetAllocSpec
        (toRustAllocBudget fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim)) :=
  rustBudgetAlloc_of_cliBase (c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim hsvc hcl hext_lo)

theorem c2_rustBudgetRealloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3LoRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepLo pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.realloc
      (rustBudgetReallocSpec
        (toRustAllocBudget fineCostModel
          (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim)) :=
  rustBudgetRealloc_of_cliBase (c2_realloc_withExecFrozen_ok hMm γ tp brkStart hlim hsvc hcl hext_lo)

/-! ## 4. Generic `avoidS5` Replay Combinators (`stubGuardedF3GhostRo_avoidS5`, `f3LinkedCallHook_avoidS5`) -/

private theorem subroutineStop_stripS_iff_local {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  cases s0; cases s; exact Iff.rfl

private theorem subroutineStop_stripS_setPC_local {keep : BitVec 64 → Bool}
    {u sf : State} {pc : BitVec 64}
    (h : SubroutineStop (stripS keep (u.setPC pc)) sf) : SubroutineStop u sf := by
  cases u; exact h

private theorem fetchMem_eq_of_externAt_eq {P1 P2 : Program} {m : Memory} {pc : BitVec 64}
    (hext : P1.externAt? pc = P2.externAt? pc) :
    P1.fetchMem m pc = P2.fetchMem m pc := by
  unfold Program.fetchMem
  rw [hext]

private theorem subroutineOutcome_to_stop_local {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨h1, _, _⟩ | ⟨h2, _⟩ | ⟨c, h3, _⟩ | ⟨h4, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h3⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

private theorem subroutineOutcome_not_halted_local {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
    (rw [hst]; nofun)

private theorem subroutineOutcome_not_exception_local {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) (msg : String) :
    sf.status ≠ .Exception msg := by
  rcases h with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
    (rw [hst]; nofun)

private theorem steps_untrap_avoidS5 {P_sub : Program} {sa' sf' : State}
    (hTrapNone : P_sub.externs s5TrapSym = none)
    (hsteps : Steps (addS5Trap P_sub) sa' sf')
    (hnoex : ∀ msg, sf'.status ≠ .Exception msg) :
    StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true) P_sub sa' sf' := by
  induction hsteps with
  | refl s => exact .refl s
  | @step sa' sb' sc' h1 hrest ih =>
    have hns5 : s5Addrs.contains sa'.pc = false := by
      cases hs5 : s5Addrs.contains sa'.pc
      · rfl
      · exfalso
        have he_trap := addS5Trap_externAt_s5 P_sub hs5
        cases h1 with
        | exec _ hfm =>
          unfold Program.fetchMem at hfm
          simp [he_trap] at hfm
        | halt_unmapped _ _ hext =>
          rw [he_trap] at hext; cases hext
        | extern _ he _ _ =>
          rw [he_trap] at he
          injection he with hf
          subst hf
          exact hnoex "hit S5" (steps_preserves_exception_local hrest rfl)
        | extern_fault _ _ _ =>
          exact hnoex _ (steps_preserves_exception_local hrest rfl)
    have hext_eq : (addS5Trap P_sub).externAt? sa'.pc = P_sub.externAt? sa'.pc :=
      addS5Trap_externAt_of_not_s5 P_sub hTrapNone hns5
    have hfm_eq : (addS5Trap P_sub).fetchMem sa'.mem sa'.pc = P_sub.fetchMem sa'.mem sa'.pc :=
      fetchMem_eq_of_externAt_eq hext_eq
    have hstep_sub : Step P_sub sa' sb' := by
      cases h1 with
      | @exec inst hr hfm =>
        exact Step.exec hr (hfm_eq.symm.trans hfm)
      | halt_unmapped hr hfm hext =>
        exact Step.halt_unmapped hr (hfm_eq.symm.trans hfm) (hext_eq.symm.trans hext)
      | extern hr he hkf hsym =>
        exact Step.extern hr (hext_eq.symm.trans he) hkf hsym
      | extern_fault hr he hbad =>
        exact Step.extern_fault hr (hext_eq.symm.trans he) hbad
    exact .step (by rw [hns5]; nofun) hstep_sub (ih hnoex)

private theorem stepsAvoidS5_of_stripS_with_externs
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P_real.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hsub_in_real : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P_real.externAt? pc = some f)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    {sa' sf' : State}
    (hsteps : StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true) P_sub sa' sf')
    (hstop' : SubroutineStop s0 sf') (hnhalt' : sf'.status ≠ .Halted) :
    ∀ sa : State, sa' = stripS keep sa → ExecFrozen sa.mem →
      ∃ sf : State,
        StepsUntil (externOnlyStdProg P_sub) (SubroutineStop s0) sa sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem ∧
        StepsStrictAvoid (fun z => s5Addrs.contains z.pc = true) P_real sa sf := by
  induction hsteps with
  | refl _ =>
    intro sa hsa hfra
    exact ⟨sa, .refl sa, subroutineStop_stripS_iff_local.mp (hsa ▸ hstop'), hsa, hfra, .refl sa⟩
  | @step sa' sb' sc' hns5' h1 hrest ih =>
    intro sa hsa hfra
    have hns5_sa : ¬ (s5Addrs.contains sa.pc = true) := by
      intro h; exact hns5' (by rwa [hsa, stripS_pc_eq_local])
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, stripS_pc_eq_local, stripS_mem_eq_local] at hfm'
          unfold Program.fetchMem at hfm'
          cases he : P_sub.externAt? sa.pc with
          | some f => simp [he] at hfm'
          | none =>
            simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
            by_cases hal : sa.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
              by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
              · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                  have h4 :
                      ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                      ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                    simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                  exact h4.1
                have hkp := (strip_perm_x_imp hx0).2
                rw [hpc_lr, hlr_out] at hkp; cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (steps_preserves_halted_local hrest.toSteps rfl))
        | extern _ he _ _ =>
          rw [hsa, stripS_pc_eq_local] at he; exact False.elim (hlr_ne sa.pc _ he hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, stripS_pc_eq_local] at he; exact False.elim (hlr_ne sa.pc _ he hpc_lr)
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running_local h1; rwa [hsa, stripS_status_eq_local] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running_local h1; rwa [hsa, stripS_status_eq_local] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running_local h1; rwa [hsa, stripS_status_eq_local] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (steps_preserves_halted_local hrest.toSteps rfl))
      | extern_fault _ _ _ =>
        have hsf_ex := steps_preserves_exception_local hrest.toSteps rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @extern f hr' he' hkf' hsym' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status_eq_local] at hr'; exact hr'
        rw [hsa, stripS_pc_eq_local] at he'
        rw [hsa] at hkf' hsym'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hcomm sa.pc f he' sa hfra hkf' hsym'
        have he_ext : (externOnlyStdProg P_sub).externAt? sa.pc = some f := by
          rw [externOnlyStdProg_externAt]; exact he'
        have hstep_ext : Step (externOnlyStdProg P_sub) sa (f sa) :=
          Step.extern hra he_ext hkf_f hsym_f
        have hstep_real : Step P_real sa (f sa) :=
          Step.extern hra (hsub_in_real sa.pc f he') hkf_f hsym_f
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, havoid_rest⟩ :=
          ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, .step hstop_sa hstep_ext huntil_rest, hstop_sf, hsf_eq, hfr_sf,
          .step hns5_sa hstep_real havoid_rest⟩
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status_eq_local] at hr'; exact hr'
        rw [hsa, stripS_pc_eq_local, stripS_mem_eq_local] at hfm'
        unfold Program.fetchMem at hfm'
        cases he_sub : P_sub.externAt? sa.pc with
        | some f => simp [he_sub] at hfm'
        | none =>
          simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal_pc : sa.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
              have hx4 :
                  ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
                simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
              obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
              obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
              obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
              obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
              have hce : sa.mem.canExec sa.pc 4 = true := by
                simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
              rw [strip_read32_eq_local] at hfm'
              have hext_ext : (externOnlyStdProg P_sub).externAt? sa.pc = none := by
                rw [externOnlyStdProg_externAt]; exact he_sub
              have hext_real : P_real.externAt? sa.pc = none := hreal_no sa.pc hkp0 he_sub
              have hfm_ext : (externOnlyStdProg P_sub).fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem; simp [hext_ext, hal_pc, hce, hfm']
              have hfm_real : P_real.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem; simp [hext_real, hal_pc, hce, hfm']
              by_cases hsvc0 : inst.isSvc0 = true
              · have hinst : inst = .system false 0#16 := by
                  cases inst <;> simp [Instr.isSvc0] at hsvc0
                  rcases hsvc0 with ⟨rfl, rfl⟩; rfl
                subst hinst
                obtain ⟨hcomm_svc, hfr_sb⟩ := standard_stripS (keep := keep) hfra
                have hev_strip :
                    P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                      stripS keep (Syscall.standard sa) := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm_svc]
                have hev_ext :
                    (externOnlyStdProg P_sub).evalInst (.system false 0#16) sa =
                      Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, externOnlyStdProg_svc]
                have hev_real :
                    P_real.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_real]
                have hstep_ext : Step (externOnlyStdProg P_sub) sa (Syscall.standard sa) :=
                  hev_ext ▸ Step.exec hra hfm_ext
                have hstep_real : Step P_real sa (Syscall.standard sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, havoid_rest⟩ :=
                  ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, .step hstop_sa hstep_ext huntil_rest, hstop_sf, hsf_eq, hfr_sf,
                  .step hns5_sa hstep_real havoid_rest⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hev_strip :
                    P_sub.evalInst inst (stripS keep sa) = stripS keep (execInst inst sa) := by
                  rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0, execInst_stripS hnsvc0]
                have hev_ext : (externOnlyStdProg P_sub).evalInst inst sa = execInst inst sa :=
                  evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 sa
                have hev_real : P_real.evalInst inst sa = execInst inst sa :=
                  evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 sa
                have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
                have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                  ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
                have hstep_ext : Step (externOnlyStdProg P_sub) sa (execInst inst sa) :=
                  hev_ext ▸ Step.exec hra hfm_ext
                have hstep_real : Step P_real sa (execInst inst sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, havoid_rest⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, .step hstop_sa hstep_ext huntil_rest, hstop_sf, hsf_eq, hfr_sf,
                  .step hns5_sa hstep_real havoid_rest⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

private theorem outcome_lift_of_stripS {α : Type} {keep : BitVec 64 → Bool} {spec : Spec α}
    (hInv : SpecStripSInvariant keep spec)
    {x : α} {R : SepProp} {s1 sf : State} (hfr_sf : ExecFrozen sf.mem)
    (hout' : SubroutineOutcome spec x R (stripS keep s1) (stripS keep sf)) :
    SubroutineOutcome spec x R s1 sf := by
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
  · refine Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, ?_, ?_⟩
    · cases s1; cases sf; exact hcc'
    · rw [hInv.post_eq x s1 sf] at hpost'
      exact satisfies_of_stripExecOutside hfr_sf hpost'
  · refine Or.inr (Or.inl ⟨hp', ?_⟩)
    rw [hInv.onPanic_eq x s1 sf] at hpan'
    exact satisfies_of_stripExecOutside hfr_sf hpan'
  · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
    rw [hInv.onExit_eq x c s1 sf] at hex'
    exact satisfies_of_stripExecOutside hfr_sf hex'
  · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
    rw [hInv.onOom_eq x s1 sf] at hoom'
    exact satisfies_of_stripExecOutside hfr_sf hoom'

theorem stubGuardedF3GhostRo_avoidS5 {α : Type}
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {sym : String} {keep : BitVec 64 → Bool} {roGuard : Memory → Prop}
    {P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hTrapNone : P_sub.externs s5TrapSym = none)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (_hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hRoStrip : ∀ m : Memory, roGuard m → roGuard (stripExecOutside keep m))
    (hOkTrap : ∀ γ tp, subroutine_ok (addS5Trap P_sub) entryTarget
      (withExecFrozenSpec (withRoMemGuard roGuard (specOf γ tp))))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTraceExact (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hlr_out_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) → keep (u.readReg64 .lr) = false)
    (hlr_ne_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubAvoid : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl sym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (u.setPC entryTarget))
    (hInvSF : ∀ u : State, InvS u →
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon.stubFrozenGuard P_sub u)
    (hInvRo : ∀ u : State, ExecFrozen u.mem → InvS u → roGuard u.mem)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    {W : CliHooks} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem) (hinv : InvS u) :
    StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u) := by
  classical
  have hSF :
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon.stubFrozenGuard P_sub u :=
    hInvSF u hinv
  have hRo : roGuard u.mem := hInvRo u hfr hinv
  have hG :
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon.stubFrozenGuard P_sub u ∧
        roGuard u.mem := ⟨hSF, hRo⟩
  have hEq :
      stubGuardedF3GhostRo keep roGuard P_sub entryTarget specOf fallback u =
        f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u := by
    unfold stubGuardedF3GhostRo; simp only [hG, and_self, ↓reduceIte]
  rw [hEq] at hnoex ⊢
  obtain ⟨_, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHookExact_activeF3CallPre_of_noException hnoex
  have hActPre :
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostCommon.ActiveF3CallPre specOf u :=
    ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hlr_out : keep (u.readReg64 .lr) = false := hlr_out_pre γ tp x R u hpre
  have hlr_ne := hlr_ne_pre γ tp x R u hpre
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvCode u hfr hinv
  let s1 := u.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ (specOf γ tp).pre x s1 ∗ R := by
    change u.mem ⊨ (specOf γ tp).pre x (u.setPC entryTarget) ∗ R
    rwa [hPrePC γ tp x u entryTarget]
  have hs1'_pre : s1'.mem ⊨ (specOf γ tp).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← (hInv γ tp).pre_eq x s1] at hsat
  have hs1'_pre_full :
      s1'.mem ⊨ (withExecFrozenSpec (withRoMemGuard roGuard (specOf γ tp))).pre x s1' ∗ R := by
    dsimp only [withExecFrozenSpec, withRoMemGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨execFrozen_stripExecOutside hfr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hRoStrip u.mem hRo, hs1'_pre⟩
  have hCodeTrap : (addS5Trap P_sub).CodeLoaded s1'.mem :=
    (addS5Trap_codeLoaded_iff P_sub _).mpr hCodeSub
  obtain ⟨sf', hsteps_trap, hout'⟩ :=
    subroutine_ok_elim_steps_outcome (hOkTrap γ tp) x R s1' rfl hrun hs1'_pre_full hsp hCodeTrap
  have hout_base : SubroutineOutcome (specOf γ tp) x R s1' sf' := hout'
  have hnoex_sf' : ∀ msg, sf'.status ≠ .Exception msg :=
    subroutineOutcome_not_exception_local hout_base
  have hstop0' : SubroutineStop u sf' :=
    subroutineStop_stripS_setPC_local (subroutineOutcome_to_stop_local hout_base)
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted_local hout_base
  have havoid_sub := steps_untrap_avoidS5 hTrapNone hsteps_trap hnoex_sf'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, havoid_real⟩ :=
    stepsAvoidS5_of_stripS_with_externs
      (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (s0 := u) (hRealSvc W) hsvc_sub (fun pc hk _ => hRealNoExt W pc hk) hcomm
      (hSubExtInReal W) hlr_out hlr_ne havoid_sub hstop0' hnhalt' s1 rfl hfr
  rw [hsf_eq] at hout_base
  have hout1 : SubroutineOutcome (specOf γ tp) x R s1 sf :=
    outcome_lift_of_stripS (hInv γ tp) hfr_sf hout_base
  have hout0 : SubroutineOutcome (specOf γ tp) x R u sf :=
    hOutPC γ tp x R u sf entryTarget hout1
  obtain ⟨hfs_sf, htr_sf⟩ := hFsT γ tp x R u sf hout0
  have hReal : ActiveRealRunExact keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hfr, hlr_out, hCodeSub, sf, huntil, hstop_sf, hfs_sf, htr_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHookExact keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHookExact
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil hstop_sf
  rw [hhook_eq]
  refine (hStubAvoid W u hpc hrun hfr hinv).trans (havoid_real.mono_bad fun z hz => ?_)
  rwa [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hz

private theorem f3LinkedCallHook_activeF3CallPre_of_noException_local {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status ≠ .Exception msg) :
    ActiveF3CallPre specOf u := by
  classical
  by_contra hnot
  have hex :
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status =
        .Exception "ghost-hook precondition violated" := by
    unfold f3LinkedCallHook
    simp only [hnot, ↓reduceDIte]
  exact hnoex _ hex

theorem f3LinkedCallHook_avoidS5 {α : Type}
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {sym : String} {keep : BitVec 64 → Bool}
    {P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hTrapNone : P_sub.externs s5TrapSym = none)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOkTrap : ∀ γ tp, subroutine_ok (addS5Trap P_sub) entryTarget
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withStubPermRO P_sub
        (withExecFrozenSpec (specOf γ tp))))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hlr_out_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) → keep (u.readReg64 .lr) = false)
    (hlr_ne_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubAvoid : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl sym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (u.setPC entryTarget))
    (hInvSF : ∀ u : State, InvS u →
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.stubFrozenGuard P_sub u)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    {W : CliHooks} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem) (hinv : InvS u) :
    StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) := by
  classical
  have hSF :
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.stubFrozenGuard P_sub u :=
    hInvSF u hinv
  obtain ⟨_, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHook_activeF3CallPre_of_noException_local hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hlr_out : keep (u.readReg64 .lr) = false := hlr_out_pre γ tp x R u hpre
  have hlr_ne := hlr_ne_pre γ tp x R u hpre
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvCode u hfr hinv
  let s1 := u.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ (specOf γ tp).pre x s1 ∗ R := by
    change u.mem ⊨ (specOf γ tp).pre x (u.setPC entryTarget) ∗ R
    rwa [hPrePC γ tp x u entryTarget]
  have hs1'_pre : s1'.mem ⊨ (specOf γ tp).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← (hInv γ tp).pre_eq x s1] at hsat
  have hro_stub : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.stubPermRO_stripExecOutside_of_stubFrozen
      hSF
  have hs1'_pre_full :
      s1'.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withStubPermRO P_sub
          (withExecFrozenSpec (specOf γ tp))).pre x s1' ∗ R := by
    dsimp only [
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withStubPermRO,
      withExecFrozenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_stub, execFrozen_stripExecOutside hfr⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨execFrozen_stripExecOutside hfr, hs1'_pre⟩
  have hCodeTrap : (addS5Trap P_sub).CodeLoaded s1'.mem :=
    (addS5Trap_codeLoaded_iff P_sub _).mpr hCodeSub
  obtain ⟨sf', hsteps_trap, hout'⟩ :=
    subroutine_ok_elim_steps_outcome (hOkTrap γ tp) x R s1' rfl hrun hs1'_pre_full hsp hCodeTrap
  have hout_base : SubroutineOutcome (specOf γ tp) x R s1' sf' := hout'
  have hnoex_sf' : ∀ msg, sf'.status ≠ .Exception msg :=
    subroutineOutcome_not_exception_local hout_base
  have hstop0' : SubroutineStop u sf' :=
    subroutineStop_stripS_setPC_local (subroutineOutcome_to_stop_local hout_base)
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted_local hout_base
  have havoid_sub := steps_untrap_avoidS5 hTrapNone hsteps_trap hnoex_sf'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, havoid_real⟩ :=
    stepsAvoidS5_of_stripS_with_externs
      (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (s0 := u) (hRealSvc W) hsvc_sub (hRealNoExt W) hcomm
      (hSubExtInReal W) hlr_out hlr_ne havoid_sub hstop0' hnhalt' s1 rfl hfr
  rw [hsf_eq] at hout_base
  have hout1 : SubroutineOutcome (specOf γ tp) x R s1 sf :=
    outcome_lift_of_stripS (hInv γ tp) hfr_sf hout_base
  have hout0 : SubroutineOutcome (specOf γ tp) x R u sf :=
    hOutPC γ tp x R u sf entryTarget hout1
  obtain ⟨hfs_sf, hfst_sf⟩ := hFsT γ tp x R u sf hout0
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hfr, hlr_out, hCodeSub, sf, huntil, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil hstop_sf
  rw [hhook_eq]
  refine (hStubAvoid W u hpc hrun hfr hinv).trans (havoid_real.mono_bad fun z hz => ?_)
  rwa [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hz

theorem f3LinkedCallHook_aesStubRcon_avoidS5 {α : Type}
    {mpl mmpl : MultiPlacement} {InvS : State → Prop}
    {sym : String} {keep : BitVec 64 → Bool}
    {P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {fallback : State → State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hTrapNone : P_sub.externs s5TrapSym = none)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOkTrap : ∀ γ tp, subroutine_ok (addS5Trap P_sub) entryTarget
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withAesStubRconRO P_sub
        (withExecFrozenSpec (specOf γ tp))))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hlr_out_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) → keep (u.readReg64 .lr) = false)
    (hlr_ne_pre : ∀ γ tp x (R : SepProp) (u : State),
      (u.mem ⊨ (specOf γ tp).pre x u ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hRealSvc : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard)
    (hRealNoExt : ∀ (W : CliHooks) (pc : BitVec 64), keep pc = true →
      P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hSubExtInReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hStubAvoid : ∀ (W : CliHooks) (u : State),
      u.pc = libsignalSessionLib.resolve mpl sym → u.status = .Running →
      ExecFrozen u.mem → InvS u →
      StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (u.setPC entryTarget))
    (hInvSF : ∀ u : State, InvS u →
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.stubFrozenGuard P_sub u)
    (hInvRcon : ∀ u : State, InvS u →
      RoDataAt u.mem
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.c2AesRconAddr
        aesRconBytes)
    (hInvCode : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    {W : CliHooks} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hfr : ExecFrozen u.mem) (hinv : InvS u) :
    StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) := by
  classical
  have hSF := hInvSF u hinv
  have hRcon := hInvRcon u hinv
  obtain ⟨_, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHook_activeF3CallPre_of_noException_local hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hlr_out : keep (u.readReg64 .lr) = false := hlr_out_pre γ tp x R u hpre
  have hlr_ne := hlr_ne_pre γ tp x R u hpre
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvCode u hfr hinv
  let s1 := u.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ (specOf γ tp).pre x s1 ∗ R := by
    change u.mem ⊨ (specOf γ tp).pre x (u.setPC entryTarget) ∗ R
    rwa [hPrePC γ tp x u entryTarget]
  have hs1'_pre : s1'.mem ⊨ (specOf γ tp).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← (hInv γ tp).pre_eq x s1] at hsat
  have hro_stub : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.stubPermRO_stripExecOutside_of_stubFrozen
      hSF
  have hro_rcon : RoDataAt s1'.mem
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.c2AesRconAddr
      aesRconBytes :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.roDataAt_stripExecOutside
      keep hRcon
  have hs1'_pre_full :
      s1'.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withAesStubRconRO P_sub
          (withExecFrozenSpec (specOf γ tp))).pre x s1' ∗ R := by
    dsimp only [
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withAesStubRconRO,
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays.withStubPermRO,
      withRoData, withExecFrozenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_stub, execFrozen_stripExecOutside hfr⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro_rcon, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨execFrozen_stripExecOutside hfr, hs1'_pre⟩
  have hCodeTrap : (addS5Trap P_sub).CodeLoaded s1'.mem :=
    (addS5Trap_codeLoaded_iff P_sub _).mpr hCodeSub
  obtain ⟨sf', hsteps_trap, hout'⟩ :=
    subroutine_ok_elim_steps_outcome (hOkTrap γ tp) x R s1' rfl hrun hs1'_pre_full hsp hCodeTrap
  have hout_base : SubroutineOutcome (specOf γ tp) x R s1' sf' := hout'
  have hnoex_sf' : ∀ msg, sf'.status ≠ .Exception msg :=
    subroutineOutcome_not_exception_local hout_base
  have hstop0' : SubroutineStop u sf' :=
    subroutineStop_stripS_setPC_local (subroutineOutcome_to_stop_local hout_base)
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted_local hout_base
  have havoid_sub := steps_untrap_avoidS5 hTrapNone hsteps_trap hnoex_sf'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, havoid_real⟩ :=
    stepsAvoidS5_of_stripS_with_externs
      (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (s0 := u) (hRealSvc W) hsvc_sub (hRealNoExt W) hcomm
      (hSubExtInReal W) hlr_out hlr_ne havoid_sub hstop0' hnhalt' s1 rfl hfr
  rw [hsf_eq] at hout_base
  have hout1 : SubroutineOutcome (specOf γ tp) x R s1 sf :=
    outcome_lift_of_stripS (hInv γ tp) hfr_sf hout_base
  have hout0 : SubroutineOutcome (specOf γ tp) x R u sf :=
    hOutPC γ tp x R u sf entryTarget hout1
  obtain ⟨hfs_sf, hfst_sf⟩ := hFsT γ tp x R u sf hout0
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hfr, hlr_out, hCodeSub, sf, huntil, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    exact h2fsgen_stepsUntil_det (Classical.choose_spec hReal.2.2.2).1
      (Classical.choose_spec hReal.2.2.2).2.1 huntil hstop_sf
  rw [hhook_eq]
  refine (hStubAvoid W u hpc hrun hfr hinv).trans (havoid_real.mono_bad fun z hz => ?_)
  rwa [s5Addrs_eq_of_linkedAt hLs, ← List.contains_iff_mem] at hz

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWide
