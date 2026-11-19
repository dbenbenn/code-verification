/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocZeroedHelpersFine -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.HookDischarge.Libc.Memset
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Pre-Panic `f3PrePanicRxProg` & `withExecFrozenBudget` Allocator Lifters (`C2RowLayoutFacts.PrePanicMngLift`)

Lifts the `mallocng` + `rdl_shim` Rust allocator contracts (`alloc`, `dealloc`, `realloc`,
`alloc_zeroed`, and the AES-split `noAes` variants) from the hook-free pre-panic prefix
`f3PrePanicRxProg` (`[0x474000, 0x479798)`) onto any `Syscall.standard` program `P` loading
`f3PrePanicRxProg` with no externs in `keepPrePanic` (including `aesCbcSubProg`,
`libcruxHmacSubProg`, and `c2FmtProgTrap lr`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open ProofLib.StdStartup (checkWordsAt evalInst_eq_execInst_of_not_isSvc0 hasInstrs hasWords_of_wordTree)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs
  (ProgContainsMallocng ProgContainsMultiLib memRegion_entails_exists_pointsToBytes
   memcpySymWords memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_ok)
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (cliElfBytes)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv FitsEvents
   NullAllowed OomPreserved RustCliAllocBudget RustCliAllocBudgetEntriesBase RustLayoutOk
   StaticMappedCover allocMemcpyVmSpec mallocngBudgetPool mallocngBudgetPoolAt
   mallocngBudgetPoolInv rustAllocEvents rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase
   rustCliReallocBudgetSpecBase rustDeallocEvents rustReallocEvents zeroBudgetLimits)
open LibsignalBinary.Heap.Fine
  (allocMemsetVmSpec f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3RxWordCount
   f3StdLayout f3StubAddrs f3StubAzAddr fineCostModel fineCostModelIface rdlAllocZeroedInstrs)
open LibsignalBinary.Heap.MuslMemOpsRunsTo
  (BlockExternFree codeLoaded_pureWordsProg_of_hasWords
   subroutine_ok_lift_pureWords_blockExternFree)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (PoolMemTransport)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
  (PoolAesInitSplit fineHookNoAesRustCliAllocBudget fineHookNoAesRustCliAllocBudgetEntries_thunks
   fineHookNoAesRustCliAllocZeroedBudget_thunk_ok instPoolAesInitSplitFineHook)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDecrypt (rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX CodeBlocksPermRXMem fineHookRustCliAllocBudget mallocngHookBudgetPool
   mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memset (memset_memsetRegionSpec_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen satisfies_of_stripExecOutside satisfies_stripExecOutside standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique f3TrialElf
   f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_stubs
   f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size f3Trial_progContainsMallocng f3Trial_rustStdThunkCode
   f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs)

/-! ## 1. Hook-Free Pre-Panic RX Prefix (`f3PrePanicRxProg`, `[0x474000, 0x479798)`) -/

/-- Word count (`5606` words = `0x5798` B) covering `.text.b_pre`, `memcpy`, `memset`, `mallocng`,
    and the `seg[2]` Rust allocator thunks/shims strictly below `.text.lib2` (`0x479798`). -/
@[expose] def f3PrePanicWordCount : Nat := 0x15e6

/-- Pre-panic prefix of `f3TrialRxProg` (`[f3RxSegBase, f3RxSegBase + 4 * f3PrePanicWordCount)`),
    with `svc = Syscall.standard` and zero externs/stubs. -/
noncomputable def f3PrePanicRxProg : Program :=
  { base := f3RxSegBase
    code := f3TrialRxProg.code.take (4 * f3PrePanicWordCount)
    svc := Syscall.standard }

/-- Half-open interval `[f3RxSegBase, f3RxSegBase + 4 * f3PrePanicWordCount)` matching
    `f3PrePanicRxProg`. -/
@[expose] def keepPrePanic (pc : BitVec 64) : Bool :=
  decide ((pc - f3RxSegBase).toNat < 4 * f3PrePanicWordCount)

private theorem f3PrePanicRxProg_base : f3PrePanicRxProg.base = f3RxSegBase := rfl

private theorem f3PrePanicRxProg_code :
    f3PrePanicRxProg.code = f3TrialRxProg.code.take (4 * f3PrePanicWordCount) := rfl

private theorem f3PrePanicRxProg_hookFree (off len : Nat) : f3PrePanicRxProg.hookFree off len :=
  ⟨rfl, rfl⟩

private theorem f3TrialRxProg_code_len :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

private theorem f3PrePanicRxProg_code_len :
    f3PrePanicRxProg.code.length = 4 * f3PrePanicWordCount := by
  rw [f3PrePanicRxProg_code, List.length_take, f3TrialRxProg_code_len]
  have hle : 4 * f3PrePanicWordCount ≤ 4 * f3RxWordCount := by decide
  exact Nat.min_eq_left hle

private theorem f3PrePanicRxProg_no_ext (pc : BitVec 64) :
    f3PrePanicRxProg.externAt? pc = none := rfl

private theorem list_getElem_of_eq_take {α : Type} {xs ys : List α} {n i : Nat}
    (h : xs = ys.take n) (hi : i < xs.length) (hi_ys : i < ys.length) :
    xs[i]'hi = ys[i]'hi_ys := by
  subst h
  exact List.getElem_take

theorem f3PrePanicRxProg_codeLoaded_of_f3Trial {m : Memory}
    (hcl : f3TrialRxProg.CodeLoaded m) :
    f3PrePanicRxProg.CodeLoaded m := by
  have hlen_le : f3PrePanicRxProg.code.length ≤ f3TrialRxProg.code.length := by
    rw [f3PrePanicRxProg_code_len, f3TrialRxProg_code_len]
    decide
  have hbase : f3PrePanicRxProg.base = f3TrialRxProg.base := f3TrialRxProg_base.symm
  refine Program.CodeLoaded.intro (hbase ▸ hcl.aligned)
    (Nat.le_trans (by rw [hbase]; omega) hcl.no_wrap) fun i hi => ?_
  have hi_full : i < f3TrialRxProg.code.length := Nat.lt_of_lt_of_le hi hlen_le
  rw [hbase]
  have hbyte : f3PrePanicRxProg.code[i]'hi = f3TrialRxProg.code[i]'hi_full :=
    list_getElem_of_eq_take f3PrePanicRxProg_code hi hi_full
  exact ⟨(hcl.byte_eq i hi_full).trans hbyte.symm, hcl.perm_eq i hi_full,
    hcl.isLazyFree_eq i hi_full⟩

private theorem f3PrePanicRxProg_read8_eq_of_codeLoaded {m1 m2 : Memory}
    (hLo : f3PrePanicRxProg.CodeLoaded m1) (hFull : f3TrialRxProg.CodeLoaded m2)
    (off : Nat) (hoff_lt : off < f3PrePanicRxProg.code.length)
    (hoff_full : off < f3TrialRxProg.code.length) :
    m1.read8 (f3PrePanicRxProg.base + BitVec.ofNat 64 off) =
      m2.read8 (f3TrialRxProg.base + BitVec.ofNat 64 off) := by
  have hbyte : f3PrePanicRxProg.code[off]'hoff_lt = f3TrialRxProg.code[off]'hoff_full :=
    list_getElem_of_eq_take f3PrePanicRxProg_code hoff_lt hoff_full
  exact (hLo.byte_eq off hoff_lt).trans (hbyte.trans (hFull.byte_eq off hoff_full).symm)

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

private theorem f3PrePanicRxProg_readWordOff_eq {off : Nat}
    (hbnd : off + 4 ≤ 4 * f3PrePanicWordCount) :
    f3PrePanicRxProg.readWordOff off = f3TrialRxProg.readWordOff off := by
  unfold Program.readWordOff
  by_cases hmod : off % 4 ≠ 0
  · simp [hmod]
  · simp only [hmod, ↓reduceIte, f3PrePanicRxProg_code]
    exact take_drop_prefix_four f3TrialRxProg.code hbnd

private theorem f3PrePanic_hasWords_of_f3Trial {addr : BitVec 64} {words : List (BitVec 32)}
    (hw : f3TrialRxProg.hasWords addr words)
    (hfit : (addr - f3RxSegBase).toNat + 4 * words.length ≤ 4 * f3PrePanicWordCount) :
    f3PrePanicRxProg.hasWords addr words := by
  unfold Program.hasWords Program.hasWordsOff at hw ⊢
  rw [f3TrialRxProg_base] at hw
  rw [f3PrePanicRxProg_base]
  refine ⟨hw.1, fun i hi => ?_, f3PrePanicRxProg_hookFree _ _⟩
  rw [← hw.2.1 i hi]
  exact f3PrePanicRxProg_readWordOff_eq (by omega)

private theorem f3PrePanic_hasInstrs_of_f3Trial {addr : BitVec 64} {instrs : List Instr}
    (hi : hasInstrs f3TrialRxProg addr instrs)
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + 4 * instrs.length ≤ f3RxSegBase.toNat + 4 * f3PrePanicWordCount) :
    hasInstrs f3PrePanicRxProg addr instrs := by
  intro k hk
  have hprev := hi k hk
  unfold Program.fetch at hprev ⊢
  have hext_lo : (f3PrePanicRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k))).isSome = false := rfl
  have hext_tr : (f3TrialRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k))).isSome = false := by
    have he : f3TrialRxProg.externAt? (addr + BitVec.ofNat 64 (4 * k)) = none :=
      f3TrialRxProg_no_ext _
    simp [he]
  rw [hext_lo]
  rw [hext_tr] at hprev
  simp only [Bool.false_eq_true, ↓reduceIte] at hprev ⊢
  have hbase : f3PrePanicRxProg.base = f3RxSegBase := rfl
  rw [hbase]
  rw [f3TrialRxProg_base] at hprev
  have htop : f3RxSegBase.toNat + 4 * f3PrePanicWordCount < 2 ^ 64 := by decide
  have hk64 : 4 * k < 2 ^ 64 := by omega
  have hpc_nat : (addr + BitVec.ofNat 64 (4 * k)).toNat = addr.toNat + 4 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (by omega)]
  have hoff_nat : ((addr + BitVec.ofNat 64 (4 * k)) - f3RxSegBase).toNat =
      addr.toNat + 4 * k - f3RxSegBase.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hpc_nat]
  rw [f3PrePanicRxProg_readWordOff_eq (by omega)]
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

theorem f3PrePanic_memcpy_hasWords :
    f3PrePanicRxProg.hasWords f3StdLayout.memcpyAddr memcpySymWords := by
  have hlen : 4 * memcpySymWords.length = 396 := by rfl_kernel
  exact f3PrePanic_hasWords_of_f3Trial f3Trial_memcpy_hasWords_local (by rw [hlen]; decide)

private theorem f3Trial_memset_hasWords_local :
    f3TrialRxProg.hasWords f3StdLayout.memsetAddr memsetWords := by
  have hoff_lt : (f3StdLayout.memsetAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memsetWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memsetWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memsetAddr - f3RxSegBase).toNat memsetWords = true)

theorem f3PrePanic_memset_hasWords :
    f3PrePanicRxProg.hasWords f3StdLayout.memsetAddr memsetWords := by
  have hlen : 4 * memsetWords.length = 260 := by rfl_kernel
  exact f3PrePanic_hasWords_of_f3Trial f3Trial_memset_hasWords_local (by rw [hlen]; decide)

private theorem c2_mng_placeable_local (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

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

private theorem c2_progContainsMallocng_f3Trial_local (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := c2_mng_placeable_local mmpl hMm
  have hIn1 := c2_mng_inElf_local mmpl hMm
  have hPl2 := mallocngLib_in_f3TrialElf.1
  have hIn2 := mallocngLib_in_f3TrialElf.2.1
  have hF3 := f3Trial_progContainsMallocng
  refine ProgContainsMultiLib.of_noExterns hPl1 f3TrialRxProg_svc
    (fun m hPm i hi => ?_) f3TrialRxProg_no_ext
  have hcl_f3 := hF3.codeLoaded m hPm i hi
  have hbase_i : mmpl.base i = f3MallocngMpl.base i :=
    (f3CliElf_mallocng_linkedAt_unique hMm).1 i hi
  have hbase_prog : (mallocngLib.blockProgram mmpl i).base =
      (mallocngLib.blockProgram f3MallocngMpl i).base := hbase_i
  have hcode_mmpl : (mallocngLib.blockProgram mmpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hcode_f3 : (mallocngLib.blockProgram f3MallocngMpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement f3MallocngMpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hlen1 : (mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hlen2 : (mallocngLib.blocks[i].patched
      (mallocngLib.blockPlacement f3MallocngMpl i)).length =
      mallocngLib.blocks[i].code.length :=
    CodeBlock.length_patched_of_aligned _ (hPl2.blocks_ok i hi).len_aligned
  have hcode_prog : (mallocngLib.blockProgram mmpl i).code =
      (mallocngLib.blockProgram f3MallocngMpl i).code := by
    rw [hcode_mmpl, hcode_f3]
    refine List.ext_getElem (hlen1.trans hlen2.symm) (fun k hk1 hk2 => ?_)
    obtain ⟨_, hc1, _⟩ := hIn1.blocks i hi k hk1
    obtain ⟨_, hc2, _⟩ := hIn2.blocks i hi k hk2
    rw [hbase_i] at hc1
    exact (Prod.mk.inj (Option.some.inj (hc1.symm.trans hc2))).2
  rw [Program.codeLoaded_iff] at hcl_f3 ⊢
  rwa [hbase_prog, hcode_prog]

theorem c2_keepPrePanic_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → keepPrePanic a = true := by
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
        ((c2_mng_placeable_local mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, _, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable_local mmpl hMm) (c2_mng_inElf_local mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hhi_lo : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3PrePanicWordCount := by decide
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have htop : f3RxSegBase.toNat + 4 * f3PrePanicWordCount < 2 ^ 64 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    unfold keepPrePanic
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    exact decide_eq_true (by omega)

theorem f3PrePanic_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3PrePanicRxProg mmpl := by
  have hPl1 := c2_mng_placeable_local mmpl hMm
  have hIn1 := c2_mng_inElf_local mmpl hMm
  have hal_trial : f3TrialRxProg.base.toNat % 4 = 0 := by
    rw [f3TrialRxProg_base]; decide
  have hnw_trial : f3TrialRxProg.base.toNat + f3TrialRxProg.code.length ≤ 2 ^ 64 := by
    rw [f3TrialRxProg_base, f3TrialRxProg_code_len]; decide
  have hm0_cl : f3TrialRxProg.CodeLoaded (loadCodeMem f3TrialRxProg Memory.empty) :=
    codeLoaded_loadCodeMem (prog := f3TrialRxProg) Memory.empty hal_trial hnw_trial
  have hTrialMng := c2_progContainsMallocng_f3Trial_local mmpl hMm
  refine ProgContainsMultiLib.of_noExterns hPl1 rfl (fun m hLo i hi => ?_) f3PrePanicRxProg_no_ext
  have hm0_blk := hTrialMng.codeLoaded (loadCodeMem f3TrialRxProg Memory.empty) hm0_cl i hi
  obtain ⟨_, _, hm_lo, hm_hi⟩ :=
    f3CliElf_mallocng_code_bounds_of_inElf hPl1 hIn1 i hi
  have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
  have hhi_lo : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3PrePanicWordCount := by decide
  have htop : f3RxSegBase.toNat + 4 * f3PrePanicWordCount < 2 ^ 64 := by decide
  have hlen_i : (mallocngLib.blockProgram mmpl i).code.length =
      mallocngLib.blocks[i].code.length := by
    simp only [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
    exact CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hbase_i : (mallocngLib.blockProgram mmpl i).base = mmpl.base i := rfl
  refine Program.CodeLoaded.intro hm0_blk.aligned hm0_blk.no_wrap fun k hk => ?_
  have hk_raw : k < mallocngLib.blocks[i].code.length := by rwa [← hlen_i]
  have hoff_lt : (mmpl.base i).toNat + k - f3RxSegBase.toNat < f3PrePanicRxProg.code.length := by
    rw [f3PrePanicRxProg_code_len]; omega
  have hoff_full : (mmpl.base i).toNat + k - f3RxSegBase.toNat < f3TrialRxProg.code.length := by
    rw [f3TrialRxProg_code_len]
    have hle_words : 4 * f3PrePanicWordCount ≤ 4 * f3RxWordCount := by decide
    omega
  have haddr_lo : (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k =
      f3PrePanicRxProg.base + BitVec.ofNat 64 ((mmpl.base i).toNat + k - f3RxSegBase.toNat) := by
    rw [hbase_i, f3PrePanicRxProg_base]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have haddr_trial : (mallocngLib.blockProgram mmpl i).base + BitVec.ofNat 64 k =
      f3TrialRxProg.base + BitVec.ofNat 64 ((mmpl.base i).toNat + k - f3RxSegBase.toNat) := by
    rw [haddr_lo, f3PrePanicRxProg_base, f3TrialRxProg_base]
  have hb_m0 := hm0_blk.byte_eq k hk
  rw [haddr_trial] at hb_m0
  rw [haddr_lo]
  exact ⟨(f3PrePanicRxProg_read8_eq_of_codeLoaded hLo hm0_cl _ hoff_lt hoff_full).trans hb_m0,
    hLo.perm_eq _ hoff_lt, hLo.isLazyFree_eq _ hoff_lt⟩

private theorem f3PrePanic_rustStdThunkCode :
    VerifiedLibraries.RustStd.RustStdThunkCode f3PrePanicRxProg
      f3StubAddrs.toRustStd f3RdlAddrs.toRustStd where
  alloc_thunk := f3PrePanic_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.alloc_thunk
    (by decide) (by decide)
  dealloc_thunk := f3PrePanic_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.dealloc_thunk
    (by decide) (by decide)
  realloc_thunk := f3PrePanic_hasInstrs_of_f3Trial f3Trial_rustStdThunkCode.realloc_thunk
    (by decide) (by decide)

private theorem f3PrePanic_rdlShims :
    VerifiedLibraries.RustStd.RustStdRdlShimCode f3PrePanicRxProg
      f3RdlAddrs.toRustStd (mallocngPlacedCAddrs f3MallocngMpl) f3StdLayout.memcpyAddr where
  alloc_instrs := f3PrePanic_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.alloc_instrs
    (by decide) (by decide)
  dealloc_instrs := f3PrePanic_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.dealloc_instrs
    (by decide) (by decide)
  realloc_instrs := f3PrePanic_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.rdlShims.realloc_instrs
    (by decide) (by decide)

private theorem f3PrePanic_stubAz_hasInstrs :
    hasInstrs f3PrePanicRxProg f3StubAzAddr
      [.b (f3RdlAzAddr - f3StubAzAddr)] :=
  f3PrePanic_hasInstrs_of_f3Trial f3Trial_stubAz_hasInstrs (by decide) (by decide)

private theorem f3PrePanic_allocZeroedInstrs :
    hasInstrs f3PrePanicRxProg f3RdlAzAddr
      (rdlAllocZeroedInstrs f3RdlAzAddr
        (mallocngLib.fnAddr f3MallocngMpl "calloc")
        (mallocngPlacedCAddrs f3MallocngMpl).posixMemalign f3StdLayout.memsetAddr) :=
  f3PrePanic_hasInstrs_of_f3Trial f3Trial_seg5ShimBundle.allocZeroedInstrs (by decide) (by decide)

/-! ## 2. `withExecFrozenBudget` & `nonZeroEquivLim` -/

/-- Strengthen `A : RustCliAllocBudget M` with `⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝` so
    subroutine proofs on `aesCbcSubProg` / `libcruxHmacSubProg` / `c2FmtProgTrap` can lift
    allocator calls out of `f3PrePanicRxProg` via `stripExecOutside keepPrePanic`. -/
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

theorem execFrozen_stripExecOutside {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) :
    ExecFrozen (stripExecOutside keep m) := by
  intro a hx
  obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
  rw [strip_perm_of_keep hk]
  exact hfr a hx_m

/-! ## 3. `memcpy`, `memset`, & `f3PrePanicRxProg → P` Lifters -/

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

private theorem steps_preserves_halted_local {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all

private theorem blockExternFree_of_keepPrePanic {P : Program} {addr : BitVec 64} {len : Nat}
    (hext_lo : ∀ pc, keepPrePanic pc = true → P.externAt? pc = none)
    (hlo : f3RxSegBase.toNat ≤ addr.toNat)
    (hhi : addr.toNat + len ≤ f3RxSegBase.toNat + 4 * f3PrePanicWordCount) :
    BlockExternFree P addr len := by
  intro a ha
  apply hext_lo
  unfold keepPrePanic
  have htop : f3RxSegBase.toNat + 4 * f3PrePanicWordCount < 2 ^ 64 := by decide
  have ha_off : (a - addr).toNat < len := ha
  have heq_a : addr + BitVec.ofNat 64 (a - addr).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have ht : (addr + BitVec.ofNat 64 (a - addr).toNat).toNat = addr.toNat + (a - addr).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [heq_a] at ht
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
  exact decide_eq_true (by omega)

private theorem allocMemcpyVm_len_le_2pow63_local {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
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

theorem c2_memcpy_f3PrePanic_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StdLayout.memcpyAddr allocMemcpyVmSpec := by
  have hcl_pure : ∀ m : Memory, P.CodeLoaded m →
      (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords).CodeLoaded m :=
    fun m hm => codeLoaded_pureWordsProg_of_hasWords (hcl m hm) f3PrePanic_memcpy_hasWords (by decide)
  have hlen_w : 4 * memcpySymWords.length = 396 := by rfl_kernel
  have hext : BlockExternFree P f3StdLayout.memcpyAddr (4 * memcpySymWords.length) :=
    blockExternFree_of_keepPrePanic hext_lo (by decide) (by rw [hlen_w]; decide)
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpyVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := allocMemcpyVm_len_le_2pow63_local (Nat.le_of_lt hlt) hm_assoc
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

private theorem pureWordsProg_hasWords_memset_local (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).hasWords entry memsetWords :=
  pureWordsProg_hasWords
    (Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble (4 * memsetWords.length) (2 ^ 64) = true))
    (by rfl_kernel : ((List.range memsetWords.length).all fun i =>
      (pureWordsProg 0#64 memsetWords).readWordOff (4 * i) == memsetWords[i]?) = true)

private theorem pureWordsProg_noSvcMsr_memset_local (entry : BitVec 64) :
    (pureWordsProg entry memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  (by rfl_kernel :
    (pureWordsProg 0#64 memsetWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)

theorem c2_memset_f3PrePanic_ok {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StdLayout.memsetAddr allocMemsetVmSpec := by
  let memsetAddr := f3StdLayout.memsetAddr
  let prog₀ := pureWordsProg memsetAddr memsetWords
  have hpure : subroutine_ok prog₀ memsetAddr
      { ProofLib.memsetRegionSpec with
        post := fun x s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab⌝ ∗
            ProofLib.memsetRegionSpec.post x s0 sf } := by
    apply subroutine_ok_of_steps_outcome
    intro x R s0 hpc hrun hpre hsp hL
    obtain ⟨sf, hsteps, hout⟩ :=
      subroutine_ok_elim_steps_outcome
        (memset_memsetRegionSpec_ok (pureWordsProg_hasWords_memset_local memsetAddr))
        x R s0 hpc hrun hpre hsp hL
    have horc : sf.oracle = s0.oracle :=
      Steps.oracle_eq_of_standard rfl
        (fun pc => by
          simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?])
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
    fun m hm => codeLoaded_pureWordsProg_of_hasWords (hcl m hm) f3PrePanic_memset_hasWords (by decide)
  have hlen_w : 4 * memsetWords.length = 260 := by rfl_kernel
  have hext : BlockExternFree P memsetAddr (4 * memsetWords.length) :=
    blockExternFree_of_keepPrePanic hext_lo (by decide) (by dsimp [memsetAddr]; rw [hlen_w]; decide)
  have hlift := subroutine_ok_lift_pureWords_blockExternFree
    (P := P)
    hpure hsvc (pureWordsProg_noSvcMsr_memset_local memsetAddr)
    hcl_pure hext
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

private theorem f3PrePanicRxProg_codeLoaded_stripKeepPrePanic {m : Memory}
    (hcl : f3PrePanicRxProg.CodeLoaded m) :
    f3PrePanicRxProg.CodeLoaded (stripExecOutside keepPrePanic m) := by
  have hlen : f3PrePanicRxProg.code.length = 4 * f3PrePanicWordCount := f3PrePanicRxProg_code_len
  have hbase : f3PrePanicRxProg.base = f3RxSegBase := rfl
  have htop : f3RxSegBase.toNat + 4 * f3PrePanicWordCount < 2 ^ 64 := by decide
  refine Program.CodeLoaded.intro hcl.aligned hcl.no_wrap fun i hi => ?_
  have hi_lt : i < 4 * f3PrePanicWordCount := by rwa [← hlen]
  have hk : keepPrePanic (f3PrePanicRxProg.base + BitVec.ofNat 64 i) = true := by
    rw [hbase]
    unfold keepPrePanic
    have hsub : (f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase).toNat = i := by
      rw [show f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase = BitVec.ofNat 64 i by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    exact decide_eq_true hi_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8]; exact hcl.byte_eq i hi
  · rw [strip_perm_of_keep hk]; exact hcl.perm_eq i hi
  · rw [strip_isLazyFree]; exact hcl.isLazyFree_eq i hi

private theorem steps_lift_of_stripS_keepPrePanic {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none)
    {sa' sf' : State} (hsteps : Steps f3PrePanicRxProg sa' sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ sa : State, sa' = stripS keepPrePanic sa → ExecFrozen sa.mem →
      ∃ sf : State, Steps P sa sf ∧ sf' = stripS keepPrePanic sf ∧ ExecFrozen sf.mem := by
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
      have he_lo : (f3PrePanicRxProg.externAt? sa.pc).isSome = false := rfl
      rw [he_lo] at hfm'
      simp only [Bool.false_eq_true, ↓reduceIte] at hfm'
      by_cases hal_pc : sa.pc.toNat % 4 = 0
      · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
        by_cases hce' : (stripExecOutside keepPrePanic sa.mem).canExec sa.pc 4 = true
        · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
          have hx4 :
              ((stripExecOutside keepPrePanic sa.mem).perm sa.pc).x = true ∧
              ((stripExecOutside keepPrePanic sa.mem).perm (sa.pc + 1#64)).x = true ∧
              ((stripExecOutside keepPrePanic sa.mem).perm (sa.pc + 2#64)).x = true ∧
              ((stripExecOutside keepPrePanic sa.mem).perm (sa.pc + 3#64)).x = true := by
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
            obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keepPrePanic) hfra
            have hev_strip :
                f3PrePanicRxProg.evalInst (.system false 0#16) (stripS keepPrePanic sa) =
                  stripS keepPrePanic (Syscall.standard sa) := by
              simp [f3PrePanicRxProg, Program.evalInst, execInstWithSvc, hcomm]
            have hevP : P.evalInst (.system false 0#16) sa = Syscall.standard sa := by
              simp [Program.evalInst, execInstWithSvc, hsvc]
            have hstepP : Step P sa (Syscall.standard sa) := hevP ▸ Step.exec hra hfmP
            rw [hsa, hev_strip] at hrest ih
            obtain ⟨sf, hsteps_rest, hsf_eq, hfr_sf⟩ :=
              ih hnhalt' (Syscall.standard sa) rfl hfr_sb
            exact ⟨sf, .step hstepP hsteps_rest, hsf_eq, hfr_sf⟩
          · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
            have hev_strip :
                f3PrePanicRxProg.evalInst inst (stripS keepPrePanic sa) =
                  stripS keepPrePanic (execInst inst sa) := by
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

theorem lift_f3PrePanicRxProg_subroutine_ok {α : Type} {P : Program} {entry : BitVec 64}
    {spec0 specF : Spec α}
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none)
    (hOk0 : subroutine_ok f3PrePanicRxProg entry spec0)
    (hPre : ∀ (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ specF.pre x s0 ∗ R) →
      ExecFrozen s0.mem ∧
        ((stripS keepPrePanic s0).mem ⊨ spec0.pre x (stripS keepPrePanic s0) ∗ R))
    (hOut : ∀ (x : α) (R : SepProp) (s0 sf : State),
      ExecFrozen sf.mem →
      SubroutineOutcome spec0 x R (stripS keepPrePanic s0) (stripS keepPrePanic sf) →
      SubroutineOutcome specF x R s0 sf) :
    subroutine_ok P entry specF := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hpreF hsp hPm
  obtain ⟨hFr0, hpre0'⟩ := hPre x R s0 hpreF
  have hcl_lo' : f3PrePanicRxProg.CodeLoaded (stripS keepPrePanic s0).mem :=
    f3PrePanicRxProg_codeLoaded_stripKeepPrePanic (hcl s0.mem hPm)
  obtain ⟨sf', hsteps', hout0'⟩ :=
    subroutine_ok_elim_steps_outcome hOk0 x R (stripS keepPrePanic s0)
      (by rw [stripS_pc_eq_local]; exact hpc)
      (by rw [stripS_status_eq_local]; exact hrun)
      hpre0'
      (by cases s0; exact hsp)
      hcl_lo'
  have hnhalt' : sf'.status ≠ .Halted := by
    rcases hout0' with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
      (rw [hst]; nofun)
  obtain ⟨sf, hstepsP, hsf_eq, hFr_sf⟩ :=
    steps_lift_of_stripS_keepPrePanic hsvc hext_lo hsteps' hnhalt' s0 rfl hFr0
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
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none)
    (hOk0 : subroutine_ok f3PrePanicRxProg entry
      (rustCliAllocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed)) :
    subroutine_ok P entry
      (rustCliAllocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim zeroed) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepPrePanic_mallocng mmpl hMm
  refine lift_f3PrePanicRxProg_subroutine_ok hsvc hcl hext_lo hOk0 ?_ ?_
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
    have hsat := satisfies_stripExecOutside keepPrePanic hpre0
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

private theorem f3PrePanic_allocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) f3PrePanicRxProg f3StubAddrs :=
  fineHookRustCliAllocBudgetEntries_thunks
    (f3PrePanic_progContainsMallocng mmpl hMm) γ tp brkStart f3PrePanic_rustStdThunkCode
    (c2_mng_cAddrs_eq_local mmpl hMm ▸ f3PrePanic_rdlShims)
    (c2_memcpy_f3PrePanic_ok rfl (fun _ h => h) (fun _ _ => rfl))

theorem c2_alloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.alloc
      (rustCliAllocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim false) :=
  lift_allocBase_withExecFrozen_ok hMm γ tp brkStart f3StubAddrs.alloc false hlim hsvc hcl hext_lo
    ((f3PrePanic_allocEntries mmpl hMm γ tp brkStart).alloc lim)

theorem c2_allocZeroed_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAzAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) :=
  lift_allocBase_withExecFrozen_ok hMm γ tp brkStart f3StubAzAddr true hlim hsvc hcl hext_lo
    (fineHookRustCliAllocZeroedBudget_thunk_ok
      (f3PrePanic_progContainsMallocng mmpl hMm) γ tp brkStart f3StubAzAddr f3RdlAzAddr
      f3StdLayout.memsetAddr lim f3PrePanic_stubAz_hasInstrs
      (by
        rw [c2_mng_fnAddr_eq_local mmpl hMm, c2_mng_cAddrs_eq_local mmpl hMm]
        exact f3PrePanic_allocZeroedInstrs)
      (c2_memset_f3PrePanic_ok rfl (fun _ h => h) (fun _ _ => rfl)))

theorem c2_dealloc_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.dealloc
      (rustCliDeallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepPrePanic_mallocng mmpl hMm
  refine lift_f3PrePanicRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3PrePanic_allocEntries mmpl hMm γ tp brkStart).dealloc lim) ?_ ?_
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
    have hsat := satisfies_stripExecOutside keepPrePanic hpre0
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

private theorem f3PrePanic_noAesAllocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart) f3PrePanicRxProg f3StubAddrs :=
  fineHookNoAesRustCliAllocBudgetEntries_thunks
    (f3PrePanic_progContainsMallocng mmpl hMm) γ tp brkStart f3PrePanic_rustStdThunkCode
    (c2_mng_cAddrs_eq_local mmpl hMm ▸ f3PrePanic_rdlShims)
    (c2_memcpy_f3PrePanic_ok rfl (fun _ h => h) (fun _ _ => rfl))

theorem c2_allocZeroed_noAes_withExecFrozen_ok {P : Program} {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits)
    (hsvc : P.svc = Syscall.standard)
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAzAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepPrePanic_mallocng mmpl hMm
  have hOk0 : subroutine_ok f3PrePanicRxProg f3StubAzAddr
      (rustCliAllocBudgetSpecBase fineCostModel A₀ lim true) :=
    fineHookNoAesRustCliAllocZeroedBudget_thunk_ok
      (f3PrePanic_progContainsMallocng mmpl hMm) γ tp brkStart f3StubAzAddr f3RdlAzAddr
      f3StdLayout.memsetAddr lim f3PrePanic_stubAz_hasInstrs
      (by
        rw [c2_mng_fnAddr_eq_local mmpl hMm, c2_mng_cAddrs_eq_local mmpl hMm]
        exact f3PrePanic_allocZeroedInstrs)
      (c2_memset_f3PrePanic_ok rfl (fun _ h => h) (fun _ _ => rfl))
  change subroutine_ok P f3StubAzAddr
    (rustCliAllocBudgetSpecBase fineCostModel (withExecFrozenBudget A₀) lim true)
  refine lift_f3PrePanicRxProg_subroutine_ok hsvc hcl hext_lo hOk0 ?_ ?_
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
    have hsat := satisfies_stripExecOutside keepPrePanic hpre0
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
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.dealloc
      (rustCliDeallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookNoAesRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepPrePanic_mallocng mmpl hMm
  refine lift_f3PrePanicRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3PrePanic_noAesAllocEntries mmpl hMm γ tp brkStart).dealloc lim) ?_ ?_
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
    have hsat := satisfies_stripExecOutside keepPrePanic hpre0
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
    (hcl : ∀ m : Memory, P.CodeLoaded m → f3PrePanicRxProg.CodeLoaded m)
    (hext_lo : ∀ pc : BitVec 64, keepPrePanic pc = true → P.externAt? pc = none) :
    subroutine_ok P f3StubAddrs.realloc
      (rustCliReallocBudgetSpecBase fineCostModel
        (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim) := by
  let A₀ := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hKeepM := c2_keepPrePanic_mallocng mmpl hMm
  refine lift_f3PrePanicRxProg_subroutine_ok hsvc hcl hext_lo
    ((f3PrePanic_allocEntries mmpl hMm γ tp brkStart).realloc lim) ?_ ?_
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
    have hsat := satisfies_stripExecOutside keepPrePanic hpre0
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

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
