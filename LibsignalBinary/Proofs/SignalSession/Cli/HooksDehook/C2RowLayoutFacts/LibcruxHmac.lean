/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
import LibsignalBinary.Proofs.HookDischarge.Libc.Memset
import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `Placeable`, `subroutine_ok`, and Hull Glue for `libcrux_hmac::hmac`

Discharges the concrete 7-block placement `c2HaclMpl`, panic-stub sub-program
`libcruxHmacSubProg`, `fs`/`trace`-preserving `subroutine_ok` for `libcrux_hmac::hmac` (`w0 = 0`
SHA-256), and `LsRetAddr624` guards for `lsLibcruxHmacSym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng)
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib lsLibcruxHmacSym)
open LibsignalBinary.Heap (BudgetLimits FdsHiFrame allocMemcpyVmSpec zeroBudgetLimits)
open LibsignalBinary.Heap.MuslMemOpsRunsTo
  (BlockExternFree codeLoaded_pureWordsProg_of_hasWords
   subroutine_ok_lift_pureWords_blockExternFree)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (hasShimInstrs_of_wordTree rustAllocShimVm_ret_ok rustHandleErrorPanic_of_extern)
open LibsignalBinary.Heap.Fine
  (allocMemsetVmSpec f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RdlAzAddr f3RxWordCount f3StdLayout
   f3StubAddrs f3StubAzAddr fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256 (haclSubroutinesTrace_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib memcpySym rustAllocShimSym rustAllocSym
   rustAllocZeroedSym rustDeallocSym rustHandleErrorSym rustUnwrapFailedSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts (HaclInProg)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256 (haclMemcpy_of_allocMemcpyVm)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac
  (HaclSubroutinesTrace HmacBudgetAllocSubroutines HmacValidAuxSubroutines
   libcruxHmac_budget_fs_subroutineOk withFsTraceBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep
  (HmacAuxSubroutines hmacMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
  (sha256CompressState_eq_spqrSha256Compress)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memset (memset_memsetRegionSpec_ok)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcPanicExterns aesCbcSubProg aesCbcSubProgRaw_blockExternFree aesCbcSubProg_base
   aesCbcSubProg_codeLoaded_f3PrePanic aesCbcSubProg_codeLoaded_iff aesCbcSubProg_externAt_cases
   aesCbcSubProg_externAt_eq aesCbcSubProg_externAt_handleError
   aesCbcSubProg_externAt_none_of_keepPrePanic aesCbcSubProg_externAt_none_of_not_panic
   aesCbcSubProg_svc c2_aesCbcSubProg_subslice c2_aesCbc_hlr_ne_stub c2_memcpy_aesCbcSubProgRaw_ok
   c2_memset_aesCbcSubProgRaw_ok hasInstrs_aesCbcSubProgRaw_of_check)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
  (c2_allocZeroed_withExecFrozen_ok c2_alloc_withExecFrozen_ok c2_dealloc_withExecFrozen_ok
   fineHookPool_nonZeroEquivLim fitsEnv_nonZeroEquivLim nonZeroEquivLim nonZeroEquivLim_ne_zero
   withExecFrozenBudget withExecFrozenBudget_pool_entails)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacGhost libcruxHmacGhost_rowSpecOk libcruxHmacSpecOf withFsTraceExact
   withHooksUnfetched)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3CliElf_mallocng_linkedAt_unique
   f3TrialElf f3TrialElf_parse mallocngLib_in_f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr isLinkedPanicAddr_false_of_mid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_stubs
   f3TrialRxProg_no_ext f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree
   f3TrialRxWordTree_eq f3TrialRxWordTree_size f3Trial_allocMemcpyVm_ok
   f3Trial_allocMemsetVm_ok f3Trial_progContainsMallocng f3Trial_rustStdThunkCode
   f3Trial_seg5ShimBundle f3Trial_stubAz_hasInstrs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2HaclMpl c2Lib2DehookedSyms c2LibcruxHmacAddr)
open ProofLib.StdStartup (checkWordsAt hasInstrs hasWords_of_wordTree)
open VerifiedLibraries.Mallocng.Proofs
  (memRegion_entails_exists_pointsToBytes memcpySymWords
   memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_ok)
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.RustStd (checkShimInstrsAt)

/-! ## 1. `c2HaclMpl` Placeability & `libcruxHmacSubProg` -/

theorem c2HaclMpl_base6 : c2HaclMpl.base 6 = c2LibcruxHmacAddr :=
  rfl

theorem lsLibcruxHmacSym_mem_c2Lib2DehookedSyms :
    lsLibcruxHmacSym ∈ c2Lib2DehookedSyms := by
  simp [lsLibcruxHmacSym, c2Lib2DehookedSyms]

theorem c2_checkLibcruxHmacPlaceable_ok :
    libcruxHmacLib.checkPlaceable c2HaclMpl = true := by
  decide +kernel

theorem c2_libcruxHmacLib_placeable :
    libcruxHmacLib.Placeable c2HaclMpl :=
  MultiPlacedLib.placeable_of_checkPlaceable c2_checkLibcruxHmacPlaceable_ok

/-- Panic-extern map for `libcruxHmacSubProg` (`rfl` alias of `aesCbcPanicExterns`). -/
abbrev libcruxHmacPanicExterns : String → Option (State → State) :=
  aesCbcPanicExterns

/-- Kept-region predicate covering `seg[2]` (`[f3RxSegBase, f3RxSegBase + f3TrialRxProg.code.length)`). -/
@[expose] noncomputable def keepRxSeg (pc : BitVec 64) : Bool :=
  decide ((pc - f3TrialRxProg.base).toNat < f3TrialRxProg.code.length)

/-- Exported `seg[2]` RX sub-program for `libcrux_hmac` replays (`rfl` alias of `aesCbcSubProg`,
    installing `Rust.panicked` at all `18` `cliLinkedPanicAddrs` in `.text.lib2`). -/
noncomputable abbrev libcruxHmacSubProg : Program :=
  aesCbcSubProg

/-- Compatibility alias (`rfl`) for `libcruxHmacSubProg`. -/
noncomputable abbrev libcruxHmacSubProgRaw : Program :=
  aesCbcSubProg

theorem libcruxHmacSubProg_svc : libcruxHmacSubProg.svc = Syscall.standard :=
  aesCbcSubProg_svc

theorem libcruxHmacSubProg_base : libcruxHmacSubProg.base = f3RxSegBase :=
  aesCbcSubProg_base

theorem libcruxHmacSubProg_codeLoaded_iff (m : Memory) :
    libcruxHmacSubProg.CodeLoaded m ↔ f3TrialRxProg.CodeLoaded m :=
  aesCbcSubProg_codeLoaded_iff m

theorem libcruxHmacSubProgRaw_svc : libcruxHmacSubProgRaw.svc = Syscall.standard :=
  aesCbcSubProg_svc

theorem libcruxHmacSubProgRaw_base : libcruxHmacSubProgRaw.base = f3RxSegBase :=
  aesCbcSubProg_base

theorem libcruxHmacSubProgRaw_codeLoaded_iff (m : Memory) :
    libcruxHmacSubProgRaw.CodeLoaded m ↔ f3TrialRxProg.CodeLoaded m :=
  aesCbcSubProg_codeLoaded_iff m

theorem libcruxHmacSubProg_externAt_eq (pc : BitVec 64) :
    libcruxHmacSubProg.externAt? pc =
      if isLinkedPanicAddr pc then some Rust.panicked else none :=
  aesCbcSubProg_externAt_eq pc

theorem libcruxHmacSubProgRaw_externAt_handleError :
    libcruxHmacSubProgRaw.externAt? (c2HaclMpl.ρ rustHandleErrorSym) = some Rust.panicked := by
  have heq : c2HaclMpl.ρ rustHandleErrorSym =
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen.wp4HandleErrorAddr := by decide
  rw [heq]
  exact aesCbcSubProg_externAt_handleError

theorem libcruxHmacSubProgRaw_externAt_unwrapFailed :
    libcruxHmacSubProgRaw.externAt? (c2HaclMpl.ρ rustUnwrapFailedSym) = some Rust.panicked := by
  rw [aesCbcSubProg_externAt_eq]
  have h : isLinkedPanicAddr (c2HaclMpl.ρ rustUnwrapFailedSym) = true := by decide
  rw [h]; rfl

theorem libcruxHmacSubProg_externAt_handleError :
    libcruxHmacSubProg.externAt? (c2HaclMpl.ρ rustHandleErrorSym) = some Rust.panicked :=
  libcruxHmacSubProgRaw_externAt_handleError

theorem libcruxHmacSubProg_externAt_unwrapFailed :
    libcruxHmacSubProg.externAt? (c2HaclMpl.ρ rustUnwrapFailedSym) = some Rust.panicked :=
  libcruxHmacSubProgRaw_externAt_unwrapFailed

theorem libcruxHmacSubProg_externAt_hmac :
    libcruxHmacSubProg.externAt? c2LibcruxHmacAddr = none :=
  aesCbcSubProg_externAt_none_of_not_panic (isLinkedPanicAddr_false_of_mid (by decide) (by decide))

theorem libcruxHmacSubProg_externAt_cases {pc : BitVec 64} {f : State → State}
    (he : libcruxHmacSubProg.externAt? pc = some f) :
    f = Rust.panicked ∧ isLinkedPanicAddr pc = true :=
  aesCbcSubProg_externAt_cases he

theorem libcruxHmacSubProg_externAt_none_of_not_panic {pc : BitVec 64}
    (hnp : isLinkedPanicAddr pc = false) :
    libcruxHmacSubProg.externAt? pc = none :=
  aesCbcSubProg_externAt_none_of_not_panic hnp

theorem keepRxSeg_eq_lt (pc : BitVec 64) :
    keepRxSeg pc = decide ((pc - f3RxSegBase).toNat < 4 * f3RxWordCount) := by
  unfold keepRxSeg
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  rw [f3TrialRxProg_base, hlen]

theorem keepRxSeg_entry :
    keepRxSeg (c2HaclMpl.base 6) = true := by
  rw [keepRxSeg_eq_lt]
  decide

theorem keepRxSeg_eq_progKeep :
    keepRxSeg = progKeep f3TrialRxProg :=
  rfl

theorem c2_libcruxHmacSubProg_subslice :
    checkProgCodeSubslice f3TrialRxProg libcruxHmacSubProg = true :=
  c2_aesCbcSubProg_subslice

/-! ## 2. `HaclInProg`, `f3TrialRxProg` Subroutines, `subroutine_ok`, & `LsRetAddr624` Guards -/

private def relocsSorted : Nat → List RelocEntry → Bool
  | _, [] => true
  | bound, r :: rs => decide (bound ≤ r.off ∧ r.off % 4 = 0) && relocsSorted (r.off + 4) rs

private theorem find?_none_of_relocsSorted :
    ∀ {off bound : Nat} {rs : List RelocEntry},
      off < bound → relocsSorted bound rs = true → rs.find? (·.off == off) = none
  | _, _, [], _, _ => rfl
  | off, bound, r :: rs, hlt, hs => by
    simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hs
    dsimp only [List.find?]
    rw [beq_false_of_ne (by omega)]
    exact find?_none_of_relocsSorted (by omega) hs.2

private theorem wordOfBytesLE_of_drop {xs : List (BitVec 8)} {off : Nat}
    {b0 b1 b2 b3 : BitVec 8} {rest : List (BitVec 8)}
    (hd : xs.drop off = b0 :: b1 :: b2 :: b3 :: rest) :
    wordOfBytesLE xs off = wordOfBytesLE [b0, b1, b2, b3] 0 := by
  have hget : ∀ k, xs.getD (off + k) 0#8 = (b0 :: b1 :: b2 :: b3 :: rest).getD k 0#8 := by
    intro k
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_drop, hd]
  have h0 := hget 0; rw [Nat.add_zero] at h0
  have h1 := hget 1
  have h2 := hget 2
  have h3 := hget 3
  unfold wordOfBytesLE
  rw [h0, h1, h2, h3]
  rfl

private theorem bytesOfWordLE_wordOfBytesLE4 (b0 b1 b2 b3 : BitVec 8) :
    bytesOfWordLE (wordOfBytesLE [b0, b1, b2, b3] 0) = [b0, b1, b2, b3] := by
  rw [wordOfBytesLE_cons4_zero]
  simp only [bytesOfWordLE, bytesLE, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits

private def patchedRelocFast (blk : CodeBlock) (pl : Placement) (off : Nat) (r : RelocEntry)
    (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  if !pl.relax off && !(4 ≤ off && pl.relax (off - 4)) &&
      !r.kind.isGotOrTlsIe && !blk.undefWeakBranch pl r then
    patchRelocWord r.kind (wordOfBytesLE [b0, b1, b2, b3] 0)
      (pl.base + BitVec.ofNat 64 off) (blk.relocTarget pl off r)
  else
    blk.patchedWord pl off

private theorem patchedRelocFast_eq {blk : CodeBlock} {pl : Placement} {off : Nat}
    {r : RelocEntry} {b0 b1 b2 b3 : BitVec 8} {rest : List (BitVec 8)}
    (hr : blk.relocAt? off = some r)
    (hd : blk.code.drop off = b0 :: b1 :: b2 :: b3 :: rest) :
    patchedRelocFast blk pl off r b0 b1 b2 b3 = blk.patchedWord pl off := by
  unfold patchedRelocFast
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    rcases hcond with ⟨⟨⟨hnr0, hnr4⟩, hng⟩, hnw⟩
    have h0 : blk.relaxedAt pl off = false := by
      simp [CodeBlock.relaxedAt, hnr0]
    have h4 : off < 4 ∨ blk.relaxedAt pl (off - 4) = false := by
      by_cases hle : 4 ≤ off
      · right
        have hnr4' : pl.relax (off - 4) = false := by simpa [hle] using hnr4
        simp [CodeBlock.relaxedAt, hnr4']
      · exact Or.inl (Nat.lt_of_not_le hle)
    rw [CodeBlock.patchedWord_of_notRelaxed hr h0 h4 hng hnw]
    have hw : blk.wordAt off = wordOfBytesLE [b0, b1, b2, b3] 0 := wordOfBytesLE_of_drop hd
    rw [hw]
  · rfl

private def patchedScan (blk : CodeBlock) (pl : Placement) :
    Nat → List RelocEntry → List (BitVec 8) → List (BitVec 8)
  | j, [], b0 :: b1 :: b2 :: b3 :: rest =>
    b0 :: b1 :: b2 :: b3 :: patchedScan blk pl (j + 1) [] rest
  | j, r :: rs, b0 :: b1 :: b2 :: b3 :: rest =>
    if r.off == 4 * j then
      bytesOfWordLE (patchedRelocFast blk pl (4 * j) r b0 b1 b2 b3) ++
        patchedScan blk pl (j + 1) rs rest
    else
      b0 :: b1 :: b2 :: b3 :: patchedScan blk pl (j + 1) (r :: rs) rest
  | _, _, _ => []

private theorem patchedScan_eq (blk : CodeBlock) (pl : Placement) :
    ∀ (bs : List (BitVec 8)) (j : Nat) (rs : List RelocEntry),
      blk.code.drop (4 * j) = bs →
      relocsSorted (4 * j) rs = true →
      (∀ k, 4 * j ≤ k → blk.relocAt? k = rs.find? (·.off == k)) →
      patchedScan blk pl j rs bs =
        (List.range (bs.length / 4)).flatMap (fun k =>
          bytesOfWordLE (blk.patchedWord pl (4 * (j + k))))
  | [], _, rs, _, _, _
  | [_], _, rs, _, _, _
  | [_, _], _, rs, _, _, _
  | [_, _, _], _, rs, _, _, _ => by
    cases rs <;> simp [patchedScan]
  | b0 :: b1 :: b2 :: b3 :: rest, j, [], hd, _, hrel => by
    have hdiv : (b0 :: b1 :: b2 :: b3 :: rest).length / 4 = 1 + rest.length / 4 := by
      change (rest.length + 4) / 4 = 1 + rest.length / 4
      omega
    have hnone : blk.relocAt? (4 * j) = none := hrel (4 * j) (Nat.le_refl _)
    have hpw : bytesOfWordLE (blk.patchedWord pl (4 * j)) = [b0, b1, b2, b3] := by
      rw [CodeBlock.patchedWord_of_relocAt_none hnone,
        show blk.wordAt (4 * j) = wordOfBytesLE [b0, b1, b2, b3] 0 from wordOfBytesLE_of_drop hd,
        bytesOfWordLE_wordOfBytesLE4]
    have hd' : blk.code.drop (4 * (j + 1)) = rest := by
      have h4 : 4 * (j + 1) = 4 * j + 4 := by omega
      rw [h4, ← List.drop_drop, hd]; rfl
    have ih := patchedScan_eq blk pl rest (j + 1) [] hd' rfl (fun k hk => hrel k (by omega))
    dsimp only [patchedScan]
    rw [ih, hdiv, Nat.add_comm 1, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      show 4 * (j + 0) = 4 * j by omega, hpw, List.cons_append, List.cons_append, List.cons_append,
      List.cons_append, List.nil_append]
    congr 4
    apply List.flatMap_congr
    intro k _
    rw [show 4 * (j + 1 + k) = 4 * (j + (k + 1)) by omega]
  | b0 :: b1 :: b2 :: b3 :: rest, j, r :: rs, hd, hs, hrel => by
    simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hdiv : (b0 :: b1 :: b2 :: b3 :: rest).length / 4 = 1 + rest.length / 4 := by
      change (rest.length + 4) / 4 = 1 + rest.length / 4
      omega
    have hd' : blk.code.drop (4 * (j + 1)) = rest := by
      have h4 : 4 * (j + 1) = 4 * j + 4 := by omega
      rw [h4, ← List.drop_drop, hd]; rfl
    dsimp only [patchedScan]
    cases heq : r.off == 4 * j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne : r.off ≠ 4 * j := beq_eq_false_iff_ne.mp heq
      have hs' : relocsSorted (4 * (j + 1)) (r :: rs) = true := by
        simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨by omega, hs.1.2⟩, hs.2⟩
      have hnone : blk.relocAt? (4 * j) = none := by
        rw [hrel (4 * j) (Nat.le_refl _)]
        exact find?_none_of_relocsSorted (by omega) hs'
      have hpw : bytesOfWordLE (blk.patchedWord pl (4 * j)) = [b0, b1, b2, b3] := by
        rw [CodeBlock.patchedWord_of_relocAt_none hnone,
          show blk.wordAt (4 * j) = wordOfBytesLE [b0, b1, b2, b3] 0 from wordOfBytesLE_of_drop hd,
          bytesOfWordLE_wordOfBytesLE4]
      have ih := patchedScan_eq blk pl rest (j + 1) (r :: rs) hd' hs'
        (fun k hk => hrel k (by omega))
      rw [ih, hdiv, Nat.add_comm 1, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        show 4 * (j + 0) = 4 * j by omega, hpw, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.nil_append]
      congr 4
      apply List.flatMap_congr
      intro k _
      rw [show 4 * (j + 1 + k) = 4 * (j + (k + 1)) by omega]
    · simp only [↓reduceIte]
      have hroff : r.off = 4 * j := beq_iff_eq.mp heq
      have hr_at : blk.relocAt? (4 * j) = some r := by
        rw [hrel (4 * j) (Nat.le_refl _)]
        dsimp only [List.find?]
        rw [heq]
      have hs' : relocsSorted (4 * (j + 1)) rs = true := by
        simpa only [show 4 * (j + 1) = r.off + 4 by omega] using hs.2
      have hrel' : ∀ k, 4 * (j + 1) ≤ k → blk.relocAt? k = rs.find? (·.off == k) := by
        intro k hk
        rw [hrel k (by omega)]
        dsimp only [List.find?]
        rw [beq_false_of_ne (by omega)]
      have ih := patchedScan_eq blk pl rest (j + 1) rs hd' hs' hrel'
      rw [patchedRelocFast_eq hr_at hd, ih, hdiv, Nat.add_comm 1, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map, show 4 * (j + 0) = 4 * j by omega]
      congr 1
      apply List.flatMap_congr
      intro k _
      rw [show 4 * (j + 1 + k) = 4 * (j + (k + 1)) by omega]

private def patchedFast (blk : CodeBlock) (pl : Placement) : List (BitVec 8) :=
  if relocsSorted 0 blk.relocs then patchedScan blk pl 0 blk.relocs blk.code
  else blk.patched pl

private theorem patchedFast_eq (blk : CodeBlock) (pl : Placement) :
    patchedFast blk pl = blk.patched pl := by
  unfold patchedFast
  cases hs : relocsSorted 0 blk.relocs
  · rfl
  · simp only [↓reduceIte, CodeBlock.patched]
    simpa only [Nat.zero_add] using
      patchedScan_eq blk pl blk.code 0 blk.relocs rfl hs (fun _ _ => rfl)

private def checkBlockWordTreeSubslice (rxBase : BitVec 64) (t : WordTree) (n : Nat)
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat) : Bool :=
  let base := mpl.base i
  let blk := (lib.blockLib i).text
  let span := 4 * (blk.code.length / 4)
  let off := (base - rxBase).toNat
  Nat.beq (base.toNat % 4) 0 &&
  Nat.ble (base.toNat + span) (2 ^ 64) &&
  ((rxBase + BitVec.ofNat 64 off) == base) &&
  (WordTree.sliceBytesChecked t n off span == some (patchedFast blk (lib.blockPlacement mpl i)))

private theorem checkProgCodeSubslice_of_blockWordTree {i : Nat}
    (hchk : checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl i = true) :
    checkProgCodeSubslice f3TrialRxProg (libcruxHmacLib.blockProgram c2HaclMpl i) = true := by
  unfold checkBlockWordTreeSubslice at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq, patchedFast_eq] at hchk
  rcases hchk with ⟨⟨⟨hAlign, hNoWrap⟩, hBaseEq⟩, hSlice⟩
  have hBounds := WordTree.sliceBytesChecked_bounds hSlice
  have hEq := WordTree.sliceBytesChecked_eq f3TrialRxWordTree_size hSlice
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hprog_base : (libcruxHmacLib.blockProgram c2HaclMpl i).base = c2HaclMpl.base i := rfl
  have hprog_code : (libcruxHmacLib.blockProgram c2HaclMpl i).code =
      (libcruxHmacLib.blockLib i).text.patched (libcruxHmacLib.blockPlacement c2HaclMpl i) := rfl
  have hprog_len : (libcruxHmacLib.blockProgram c2HaclMpl i).code.length =
      4 * ((libcruxHmacLib.blockLib i).text.code.length / 4) := by
    rw [hprog_code, CodeBlock.length_patched]
  unfold checkProgCodeSubslice
  rw [f3TrialRxProg_base, hlen, f3TrialRxWordTree_eq, hprog_base, hprog_len, hprog_code]
  dsimp only
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨hAlign, hNoWrap⟩, hBaseEq⟩, hBounds.2.2⟩, hEq.symm⟩

private theorem c2_rxSlice_hacl_0 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 0 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_1 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 1 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_2 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 2 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_3 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 3 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_4 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 4 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_5 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 5 = true := by
  rfl_kernel

private theorem c2_rxSlice_hacl_6 :
    checkBlockWordTreeSubslice f3RxSegBase f3TrialRxWordTree f3RxWordCount
      libcruxHmacLib c2HaclMpl 6 = true := by
  rfl_kernel

private theorem c2_libcruxHmacLib_blocks_length : libcruxHmacLib.blocks.length = 7 :=
  rfl

theorem c2_libcruxHmac_block_subslice {i : Nat} (hi : i < libcruxHmacLib.blocks.length) :
    checkProgCodeSubslice f3TrialRxProg (libcruxHmacLib.blockProgram c2HaclMpl i) = true := by
  rw [c2_libcruxHmacLib_blocks_length] at hi
  apply checkProgCodeSubslice_of_blockWordTree
  match i, hi with
  | 0, _ => exact c2_rxSlice_hacl_0
  | 1, _ => exact c2_rxSlice_hacl_1
  | 2, _ => exact c2_rxSlice_hacl_2
  | 3, _ => exact c2_rxSlice_hacl_3
  | 4, _ => exact c2_rxSlice_hacl_4
  | 5, _ => exact c2_rxSlice_hacl_5
  | 6, _ => exact c2_rxSlice_hacl_6

theorem c2_libcruxHmacLib_codeLoaded_of_rxProg {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    libcruxHmacLib.CodeLoaded c2HaclMpl m :=
  fun _ hi => codeLoaded_of_checkProgCodeSubslice hRx (c2_libcruxHmac_block_subslice hi)

theorem c2_haclInProg_f3TrialRxProg :
    HaclInProg f3TrialRxProg c2HaclMpl where
  placeable := c2_libcruxHmacLib_placeable
  svc_eq := f3TrialRxProg_svc
  noHooks := fun _ _ _ _ => f3TrialRxProg_no_ext _

private theorem c2_hacl_block_mid_ok :
    (List.finRange 7).all (fun k =>
      decide (0x47ac2c ≤ (c2HaclMpl.base k.val).toNat ∧
        (c2HaclMpl.base k.val).toNat + (libcruxHmacLib.blocks[k.val]'(by
          rw [c2_libcruxHmacLib_blocks_length]; exact k.isLt)).code.length ≤ 0x4cb070)) = true := by
  decide +kernel

theorem c2_haclInProg_libcruxHmacSubProg :
    HaclInProg libcruxHmacSubProg c2HaclMpl where
  placeable := c2_libcruxHmacLib_placeable
  svc_eq := libcruxHmacSubProg_svc
  noHooks := by
    intro i hi off hoff
    have hlen_prog : (libcruxHmacLib.blockProgram c2HaclMpl i).code.length =
        libcruxHmacLib.blocks[i].code.length := by
      simp only [MultiPlacedLib.blockProgram, PlacedLib.program, libcruxHmacLib.blockLib_text hi]
      exact CodeBlock.length_patched_of_aligned _
        (c2_libcruxHmacLib_placeable.blocks_ok i hi).len_aligned
    have hoff' : off < libcruxHmacLib.blocks[i].code.length := hlen_prog ▸ hoff
    have hi7 : i < 7 := by rwa [c2_libcruxHmacLib_blocks_length] at hi
    have hbounds :
        0x47ac2c ≤ (c2HaclMpl.base i).toNat ∧
        (c2HaclMpl.base i).toNat + libcruxHmacLib.blocks[i].code.length ≤ 0x4cb070 :=
      of_decide_eq_true (List.all_eq_true.mp c2_hacl_block_mid_ok ⟨i, hi7⟩ (List.mem_finRange _))
    have ha_nat : (c2HaclMpl.base i + BitVec.ofNat 64 off).toNat = (c2HaclMpl.base i).toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact libcruxHmacSubProg_externAt_none_of_not_panic
      (isLinkedPanicAddr_false_of_mid (by omega) (by omega))

private theorem c2HaclMpl_rho_memcpy : c2HaclMpl.ρ memcpySym = f3StdLayout.memcpyAddr := by
  decide

private theorem c2HaclMpl_rho_shim : c2HaclMpl.ρ rustAllocShimSym = f3NoShimV2Addr := by
  decide

private theorem c2HaclMpl_rho_alloc : c2HaclMpl.ρ rustAllocSym = f3StubAddrs.alloc := by
  decide

private theorem c2HaclMpl_rho_dealloc : c2HaclMpl.ρ rustDeallocSym = f3StubAddrs.dealloc := by
  decide

private theorem c2HaclMpl_rho_allocZeroed : c2HaclMpl.ρ rustAllocZeroedSym = f3StubAzAddr := by
  decide

theorem c2_haclSubroutinesTrace_f3TrialRxProg :
    HaclSubroutinesTrace f3TrialRxProg c2HaclMpl := by
  refine haclSubroutinesTrace_ok c2_haclInProg_f3TrialRxProg ?_
  rw [c2HaclMpl_rho_memcpy]
  exact haclMemcpy_of_allocMemcpyVm f3Trial_allocMemcpyVm_ok

theorem c2_hmacValidAux_f3TrialRxProg :
    HmacValidAuxSubroutines f3TrialRxProg c2HaclMpl where
  shim_ok := by
    rw [c2HaclMpl_rho_shim]
    exact rustAllocShimVm_ret_ok f3Trial_seg5ShimBundle.noAllocShimV2
  memcpy_ok := by
    rw [c2HaclMpl_rho_memcpy]
    apply subroutine_ok.of_codeLoaded
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _
    dsimp only [hmacMemcpyVmSpec] at hpre
    have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ (stackAt s0.sp 4096 ∗ R) := by
      dsimp only [allocMemcpyVmSpec]
      simpa only [sepConj_assoc] using hpre
    refine subroutine_ok.mono_outcome f3Trial_allocMemcpyVm_ok (dst, src, bs)
      (stackAt s0.sp 4096 ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [allocMemcpyVmSpec] at hpost
      dsimp only [hmacMemcpyVmSpec]
      simp only [sepConj_assoc] at hpost ⊢
      rw [satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨hret0, hacp, hvm⟩, hspat⟩
      exact ⟨⟨hret0, hvm, hacp.2.1, hacp.1⟩, hspat⟩
    · dsimp only [allocMemcpyVmSpec] at hpan
      rw [satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · dsimp only [allocMemcpyVmSpec] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [allocMemcpyVmSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1

theorem c2_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

private theorem c2_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem c2_mng_fnAddr_eq (mmpl : MultiPlacement)
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

private theorem c2_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  unfold mallocngPlacedCAddrs
  simp only [c2_mng_fnAddr_eq mmpl hMm]

theorem c2_progContainsMallocng_f3TrialRxProg (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hPl1 := c2_mng_placeable mmpl hMm
  have hIn1 := c2_mng_inElf mmpl hMm
  have hPl2 := mallocngLib_in_f3TrialElf.1
  have hIn2 := mallocngLib_in_f3TrialElf.2.1
  have hF3 := f3Trial_progContainsMallocng
  refine VerifiedLibraries.Mallocng.Proofs.ProgContainsMultiLib.of_noExterns hPl1 f3TrialRxProg_svc
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

private theorem c2_haclSubroutinesTrace_libcruxHmacSubProgRaw :
    HaclSubroutinesTrace libcruxHmacSubProgRaw c2HaclMpl := by
  refine haclSubroutinesTrace_ok c2_haclInProg_libcruxHmacSubProg ?_
  rw [c2HaclMpl_rho_memcpy]
  exact haclMemcpy_of_allocMemcpyVm c2_memcpy_aesCbcSubProgRaw_ok

private theorem c2_hmacAux_libcruxHmacSubProgRaw :
    HmacAuxSubroutines libcruxHmacSubProgRaw c2HaclMpl where
  shim_ok := by
    rw [c2HaclMpl_rho_shim]
    exact rustAllocShimVm_ret_ok
      (hasInstrs_aesCbcSubProgRaw_of_check (by rfl_kernel) (by decide))
  memcpy_ok := by
    rw [c2HaclMpl_rho_memcpy]
    apply subroutine_ok.of_codeLoaded
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _
    dsimp only [hmacMemcpyVmSpec] at hpre
    have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ (stackAt s0.sp 4096 ∗ R) := by
      dsimp only [allocMemcpyVmSpec]
      simpa only [sepConj_assoc] using hpre
    refine subroutine_ok.mono_outcome c2_memcpy_aesCbcSubProgRaw_ok (dst, src, bs)
      (stackAt s0.sp 4096 ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [allocMemcpyVmSpec] at hpost
      dsimp only [hmacMemcpyVmSpec]
      simp only [sepConj_assoc] at hpost ⊢
      rw [satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨hret0, hacp, hvm⟩, hspat⟩
      exact ⟨⟨hret0, hvm, hacp.2.1, hacp.1⟩, hspat⟩
    · dsimp only [allocMemcpyVmSpec] at hpan
      rw [satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · dsimp only [allocMemcpyVmSpec] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [allocMemcpyVmSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1
  handleError_ok := rustHandleErrorPanic_of_extern libcruxHmacSubProgRaw_externAt_handleError
  unwrapFailed_ok := rustHandleErrorPanic_of_extern libcruxHmacSubProgRaw_externAt_unwrapFailed

private theorem c2_hmacBudgetAlloc_libcruxHmacSubProgRaw [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) {lim : BudgetLimits}
    (hlim : lim ≠ zeroBudgetLimits) :
    HmacBudgetAllocSubroutines fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim
      libcruxHmacSubProgRaw c2HaclMpl := by
  refine ⟨?_, ?_, ?_⟩
  · rw [c2HaclMpl_rho_allocZeroed]
    exact c2_allocZeroed_withExecFrozen_ok hMm γ tp brkStart hlim
      aesCbcSubProg_svc (fun _ => aesCbcSubProg_codeLoaded_f3PrePanic)
      (fun _ => aesCbcSubProg_externAt_none_of_keepPrePanic)
  · rw [c2HaclMpl_rho_alloc]
    exact c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim
      aesCbcSubProg_svc (fun _ => aesCbcSubProg_codeLoaded_f3PrePanic)
      (fun _ => aesCbcSubProg_externAt_none_of_keepPrePanic)
  · rw [c2HaclMpl_rho_dealloc]
    exact c2_dealloc_withExecFrozen_ok hMm γ tp brkStart hlim
      aesCbcSubProg_svc (fun _ => aesCbcSubProg_codeLoaded_f3PrePanic)
      (fun _ => aesCbcSubProg_externAt_none_of_keepPrePanic)

theorem c2_hmacBudgetAlloc_f3TrialRxProg [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    HmacBudgetAllocSubroutines fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      f3TrialRxProg c2HaclMpl := by
  have hProgMng := c2_progContainsMallocng_f3TrialRxProg mmpl hMm
  have hShims := f3Trial_seg5ShimBundle.rdlShims
  rw [← c2_mng_cAddrs_eq mmpl hMm] at hShims
  have hEntries := fineHookRustCliAllocBudgetEntries_thunks hProgMng γ tp brkStart
    f3Trial_rustStdThunkCode hShims f3Trial_allocMemcpyVm_ok
  have hZero := f3Trial_seg5ShimBundle.allocZeroedInstrs
  rw [← c2_mng_fnAddr_eq mmpl hMm "calloc", ← c2_mng_cAddrs_eq mmpl hMm] at hZero
  refine ⟨?_, ?_, ?_⟩
  · rw [c2HaclMpl_rho_allocZeroed]
    exact fineHookRustCliAllocZeroedBudget_thunk_ok hProgMng γ tp brkStart
      f3StubAzAddr f3RdlAzAddr f3StdLayout.memsetAddr lim
      f3Trial_stubAz_hasInstrs hZero f3Trial_allocMemsetVm_ok
  · rw [c2HaclMpl_rho_alloc]
    exact hEntries.alloc lim
  · rw [c2HaclMpl_rho_dealloc]
    exact hEntries.dealloc lim

theorem c2_libcruxHmac_subroutineOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok libcruxHmacSubProg c2LibcruxHmacAddr
      (withHooksUnfetched libcruxHmacSubProg
        (withFsTraceExact (libcruxHmacSpecOf mmpl brkStart lim γ tp))) := by
  let lim' := nonZeroEquivLim lim
  have hlim' : lim' ≠ zeroBudgetLimits := nonZeroEquivLim_ne_zero lim
  let A0 := fineHookRustCliAllocBudget γ mmpl tp brkStart
  let A' := withExecFrozenBudget A0
  have hRaw := libcruxHmac_budget_fs_subroutineOk
    c2_haclInProg_libcruxHmacSubProg
    (fun m hCL => c2_libcruxHmacLib_codeLoaded_of_rxProg
      ((libcruxHmacSubProgRaw_codeLoaded_iff m).mp hCL))
    c2_haclSubroutinesTrace_libcruxHmacSubProgRaw
    c2_hmacAux_libcruxHmacSubProgRaw
    libcruxHmacSubProgRaw_externAt_unwrapFailed
    (c2_hmacBudgetAlloc_libcruxHmacSubProgRaw mmpl hMm γ tp brkStart hlim')
  rw [c2HaclMpl_base6, sha256CompressState_eq_spqrSha256Compress] at hRaw
  apply subroutine_ok.of_codeLoaded
  intro (x, st0) R s0 hpc hrun hpre hsp _
  dsimp only [withHooksUnfetched, withFsTraceExact, libcruxHmacSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hfr⟩, hpre_rest⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨_, hpre_bud⟩
  have hpre' : s0.mem ⊨
      (withFsTraceBudget (libcruxHmacBudgetSpec sha256Compress fineCostModel A' lim')).pre
        (x, st0) s0 ∗ R := by
    dsimp only [withFsTraceBudget, libcruxHmacBudgetSpec, A', A0, withExecFrozenBudget,
      lim'] at hpre_bud ⊢
    rw [fitsEnv_nonZeroEquivLim, fineHookPool_nonZeroEquivLim]
    refine Satisfies.mono ?_ hpre_bud
    exact Entails.trans
      (Entails.pure_right (fun (_ : lim' ≠ zeroBudgetLimits) => hfr) (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  refine subroutine_ok.mono_outcome hRaw (x, st0) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceBudget, libcruxHmacBudgetSpec, A', A0, lim'] at hpost
    dsimp only [withHooksUnfetched, withFsTraceExact, libcruxHmacSpecOf,
      withLsRet, libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hfs_tr, hpost⟩
    refine ⟨hfs_tr, ?_⟩
    rw [sepExists_sepConj_left] at hpost ⊢
    obtain ⟨evs, hpost⟩ := (satisfies_sepExists _ _).mp hpost
    refine (satisfies_sepExists _ _).mpr ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hev_pure, hpost⟩
    refine ⟨hev_pure, ?_⟩
    refine Satisfies.mono ?_ hpost
    exact sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono_left (withExecFrozenBudget_pool_entails γ mmpl tp brkStart lim _ sf)))))
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    simpa only [withHooksUnfetched, withFsTraceExact, libcruxHmacSpecOf,
      withLsRet, withFsTraceBudget, libcruxHmacBudgetSpec] using hpan
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem c2_keepRxSeg_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → keepRxSeg a = true := by
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
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable mmpl hMm) (c2_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have hhi_rx : f3MngCodeHi ≤ f3RxSegBase.toNat + 4 * f3RxWordCount := by decide
    have hrx_nat : f3RxSegBase.toNat < 2 ^ 64 := BitVec.isLt f3RxSegBase
    have hsub_nat : (a - f3RxSegBase).toNat = a.toNat - f3RxSegBase.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    rw [keepRxSeg_eq_lt]
    exact decide_eq_true (by omega)

theorem c2_libcruxHmacGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsLibcruxHmacSym
      (libcruxHmacGhost keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  libcruxHmacGhost_rowSpecOk keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim

theorem c2_libcruxHmac_hKeep [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr) :
    keepRxSeg lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hRet
  have hstub_le : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  have hrx_hi : f3RxSegBase.toNat + 4 * f3RxWordCount < 2 ^ 64 := by decide
  rw [keepRxSeg_eq_lt, decide_eq_false_iff_not]
  intro hlt_rx
  have hl_lt : lr.toNat < f3RxSegBase.toNat := Nat.lt_of_lt_of_le hlt hstub_le
  have hwrap : (lr - f3RxSegBase).toNat = 2 ^ 64 + lr.toNat - f3RxSegBase.toNat := by
    rw [BitVec.toNat_sub]
    omega
  omega

theorem c2_libcruxHmac_hlr_ne_stub [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hRet : LsRetAddr624 lr)
    (pc : BitVec 64) (f : State → State)
    (he : libcruxHmacSubProg.externAt? pc = some f) :
    pc ≠ lr :=
  c2_aesCbc_hlr_ne_stub hLs lr hRet pc f he

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
