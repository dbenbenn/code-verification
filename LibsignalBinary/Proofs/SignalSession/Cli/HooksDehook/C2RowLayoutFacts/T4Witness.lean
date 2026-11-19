/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8
import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
import LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256RxSlice
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import ProofLib.Placed.LabelsCoverage
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux

/-!
# Cutover-2 (`C2`) T4 Kernel-Closed Layout Witnesses (`C2RowLayoutFacts.T4Witness`)

**Checked by Lean. Untrusted (`Role::Proof`, `CliElfLib`).**

Closes all four `.text.lib2` / `.rodata.lib2` layout-fact bundles on `cliElfBytes`:
1. **`c2RoSliceFacts : C2RoSliceFacts`:** `rfl_kernel` `.rodata.lib2` segment-slice checks for
   `c2FromUtf8TableAddr` (`UTF8_CHAR_WIDTH`, `256` B) and `c2DurationSinceCst16Addr`
   (`1_u128`, `16` B) on `f3PatchedElf`.
2. **`c2ResolveFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** Symbol-resolved entry equalities across
   all `10` de-hooked C2 rows under `libsignalSessionLib.LinkedAt cliElfBytes mpl`.
3. **`c2Lib2RxSliceFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** `rfl_kernel` linear byte-subslice
   checks `checkProgCodeSubslice f3TrialRxProg <rowSubProg> = true` across all `10` de-hooked C2
   rows.
4. **`c2ExternTableFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** Block-`617` real & ghost `externAt?`
   identities and `.text.lib2` / `.text.b_pre` hull memberships across `c2RxDehookedSyms`.
5. **Bundle-free per-row `GhostRowOk` corollaries (`c2_<row>Ghost_rowOk[_guardOf]_of_linkedAt`):**
   Direct `LinkedAt`-only `GhostRowOk` instantiations across all `10` de-hooked C2 rows at
   `mpl := lsmpl`, eliminating every `C2*Facts` binder from consumer call sites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Musl (memmoveLibcaCalls memmoveLibcaWords)
open CryptoVerification (LibsignalPlacement libsignalHookedExterns libsignalSessionExterns lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliCratePanicSyms cliElfBytes cliExternsPlaced cliPanicSymbolsLinked
   cliPanicSymbolsPlaced isCliPanicSymbolPlaced libsignalSessionLib lsAesDecSym lsAesEncSym
   lsBlackBoxSym lsCompress256Sym lsDurationSinceSym lsFromUtf8Sym lsLibcruxHmacSym lsMemrchrSym
   lsSharedSecretDropSym lsSpqrOnceCallSym lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (blackBoxU8Words)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (zeroize32Words)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (f3ByteBeq f3ByteBeq_true_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecEntryGuard aesDecGhost aesEncEntryGuard aesEncGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (bcmpHullWords memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost bcmpHullBase bcmpSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost blackBoxSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts
  (C2Lib2RxSliceFacts C2ResolveFacts
   c2_aesDecGhost_rowOk c2_aesDecGhost_rowOk_guardOf
   c2_aesEncGhost_rowOk c2_aesEncGhost_rowOk_guardOf
   c2_bcmpGhost_rowOk c2_bcmpGhost_rowOk_guardOf
   c2_blackBoxGhost_rowOk c2_blackBoxGhost_rowOk_guardOf
   c2_compress256Ghost_rowOk c2_compress256Ghost_rowOk_guardOf
   c2_durationSinceGhost_rowOk c2_durationSinceGhost_rowOk_guardOf
   c2_fromUtf8Ghost_rowOk c2_fromUtf8Ghost_rowOk_guardOf
   c2_libcruxHmacGhost_rowOk c2_libcruxHmacGhost_rowOk_guardOf
   c2_memmoveGhost_rowOk c2_memmoveGhost_rowOk_guardOf
   c2_memrchrGhost_rowOk c2_memrchrGhost_rowOk_guardOf
   c2_staticSecretDropGhost_rowOk c2_staticSecretDropGhost_rowOk_guardOf
   c2_strlenGhost_rowOk c2_strlenGhost_rowOk_guardOf
   c2_timeAddGhost_rowOk c2_timeAddGhost_rowOk_guardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg c2AesDecAddr c2AesEncAddr c2_aesCbcSubProg_subslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256RxSlice
  (c2_rxSlice_compress256_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
  (libcruxHmacSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen libsignalSessionExterns_resolve_eq_rho resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time (c2TimeMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617 externAt?_cliProgExtPlacedAt_617_of_unique_resolve
   ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256EntryGuard compress256Ghost compress256SubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceEntryGuard durationSinceGhost durationSinceSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost fromUtf8SubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (fromUtf8Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacEntryGuard libcruxHmacGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
  (bPreHullWords bPreMemmoveByteOff bPrePadWord)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (memcpyEntry memmoveEntryGuard memmoveGhost memmoveHullWords memmoveSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
  (memrchrEntryGuard memrchrGhost memrchrSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrOnceCallGhostReplays
  (c2Blk321SubProg c2Blk385SubProg c2Cas4AcqSubProg c2GetauxvalSubProg c2HwcapSubProg
   c2OnceCallAddr c2OnceCallSubProg c2Swp4RelSubProg keepSpqrOnceCall spqrOnceCallEntryGuard
   spqrOnceCallGhost spqrOnceCallGhost_rowOk_guardOf spqrProbeGuard_of_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (staticSecretDropEntryGuard staticSecretDropGhost staticSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (strlenEntry strlenEntryGuard strlenGhost strlenSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (timeAddEntryGuard timeAddGhost timeAddSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (ls_idsOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts c2CorePlacedData1 c2TimePlacedData0 cliLinkedPanicAddrs
   f3RxSeg_realProg617_externAt_none isLinkedPanicAddr keepLib2Text keepTextBPre)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_externs_distinct_of_linkedAt cliElf_linkedAt cliElf_linkedAt_unique
   lsInternedMultiLib lsSharedExterns ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BatchLDehookedSyms c2BcmpAddr c2BlackBoxAddr c2Compress256Addr c2Compress256K32Addr
   c2DurationSinceAddr c2DurationSinceCst16Addr c2FirstExternStubAddr c2FromUtf8Addr
   c2FromUtf8TableAddr c2Lib2DehookedSyms c2LibcruxHmacAddr c2MemmoveAddr c2MemrchrAddr
   c2RxDehookedSyms c2SharedSecretDropAddr c2StaticSecretDropAddr c2StrlenAddr c2TimeAddAddr
   hole2_keepSubHi hole2_keepSubLo wp4MemcpyRealAddr)

/-! ## 1. `.rodata.lib2` Slice Witness (`c2RoSliceFacts`) -/

private noncomputable def checkT4RoAll (elf : Process.ElfImage) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) f3StdLayout.roSegIdx none with
  | none => false
  | some seg =>
    let roLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.ro) &&
    checkSegSlice seg roLen c2FromUtf8TableAddr c2CorePlacedData1 &&
    checkSegSlice seg roLen c2DurationSinceCst16Addr c2TimePlacedData0 &&
    checkSegSlice seg roLen c2Compress256K32Addr sha256KBytes

set_option maxRecDepth 4000000 in
private theorem c2_roSlices_all_ok : checkT4RoAll f3PatchedElf = true := by
  rfl_kernel

private theorem rGetD_map_some_eq_getElem?_local {α : Type} :
    ∀ (xs : List α) (i : Nat),
      ProofLib.Placed.Split.rGetD (xs.map some) i none = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => rGetD_map_some_eq_getElem?_local xs i

theorem c2RoSliceFacts : C2RoSliceFacts := by
  have h := c2_roSlices_all_ok
  unfold checkT4RoAll at h
  rw [rGetD_map_some_eq_getElem?_local] at h
  cases hseg : f3PatchedElf.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hperm, h1⟩, h2⟩, h3⟩
    exact
      { fromUtf8Slice := ⟨seg, hseg, hperm, h1⟩
        durationSinceSlice := ⟨seg, hseg, hperm, h2⟩
        compress256K32Slice := ⟨seg, hseg, hperm, h3⟩ }

/-! ## 2. Symbol-Resolution Witness (`c2ResolveFacts_*`) -/

theorem c2ResolveFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2ResolveFacts mpl where
  fromUtf8_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  durationSince_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  timeAdd_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  memrchr_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  strlen_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  bcmp_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  memmove_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  dalek :=
    { blackBox_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel)
      sharedSecretDrop_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel)
      staticSecretDrop_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel) }
  compress256_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  libcruxHmac_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  aesEnc_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  aesDec_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)

theorem c2ResolveFacts_cliElf : C2ResolveFacts cliElfMultiPlacement :=
  c2ResolveFacts_of_linkedAt cliElf_linkedAt

theorem c2ResolveFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2ResolveFacts lsmpl :=
  c2ResolveFacts_of_linkedAt hLs

private theorem resolve_memcpy_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl "memcpy" = wp4MemcpyRealAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
    (by rfl_kernel)

/-! ## 3. RX Byte-Subslice Witness (`c2Lib2RxSliceFacts_*`) -/

private theorem patchCalls_memmoveLibcaCalls_congr
    (words : List (BitVec 32)) (a : BitVec 64)
    (r1 r2 : String → BitVec 64) (h : r1 "memcpy" = r2 "memcpy") :
    Obj.patchCalls memmoveLibcaCalls words a r1 =
      Obj.patchCalls memmoveLibcaCalls words a r2 := by
  unfold Obj.patchCalls
  refine congrArg (fun fn => words.mapIdx fn) (funext fun j => funext fun w => ?_)
  cases hp : ((104 : Nat) == 4 * j)
  · simp [List.find?, hp]
  · simp [List.find?, hp, h]

private theorem memmoveSubProg_eq_closed {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    memmoveSubProg mpl =
      pureWordsProg wp4MemcpyRealAddr
        (bPreHullWords wp4MemcpyRealAddr (fun _ => wp4MemcpyRealAddr) bPrePadWord) := by
  have hm : libsignalSessionLib.resolve mpl "memcpy" = wp4MemcpyRealAddr :=
    resolve_memcpy_eq_of_linkedAt hLs
  unfold memmoveSubProg memmoveHullWords memcpyEntry bPreHullWords
  rw [hm, patchCalls_memmoveLibcaCalls_congr memmoveLibcaWords
    (wp4MemcpyRealAddr + bPreMemmoveByteOff) (libsignalSessionLib.resolve mpl)
    (fun _ => wp4MemcpyRealAddr) hm]

private theorem rxProg_code_len_eq :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size]

private def checkBytesMatchWordTree : WordTree → Nat → List (BitVec 8) → Bool
  | _, _, [] => true
  | wt, q, b0 :: b1 :: b2 :: b3 :: rest =>
    match wt.getQuad? q with
    | some (a0, a1, a2, a3) =>
      f3ByteBeq a0 b0 && f3ByteBeq a1 b1 && f3ByteBeq a2 b2 && f3ByteBeq a3 b3 &&
      checkBytesMatchWordTree wt (q + 1) rest
    | none => false
  | _, _, _ => false

private def checkRxSubProgByTree (subProg : Program) : Bool :=
  let off := (subProg.base - f3RxSegBase).toNat
  let q := off / 4
  Nat.beq (subProg.base.toNat % 4) 0 &&
  Nat.beq (4 * q) off &&
  Nat.ble (subProg.base.toNat + subProg.code.length) (2 ^ 64) &&
  decide (f3RxSegBase + BitVec.ofNat 64 off = subProg.base) &&
  Nat.ble (off + subProg.code.length) (4 * f3RxWordCount) &&
  checkBytesMatchWordTree f3TrialRxWordTree q subProg.code

private theorem drop_add_four {α : Type} :
    ∀ (xs : List α) (n : Nat), xs.drop (n + 4) = (xs.drop n).drop 4
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: xs, n + 1 => by
    rw [Nat.succ_add]
    exact drop_add_four xs n

private theorem bytesMatchWordTree_sound {wt : WordTree} {nWords : Nat}
    (hsz : wt.checkSize? = some nWords) :
    ∀ (q : Nat) (bs : List (BitVec 8)),
      checkBytesMatchWordTree wt q bs = true →
      (wt.toBytes.drop (4 * q)).take bs.length = bs
  | _, [], _ => rfl
  | _, [_], hok => by simp [checkBytesMatchWordTree] at hok
  | _, [_, _], hok => by simp [checkBytesMatchWordTree] at hok
  | _, [_, _, _], hok => by simp [checkBytesMatchWordTree] at hok
  | q, b0 :: b1 :: b2 :: b3 :: rest, hok => by
    unfold checkBytesMatchWordTree at hok
    cases hg : wt.getQuad? q with
    | none => rw [hg] at hok; simp at hok
    | some quad =>
      rcases quad with ⟨a0, a1, a2, a3⟩
      rw [hg] at hok
      simp only [Bool.and_eq_true, f3ByteBeq_true_iff] at hok
      rcases hok with ⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, hrest⟩
      subst e0; subst e1; subst e2; subst e3
      obtain ⟨tail, hdrop⟩ := WordTree.toBytes_drop_of_getQuad? hsz hg
      have hdrop4 : wt.toBytes.drop (4 * (q + 1)) = tail := by
        have h4 : 4 * (q + 1) = 4 * q + 4 := by omega
        rw [h4, drop_add_four, hdrop]; rfl
      have ih := bytesMatchWordTree_sound hsz (q + 1) rest hrest
      rw [hdrop4] at ih
      rw [hdrop]
      simp only [List.length_cons, List.take_succ_cons]
      exact congrArg (List.cons a0)
        (congrArg (List.cons a1) (congrArg (List.cons a2) (congrArg (List.cons a3) ih)))

private theorem checkProgCodeSubslice_of_checkRxSubProgByTree {subProg : Program}
    (hok : checkRxSubProgByTree subProg = true) :
    checkProgCodeSubslice f3TrialRxProg subProg = true := by
  unfold checkRxSubProgByTree at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨hAlign, hq⟩, hNoWrap⟩, hBaseEq⟩, hBound⟩, hMatch⟩
  have htake := bytesMatchWordTree_sound f3TrialRxWordTree_size
    ((subProg.base - f3RxSegBase).toNat / 4) subProg.code hMatch
  rw [hq] at htake
  unfold checkProgCodeSubslice
  rw [f3TrialRxProg_base]
  dsimp only
  rw [rxProg_code_len_eq, f3TrialRxWordTree_eq, htake]
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq, beq_self_eq_true]
  exact ⟨⟨⟨⟨hAlign, hNoWrap⟩, hBaseEq⟩, hBound⟩, trivial⟩

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_fromUtf8_ok :
    checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_durationSince_ok :
    checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_timeAdd_ok :
    checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_blackBox_ok :
    checkProgCodeSubslice f3TrialRxProg (pureWordsProg c2BlackBoxAddr blackBoxU8Words) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_staticSecretDrop_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2StaticSecretDropAddr zeroize32Words) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_memrchr_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2MemrchrAddr coreMemrchrWords) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_strlen_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2StrlenAddr muslStrlenWords) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_bcmp_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg (c2BcmpAddr - memcmpByteLen)
        (bcmpHullWords (c2BcmpAddr - memcmpByteLen))) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_memmove_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg wp4MemcpyRealAddr
        (bPreHullWords wp4MemcpyRealAddr (fun _ => wp4MemcpyRealAddr) bPrePadWord)) = true :=
  checkProgCodeSubslice_of_checkRxSubProgByTree (by rfl_kernel)

private theorem c2_rxSlice_libcruxHmac_ok :
    checkProgCodeSubslice f3TrialRxProg libcruxHmacSubProg = true := by
  have hbase : libcruxHmacSubProg.base = f3TrialRxProg.base := rfl
  have hcode : libcruxHmacSubProg.code = f3TrialRxProg.code := rfl
  unfold checkProgCodeSubslice
  rw [hbase, hcode, BitVec.sub_self, BitVec.toNat_zero]
  dsimp only
  rw [List.drop_zero, List.take_length, beq_self_eq_true, f3TrialRxProg_base, rxProg_code_len_eq]
  decide

theorem c2Lib2RxSliceFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2Lib2RxSliceFacts mpl := by
  have hRes := c2ResolveFacts_of_linkedAt hLs
  refine
    { fromUtf8 := c2_rxSlice_fromUtf8_ok
      durationSince := c2_rxSlice_durationSince_ok
      timeAdd := c2_rxSlice_timeAdd_ok
      blackBox := ?_
      staticSecretDrop := ?_
      memrchr := ?_
      strlen := ?_
      bcmp := ?_
      memmove := ?_
      compress256 := c2_rxSlice_compress256_ok
      libcruxHmac := c2_rxSlice_libcruxHmac_ok
      aesCbc := c2_aesCbcSubProg_subslice }
  · unfold blackBoxSubProg; rw [hRes.blackBox_eq]; exact c2_rxSlice_blackBox_ok
  · unfold staticSecretDropSubProg; rw [hRes.staticSecretDrop_eq]; exact c2_rxSlice_staticSecretDrop_ok
  · unfold memrchrSubProg; rw [hRes.memrchr_eq]; exact c2_rxSlice_memrchr_ok
  · unfold strlenSubProg strlenEntry; rw [hRes.strlen_eq]; exact c2_rxSlice_strlen_ok
  · unfold bcmpSubProg bcmpHullBase; rw [hRes.bcmp_eq]; exact c2_rxSlice_bcmp_ok
  · rw [memmoveSubProg_eq_closed hLs]; exact c2_rxSlice_memmove_ok

theorem c2Lib2RxSliceFacts_cliElf : C2Lib2RxSliceFacts cliElfMultiPlacement :=
  c2Lib2RxSliceFacts_of_linkedAt cliElf_linkedAt

theorem c2Lib2RxSliceFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2Lib2RxSliceFacts lsmpl :=
  c2Lib2RxSliceFacts_of_linkedAt hLs

/-! ## 4. Block-`617` Extern-Table & Hull Membership Witness (`c2ExternTableFacts_*`) -/

private theorem f3RxSegBase_eq_lo :
    f3RxSegBase = BitVec.ofNat 64 hole2_keepSubLo := by
  rfl_kernel

private theorem f3RxByteLen_eq :
    4 * f3RxWordCount = hole2_keepSubHi - hole2_keepSubLo := by
  rfl_kernel

private theorem progKeep_f3TrialRxProg_bounds {pc : BitVec 64}
    (h : progKeep f3TrialRxProg pc = true) :
    hole2_keepSubLo ≤ pc.toNat ∧ pc.toNat < hole2_keepSubHi := by
  unfold progKeep at h
  rw [f3TrialRxProg_base, f3RxSegBase_eq_lo, rxProg_code_len_eq, f3RxByteLen_eq,
    decide_eq_true_eq] at h
  unfold hole2_keepSubLo hole2_keepSubHi at h ⊢
  bv_omega

set_option maxRecDepth 2000000 in
private theorem c2RxDehookedSyms_unhooked :
    (c2RxDehookedSyms.all fun s =>
      !(cliCratePanicSyms.contains s || Arm64.Obj.isPanicSymbolFast s) ||
        isLinkedPanicAddr (cliElfMultiPlacement.ρ s)) = true := by
  rfl_kernel

private theorem cliExternsPlaced_eq_none_of_c2Rx
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {s : String}
    (hs : s ∈ c2RxDehookedSyms)
    (hnp : isLinkedPanicAddr (cliElfMultiPlacement.ρ s) = false) :
    cliExternsPlaced mmpl W s = none := by
  have hall := List.all_eq_true.mp c2RxDehookedSyms_unhooked s hs
  rw [hnp, Bool.or_false, Bool.not_eq_true'] at hall
  unfold cliExternsPlaced isCliPanicSymbolPlaced
  rw [Arm64.Obj.rust_isPanicSymbol_eq_fast, hall]
  rfl

private theorem findSome?_eq_none_of_forall {α γ : Type}
    {xs : List α} {g : α → Option γ}
    (h : ∀ e ∈ xs, g e = none) :
    xs.findSome? g = none := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.findSome?_cons, h a (.head _)]
    exact ih (fun e he => h e (.tail _ he))

private theorem findSome?_eq_none_of_forall_ne {α β γ : Type} [BEq β] [LawfulBEq β]
    {xs : List α} {f : α → β} (g : α → Option γ) {v : β}
    (hne : ∀ e ∈ xs, f e ≠ v) :
    (xs.findSome? fun e => if f e == v then g e else none) = none := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : (f a == v) = false := beq_eq_false_iff_ne.mpr (hne a (.head _))
    simp only [List.findSome?_cons, ha, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun e he => hne e (.tail _ he))

set_option maxRecDepth 4000000 in
private theorem sharedExterns_lookup_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true :=
  ⟨by rfl_kernel, by rfl_kernel⟩

private theorem resolve_extern_eq_cliElf_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {e : String} (he : e ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve mpl e = cliElfMultiPlacement.ρ e := by
  have hres_rho := libsignalSessionExterns_resolve_eq_rho mpl e he
  have huniq := (cliElf_linkedAt_unique hLs).2.2.1
  rw [sharedExterns_lookup_ok.1, List.mem_map] at he
  rcases he with ⟨idx, hidx, rfl⟩
  have hall := List.all_eq_true.mp sharedExterns_lookup_ok.2 idx hidx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hall
  have hmem : lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
    rw [Obj.Interned.getD_of_lt hall.1]
    exact List.getElem_mem hall.1
  have hnone :
      Obj.lookupBlockSym (lsInternedMultiLib.names.getD idx "") libsignalSessionLib.blocks =
        none := by
    rw [ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hall.1]
    exact hall.2
  exact hres_rho.trans (huniq _ hmem hnone)

set_option maxRecDepth 4000000 in
private theorem externs_in_rx_sub_c2RxDehooked :
    (libsignalSessionExterns.all fun e =>
      let a := (cliElfMultiPlacement.ρ e).toNat
      !(Nat.ble hole2_keepSubLo a && Nat.blt a hole2_keepSubHi) || c2RxDehookedSyms.contains e) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2RxDehookedSyms_sub_externs :
    (c2RxDehookedSyms.all fun s => libsignalSessionExterns.contains s) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2Lib2DehookedSyms_in_keepLib2Text :
    (c2Lib2DehookedSyms.all fun s =>
      c2RxDehookedSyms.contains s && keepLib2Text (cliElfMultiPlacement.ρ s)) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2BatchLDehookedSyms_in_keepTextBPre :
    (c2BatchLDehookedSyms.all fun s =>
      c2RxDehookedSyms.contains s && keepTextBPre (cliElfMultiPlacement.ρ s)) = true := by
  rfl_kernel

theorem c2ExternTableFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2ExternTableFacts mpl where
  realRxNoExtern mmpl W {pc} hpc hnp := by
    obtain ⟨hk_lo, hk_hi⟩ := progKeep_f3TrialRxProg_bounds hpc
    rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
    refine findSome?_eq_none_of_forall fun e he => ?_
    by_cases hres_eq : libsignalSessionLib.resolve mpl e = pc
    · have hrho : cliElfMultiPlacement.ρ e = pc :=
        (resolve_extern_eq_cliElf_rho hLs he).symm.trans hres_eq
      have hall := List.all_eq_true.mp externs_in_rx_sub_c2RxDehooked e he
      dsimp only at hall
      rw [hrho, Nat.ble_eq.mpr hk_lo, Nat.blt_eq.mpr hk_hi] at hall
      simp only [Bool.true_and, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hall
      rw [cliExternsPlaced_eq_none_of_c2Rx mmpl W hall (hrho.symm ▸ hnp), ite_self]
    · simp [beq_eq_false_iff_ne.mpr hres_eq]
  ghostRxNoExternIfAllNoneAtPc extFn W {pc} hpc hall := by
    obtain ⟨hk_lo, hk_hi⟩ := progKeep_f3TrialRxProg_bounds hpc
    rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
    refine findSome?_eq_none_of_forall fun e he => ?_
    by_cases hres_eq : libsignalSessionLib.resolve mpl e = pc
    · have hrho : cliElfMultiPlacement.ρ e = pc :=
        (resolve_extern_eq_cliElf_rho hLs he).symm.trans hres_eq
      have hsub := List.all_eq_true.mp externs_in_rx_sub_c2RxDehooked e he
      dsimp only at hsub
      rw [hrho, Nat.ble_eq.mpr hk_lo, Nat.blt_eq.mpr hk_hi] at hsub
      simp only [Bool.true_and, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hsub
      rw [hall e hsub hres_eq, ite_self]
    · simp [beq_eq_false_iff_ne.mpr hres_eq]
  ghostRxNoExternOffEntries extFn W {pc} hpc hnotin := by
    obtain ⟨hk_lo, hk_hi⟩ := progKeep_f3TrialRxProg_bounds hpc
    rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
    refine findSome?_eq_none_of_forall_ne (extFn W) fun e he hres_eq => ?_
    have hrho : cliElfMultiPlacement.ρ e = pc :=
      (resolve_extern_eq_cliElf_rho hLs he).symm.trans hres_eq
    have hall := List.all_eq_true.mp externs_in_rx_sub_c2RxDehooked e he
    dsimp only at hall
    rw [hrho, Nat.ble_eq.mpr hk_lo, Nat.blt_eq.mpr hk_hi] at hall
    simp only [Bool.true_and, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hall
    exact hnotin (hres_eq ▸ List.mem_map_of_mem hall)
  ghostRxEntry extFn W {sym} hsym hhooked := by
    have hMemExt : sym ∈ libsignalSessionExterns :=
      List.contains_iff_mem.mp (List.all_eq_true.mp c2RxDehookedSyms_sub_externs sym hsym)
    have hMem617 : sym ∈ (libsignalSessionLib.blockLib 617).text.externs := by
      rwa [ls_block617_externs_eq_libsignalSessionExterns]
    have hDist := cliElf_externs_distinct_of_linkedAt hLs
    refine externAt?_cliProgExtPlacedAt_617_of_unique_resolve hMem617 (fun e he hres => ?_) W
    rw [ls_block617_externs_eq_libsignalSessionExterns] at he
    rw [libsignalSessionExterns_resolve_eq_rho mpl e he,
      libsignalSessionExterns_resolve_eq_rho mpl sym hMemExt] at hres
    exact hDist sym hhooked e he hres
  lib2InKeep {sym} hsym := by
    have hall := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp c2Lib2DehookedSyms_in_keepLib2Text sym hsym)
    have hmem : sym ∈ c2RxDehookedSyms := List.contains_iff_mem.mp hall.1
    rw [resolve_c2RxSym_eq_cliElf_rho hLs hmem]
    exact hall.2
  batchLInKeep {sym} hsym := by
    have hall := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp c2BatchLDehookedSyms_in_keepTextBPre sym hsym)
    have hmem : sym ∈ c2RxDehookedSyms := List.contains_iff_mem.mp hall.1
    rw [resolve_c2RxSym_eq_cliElf_rho hLs hmem]
    exact hall.2

theorem c2ExternTableFacts_cliElf : C2ExternTableFacts cliElfMultiPlacement :=
  c2ExternTableFacts_of_linkedAt cliElf_linkedAt

theorem c2ExternTableFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2ExternTableFacts lsmpl :=
  c2ExternTableFacts_of_linkedAt hLs

/-! ## 5. Bundle-Free Per-Row `GhostRowOk` Corollaries at `mpl := lsmpl` -/

theorem c2_fromUtf8Ghost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (fromUtf8EntryGuard lsmpl)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8Ghost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_fromUtf8Ghost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hGuard : ∀ s0 : State, guardOf lsFromUtf8Sym s0 → fromUtf8EntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (guardOf lsFromUtf8Sym)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8Ghost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_durationSinceGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (durationSinceEntryGuard lsmpl)
      (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_durationSinceGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (guardOf lsDurationSinceSym)
      (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_timeAddGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (timeAddEntryGuard lsmpl)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_timeAddGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (guardOf lsTimeAddSym)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_blackBoxGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (blackBoxEntryGuard lsmpl)
      (blackBoxGhost lsmpl mmpl) :=
  c2_blackBoxGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_blackBoxGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsBlackBoxSym s0 → blackBoxEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (guardOf lsBlackBoxSym)
      (blackBoxGhost lsmpl mmpl) :=
  c2_blackBoxGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_staticSecretDropGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (staticSecretDropEntryGuard lsmpl)
      (staticSecretDropGhost lsmpl mmpl) :=
  c2_staticSecretDropGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_staticSecretDropGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsStaticSecretDropSym s0 → staticSecretDropEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (guardOf lsStaticSecretDropSym)
      (staticSecretDropGhost lsmpl mmpl) :=
  c2_staticSecretDropGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memrchrGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (memrchrEntryGuard lsmpl)
      (memrchrGhost lsmpl mmpl) :=
  c2_memrchrGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memrchrGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (guardOf lsMemrchrSym)
      (memrchrGhost lsmpl mmpl) :=
  c2_memrchrGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_strlenGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (strlenEntryGuard lsmpl)
      (strlenGhost lsmpl mmpl) :=
  c2_strlenGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_strlenGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "strlen" s0 → strlenEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (guardOf "strlen")
      (strlenGhost lsmpl mmpl) :=
  c2_strlenGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_bcmpGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (bcmpEntryGuard lsmpl)
      (bcmpGhost lsmpl mmpl) :=
  c2_bcmpGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_bcmpGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "bcmp" s0 → bcmpEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (guardOf "bcmp")
      (bcmpGhost lsmpl mmpl) :=
  c2_bcmpGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memmoveGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (memmoveEntryGuard lsmpl)
      (memmoveGhost lsmpl mmpl) :=
  c2_memmoveGhost_rowOk mmpl PredFs g extra hLook hGMemcpy hGMemset
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memmoveGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "memmove" s0 → memmoveEntryGuard lsmpl s0)
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (guardOf "memmove")
      (memmoveGhost lsmpl mmpl) :=
  c2_memmoveGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard hGMemcpy hGMemset
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_compress256Ghost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsCompress256Sym
      (compress256EntryGuard lsmpl)
      (compress256Ghost c2Compress256Pl) :=
  c2_compress256Ghost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_compress256Ghost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsCompress256Sym
      (guardOf lsCompress256Sym)
      (compress256Ghost c2Compress256Pl) :=
  c2_compress256Ghost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_libcruxHmacGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsLibcruxHmacSym
      (libcruxHmacEntryGuard lsmpl)
      (libcruxHmacGhost C2RowLayoutFacts.LibcruxHmac.keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  c2_libcruxHmacGhost_rowOk mmpl brkStart lim PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm

theorem c2_libcruxHmacGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsLibcruxHmacSym
      (guardOf lsLibcruxHmacSym)
      (libcruxHmacGhost C2RowLayoutFacts.LibcruxHmac.keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  c2_libcruxHmacGhost_rowOk_guardOf mmpl brkStart lim PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm

theorem c2_aesEncGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesEncSym
      (aesEncEntryGuard lsmpl)
      (aesEncGhost C2RowLayoutFacts.AesCbc.keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  c2_aesEncGhost_rowOk mmpl brkStart lim PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm hbrk

theorem c2_aesEncGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesEncSym
      (guardOf lsAesEncSym)
      (aesEncGhost C2RowLayoutFacts.AesCbc.keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  c2_aesEncGhost_rowOk_guardOf mmpl brkStart lim PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm hbrk

theorem c2_aesDecGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (aesDecEntryGuard lsmpl)
      (aesDecGhost C2RowLayoutFacts.AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecGhost_rowOk mmpl brkStart lim PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm hbrk

theorem c2_aesDecGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (guardOf lsAesDecSym)
      (aesDecGhost C2RowLayoutFacts.AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecGhost_rowOk_guardOf mmpl brkStart lim PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2ExternTableFacts_lsmpl hLs) hLs hMm hbrk

/-! ## 6. Row 38 (`lsSpqrOnceCallSym`) Resolve, `hRealHullNoExt`, & `GhostRowOk` Witnesses -/

set_option maxRecDepth 400000 in
theorem c2_resolve_spqrOnceCall_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsSpqrOnceCallSym = c2OnceCallAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans (by rfl_kernel)

private theorem progKeep_f3TrialRxProg_of_bounds {pc : BitVec 64}
    (hlo : hole2_keepSubLo ≤ pc.toNat) (hhi : pc.toNat < hole2_keepSubHi) :
    progKeep f3TrialRxProg pc = true := by
  unfold progKeep
  rw [f3TrialRxProg_base, f3RxSegBase_eq_lo, rxProg_code_len_eq, f3RxByteLen_eq,
    decide_eq_true_eq]
  unfold hole2_keepSubLo at hlo ⊢
  unfold hole2_keepSubHi at hhi ⊢
  bv_omega

private theorem progKeep_rx_and_noPanic_of_sub {P : Program}
    (hlo : hole2_keepSubLo ≤ P.base.toNat)
    (hhi : P.base.toNat + P.code.length ≤ hole2_keepSubHi)
    (hnp_all : (cliLinkedPanicAddrs.all fun p => !(progKeep P p)) = true)
    {pc : BitVec 64} (hk : progKeep P pc = true) :
    progKeep f3TrialRxProg pc = true ∧ isLinkedPanicAddr pc = false := by
  have hhi_bound : hole2_keepSubHi < 2 ^ 48 := by decide
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk
  generalize hd : pc - P.base = d at hk
  have hpc_eq : pc = P.base + d := by subst hd; bv_omega
  have hpc_nat : pc.toNat = P.base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨progKeep_f3TrialRxProg_of_bounds (by omega) (by omega), ?_⟩
  cases hpan : isLinkedPanicAddr pc with
  | false => rfl
  | true =>
    have hmem : pc ∈ cliLinkedPanicAddrs := List.contains_iff_mem.mp hpan
    have hn := List.all_eq_true.mp hnp_all pc hmem
    unfold progKeep at hn
    rw [hd, decide_eq_true_eq.mpr hk] at hn
    nomatch hn

set_option maxRecDepth 4000000 in
private theorem panic_externs_ge_firstExternStub :
    (libsignalSessionExterns.all fun e =>
      !(cliCratePanicSyms.contains e || Arm64.Obj.isPanicSymbolFast e) ||
        Nat.ble c2FirstExternStubAddr.toNat (cliElfMultiPlacement.ρ e).toNat) = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
private theorem blk321_hi_le_stub :
    Nat.ble ((cliElfMultiPlacement.base 321).toNat + 48) c2FirstExternStubAddr.toNat = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
private theorem blk385_hi_le_stub :
    Nat.ble ((cliElfMultiPlacement.base 385).toNat + 68) c2FirstExternStubAddr.toNat = true := by
  rfl_kernel

private theorem externAt_none_of_progKeep_lt_stub {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {P : Program}
    (hhi : P.base.toNat + P.code.length ≤ c2FirstExternStubAddr.toNat)
    (W : CliHooks) {pc : BitVec 64} (hk : progKeep P pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  have hstub_bound : c2FirstExternStubAddr.toNat < 2 ^ 48 := by decide
  unfold progKeep at hk
  rw [decide_eq_true_eq] at hk
  generalize hd : pc - P.base = d at hk
  have hpc_eq : pc = P.base + d := by subst hd; bv_omega
  have hpc_nat : pc.toNat = P.base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hpc_lt : pc.toNat < c2FirstExternStubAddr.toNat := by omega
  rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
  refine findSome?_eq_none_of_forall fun e he => ?_
  by_cases hres : libsignalSessionLib.resolve mpl e = pc
  · have hrho : cliElfMultiPlacement.ρ e = pc :=
      (resolve_extern_eq_cliElf_rho hLs he).symm.trans hres
    have hall := List.all_eq_true.mp panic_externs_ge_firstExternStub e he
    have hble_false : Nat.ble c2FirstExternStubAddr.toNat (cliElfMultiPlacement.ρ e).toNat = false := by
      rw [hrho]
      exact Bool.eq_false_iff.mpr fun h => by have := Nat.ble_eq.mp h; omega
    rw [hble_false, Bool.or_false, Bool.not_eq_true'] at hall
    have hnone : cliExternsPlaced mmpl W e = none := by
      unfold cliExternsPlaced isCliPanicSymbolPlaced
      rw [Arm64.Obj.rust_isPanicSymbol_eq_fast, hall]
      rfl
    rw [hnone, ite_self]
  · simp [beq_eq_false_iff_ne.mpr hres]

theorem c2_spqrOnceCall_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {pc : BitVec 64}
    (hk : keepSpqrOnceCall mpl pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  have hExt := c2ExternTableFacts_of_linkedAt hLs
  unfold keepSpqrOnceCall at hk
  simp only [Bool.or_eq_true] at hk
  rcases hk with (((((h1 | h2) | h3) | h4) | h5) | h6) | h7
  · obtain ⟨hrx, hnp⟩ := progKeep_rx_and_noPanic_of_sub
      (of_decide_eq_true (by rfl_kernel)) (of_decide_eq_true (by rfl_kernel)) (by rfl_kernel) h1
    exact f3RxSeg_realProg617_externAt_none hExt W hrx hnp
  · obtain ⟨hrx, hnp⟩ := progKeep_rx_and_noPanic_of_sub
      (of_decide_eq_true (by rfl_kernel)) (of_decide_eq_true (by rfl_kernel)) (by rfl_kernel) h2
    exact f3RxSeg_realProg617_externAt_none hExt W hrx hnp
  · obtain ⟨hrx, hnp⟩ := progKeep_rx_and_noPanic_of_sub
      (of_decide_eq_true (by rfl_kernel)) (of_decide_eq_true (by rfl_kernel)) (by rfl_kernel) h3
    exact f3RxSeg_realProg617_externAt_none hExt W hrx hnp
  · obtain ⟨hrx, hnp⟩ := progKeep_rx_and_noPanic_of_sub
      (of_decide_eq_true (by rfl_kernel)) (of_decide_eq_true (by rfl_kernel)) (by rfl_kernel) h4
    exact f3RxSeg_realProg617_externAt_none hExt W hrx hnp
  · obtain ⟨hrx, hnp⟩ := progKeep_rx_and_noPanic_of_sub
      (of_decide_eq_true (by rfl_kernel)) (of_decide_eq_true (by rfl_kernel)) (by rfl_kernel) h5
    exact f3RxSeg_realProg617_externAt_none hExt W hrx hnp
  · have hlen : c2Blk321SubProg.code.length = 48 := by decide
    have hbase : c2Blk321SubProg.base = cliElfMultiPlacement.base 321 := rfl
    exact externAt_none_of_progKeep_lt_stub hLs
      (by rw [hbase, hlen]; exact Nat.ble_eq.mp blk321_hi_le_stub) W h6
  · have hlen : c2Blk385SubProg.code.length = 68 := by decide
    have hbase : c2Blk385SubProg.base = cliElfMultiPlacement.base 385 := rfl
    exact externAt_none_of_progKeep_lt_stub hLs
      (by rw [hbase, hlen]; exact Nat.ble_eq.mp blk385_hi_le_stub) W h7

theorem c2_spqrOnceCallGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      EG
      lsSpqrOnceCallSym
      (guardOf lsSpqrOnceCallSym)
      spqrOnceCallGhost :=
  spqrOnceCallGhost_rowOk_guardOf mmpl
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
    EG guardOf hLs
    (c2_resolve_spqrOnceCall_eq hLs)
    (fun _ hu => spqrProbeGuard_of_codeLoaded hLs hu.1.lsRo.1 hu.1.rxCode)
    (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
    (c2_spqrOnceCall_hRealHullNoExt hLs)

theorem c2_spqrOnceCallGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      EG
      lsSpqrOnceCallSym
      (spqrOnceCallEntryGuard lsmpl)
      spqrOnceCallGhost :=
  c2_spqrOnceCallGhost_rowOk_guardOf_of_linkedAt mmpl PredFs
    (fun _ => spqrOnceCallEntryGuard lsmpl) EG hLs

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
