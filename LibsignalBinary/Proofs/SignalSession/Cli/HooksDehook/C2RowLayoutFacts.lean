/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512Row -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DalekRows
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcRows
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemmoveRow
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemrchrRow
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon

/-!
# Aggregate Layout-Fact Bundles and Per-Row `GhostRowOk` Re-Exports

**Checked by Lean.**

Defines the two aggregate layout-fact bundles and re-exports per-row `GhostRowOk` theorems at
`mpl := lsmpl`:
1. `C2ResolveFacts (mpl : Obj.MultiPlacement) : Prop`: symbol-resolved entry equalities
   `libsignalSessionLib.resolve mpl <sym> = c2<Row>Addr` across `from_utf8`, `duration_since`,
   `SystemTime::add`, `memrchr`, `"strlen"`, `"bcmp"`, `"memmove"`, `compress256`, `libcrux_hmac`,
   `aes_256_cbc_encrypt`, `aes_256_cbc_decrypt`, and the 3 Dalek `.text.lib2` rows
   (`Dalek.C2DalekResolveFacts mpl`).
2. `C2Lib2RxSliceFacts (mpl : Obj.MultiPlacement) : Prop`: linear byte-subslice checks
   `CodeSubslice.checkProgCodeSubslice Tie.f3TrialRxProg <rowSubProg> = true` against the
   `subProg` definition each row's replay and `GhostRowSpecOk` are proved over.
3. Per-row `GhostRowOk` re-exports at `mpl := lsmpl` (`[LibsignalPlacement]`): instantiates
   `mpl := lsmpl` directly (without a second `LinkedAt` witness or `mpl = lsmpl` equality) on
   `InvS := fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs` and
   `EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')`, matching
   `ExtraGhostReplay.ExtraListReplaysOn` / `ExtraOk`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsAesDecSym lsAesEncSym lsBlackBoxSym
   lsCompress256Sym lsDurationSinceSym lsFromUtf8Sym lsLibcruxHmacSym lsMemrchrSym
   lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
  (aesDecEntryGuard aesDecGhost aesDecSpecOf aesDecWeakSpecOf aesEncEntryGuard aesEncGhost
   aesEncSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost bcmpSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost blackBoxSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (aesCbcSubProg c2AesDecAddr c2AesEncAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow
  (c2_aesDecGhost_hookOk c2_aesDecGhost_rowOk_lsmpl_and_fs c2_aesDecGhost_weakHookOk
   c2_aesEncGhost_hookOk c2_aesEncGhost_rowOk_lsmpl_and_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row
  (c2_compress256Ghost_rowOk_lsmpl_and_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
  (C2DalekResolveFacts)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row
  (c2_fromUtf8MplGhost_rowOk c2_fromUtf8MplGhost_rowOk_guardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmac
  (libcruxHmacSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcruxHmacRow
  (c2_libcruxHmacGhost_hookOk c2_libcruxHmacGhost_rowOk_lsmpl_and_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2TimeMpl c2_durationSinceGhost_rowOk_lsmpl_and_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (c2_timeAddGhost_rowOk_lsmpl_extra c2_timeAddGhost_rowOk_lsmpl_guardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256EntryGuard compress256Ghost compress256SubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceEntryGuard durationSinceGhost durationSinceSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost fromUtf8SubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (fromUtf8Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LibcruxHmacGhostReplays
  (libcruxHmacEntryGuard libcruxHmacGhost libcruxHmacSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (memmoveEntryGuard memmoveGhost memmoveSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
  (memrchrEntryGuard memrchrGhost memrchrSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (staticSecretDropEntryGuard staticSecretDropGhost staticSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (strlenEntryGuard strlenGhost strlenSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (timeAddEntryGuard timeAddGhost timeAddSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BcmpAddr c2BlackBoxAddr c2Compress256Addr c2DurationSinceAddr c2FromUtf8Addr
   c2FromUtf8TableAddr c2LibcruxHmacAddr c2MemmoveAddr c2MemrchrAddr c2SharedSecretDropAddr
   c2StaticSecretDropAddr c2StrlenAddr c2TimeAddAddr)

/-! ## 1. Aggregate Pending-Witness Bundles (`C2ResolveFacts`, `C2Lib2RxSliceFacts`) -/

/-- Aggregate symbol-resolution witness across the linked `.text.lib2` rows (11 direct fields plus
    the 3 Dalek equalities embedded via `Dalek.C2DalekResolveFacts mpl`), tied to `mpl` and
    instantiated at `lsmpl` under `libsignalSessionLib.LinkedAt cliElfBytes lsmpl`. -/
structure C2ResolveFacts (mpl : Obj.MultiPlacement) : Prop where
  fromUtf8_eq : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr
  durationSince_eq : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr
  timeAdd_eq : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr
  memrchr_eq : libsignalSessionLib.resolve mpl lsMemrchrSym = c2MemrchrAddr
  strlen_eq : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr
  bcmp_eq : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr
  memmove_eq : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr
  dalek : C2DalekResolveFacts mpl
  compress256_eq : libsignalSessionLib.resolve mpl lsCompress256Sym = c2Compress256Addr
  libcruxHmac_eq : libsignalSessionLib.resolve mpl lsLibcruxHmacSym = c2LibcruxHmacAddr
  aesEnc_eq : libsignalSessionLib.resolve mpl lsAesEncSym = c2AesEncAddr
  aesDec_eq : libsignalSessionLib.resolve mpl lsAesDecSym = c2AesDecAddr

theorem C2ResolveFacts.blackBox_eq {mpl : Obj.MultiPlacement} (h : C2ResolveFacts mpl) :
    libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr :=
  h.dalek.blackBox_eq

theorem C2ResolveFacts.sharedSecretDrop_eq {mpl : Obj.MultiPlacement} (h : C2ResolveFacts mpl) :
    libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr :=
  h.dalek.sharedSecretDrop_eq

theorem C2ResolveFacts.staticSecretDrop_eq {mpl : Obj.MultiPlacement} (h : C2ResolveFacts mpl) :
    libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr :=
  h.dalek.staticSecretDrop_eq

/-- Aggregate RX byte-subslice witness across the linked `.text.lib2` rows (12 sub-program checks),
    checked against `Tie.f3TrialRxProg` using the `subProg` definition each row's replay and
    `GhostRowSpecOk` are proved over. -/
structure C2Lib2RxSliceFacts (mpl : Obj.MultiPlacement) : Prop where
  fromUtf8 :
    checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true
  durationSince :
    checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true
  timeAdd :
    checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true
  blackBox :
    checkProgCodeSubslice f3TrialRxProg (blackBoxSubProg mpl) = true
  staticSecretDrop :
    checkProgCodeSubslice f3TrialRxProg (staticSecretDropSubProg mpl) = true
  memrchr :
    checkProgCodeSubslice f3TrialRxProg (memrchrSubProg mpl) = true
  strlen :
    checkProgCodeSubslice f3TrialRxProg (strlenSubProg mpl) = true
  bcmp :
    checkProgCodeSubslice f3TrialRxProg (bcmpSubProg mpl) = true
  memmove :
    checkProgCodeSubslice f3TrialRxProg (memmoveSubProg mpl) = true
  compress256 :
    checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true
  libcruxHmac :
    checkProgCodeSubslice f3TrialRxProg libcruxHmacSubProg = true
  aesCbc :
    checkProgCodeSubslice f3TrialRxProg aesCbcSubProg = true

/-! ## 2. Per-Row `GhostRowOk` Re-Exports at `mpl := lsmpl` -/

private theorem ghostRowReplayOn_of_true_guard
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {f : State → State}
    (entryGuard : State → Prop)
    (h : GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True) f) :
    GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f :=
  ⟨h.preserves_execFrozen, fun W s0 sf _ => h.replay_at_stub W s0 sf trivial⟩

/-- `GhostRowOk` re-export for `lsFromUtf8Sym` (`core::str::converts::from_utf8`) at
    `mpl := lsmpl`. -/
theorem c2_fromUtf8Ghost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (fromUtf8EntryGuard lsmpl)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8MplGhost_rowOk lsmpl mmpl PredFs g extra hLook
    hRo hExt hRx.fromUtf8 hRes.fromUtf8_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsFromUtf8Sym` at `mpl := lsmpl`. -/
theorem c2_fromUtf8Ghost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hGuard : ∀ s0 : State, guardOf lsFromUtf8Sym s0 → fromUtf8EntryGuard lsmpl s0)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (guardOf lsFromUtf8Sym)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8MplGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hRo hExt hRx.fromUtf8 hRes.fromUtf8_eq hLs

/-- `GhostRowOk` re-export for `lsDurationSinceSym` (`SystemTime::duration_since`) at
    `mpl := lsmpl`. -/
theorem c2_durationSinceGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (durationSinceEntryGuard lsmpl)
      (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_lsmpl_and_fs mmpl PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hRo hExt hRx.durationSince hRes.durationSince_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsDurationSinceSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `durationSinceEntryGuard lsmpl` is `True`). -/
theorem c2_durationSinceGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (guardOf lsDurationSinceSym)
      (durationSinceGhost c2TimeMpl) := by
  have hRow := c2_durationSinceGhost_rowOk mmpl PredFs g extra hRes hRx hRo hExt hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsDurationSinceSym) hRow.2⟩

/-- `GhostRowOk` re-export for `lsTimeAddSym` (`<SystemTime as Add<Duration>>::add`) at
    `mpl := lsmpl`. -/
theorem c2_timeAddGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (timeAddEntryGuard lsmpl)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_lsmpl_extra mmpl PredFs g extra
    hExt hRx.timeAdd hRes.timeAdd_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsTimeAddSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `timeAddEntryGuard lsmpl` is `True`). -/
theorem c2_timeAddGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (guardOf lsTimeAddSym)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_lsmpl_guardOf mmpl PredFs guardOf g extra
    hExt hRx.timeAdd hRes.timeAdd_eq hLs

/-- `GhostRowOk` re-export for `lsBlackBoxSym` (`core::hint::black_box::<&[u8]>`) at
    `mpl := lsmpl`. -/
theorem c2_blackBoxGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (blackBoxEntryGuard lsmpl)
      (blackBoxGhost lsmpl mmpl) :=
  DalekRows.c2_blackBoxGhost_rowOk lsmpl mmpl PredFs g extra hLook
    hExt hRx.blackBox hRes.blackBox_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsBlackBoxSym` at `mpl := lsmpl`. -/
theorem c2_blackBoxGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsBlackBoxSym s0 → blackBoxEntryGuard lsmpl s0)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (guardOf lsBlackBoxSym)
      (blackBoxGhost lsmpl mmpl) :=
  DalekRows.c2_blackBoxGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hExt hRx.blackBox hRes.blackBox_eq hLs

/-- `GhostRowOk` re-export for `lsStaticSecretDropSym` (`StaticSecret::drop`) at
    `mpl := lsmpl`. -/
theorem c2_staticSecretDropGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (staticSecretDropEntryGuard lsmpl)
      (staticSecretDropGhost lsmpl mmpl) :=
  DalekRows.c2_staticSecretDropGhost_rowOk lsmpl mmpl PredFs g extra hLook
    hExt hRx.staticSecretDrop hRes.staticSecretDrop_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsStaticSecretDropSym` at
    `mpl := lsmpl`. -/
theorem c2_staticSecretDropGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsStaticSecretDropSym s0 → staticSecretDropEntryGuard lsmpl s0)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (guardOf lsStaticSecretDropSym)
      (staticSecretDropGhost lsmpl mmpl) :=
  DalekRows.c2_staticSecretDropGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hExt hRx.staticSecretDrop hRes.staticSecretDrop_eq hLs

/-- `GhostRowOk` re-export for `lsMemrchrSym` (`slice::memchr::memrchr`) at
    `mpl := lsmpl`. -/
theorem c2_memrchrGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (memrchrEntryGuard lsmpl)
      (memrchrGhost lsmpl mmpl) :=
  MemrchrRow.c2_memrchrGhost_rowOk mmpl PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hRx.memrchr hRes.memrchr_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsMemrchrSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `memrchrEntryGuard lsmpl` is `True`). -/
theorem c2_memrchrGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (guardOf lsMemrchrSym)
      (memrchrGhost lsmpl mmpl) := by
  have hRow := c2_memrchrGhost_rowOk mmpl PredFs g extra hRes hRx hExt hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsMemrchrSym) hRow.2⟩

/-- `GhostRowOk` re-export for `"strlen"` at `mpl := lsmpl`. -/
theorem c2_strlenGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (strlenEntryGuard lsmpl)
      (strlenGhost lsmpl mmpl) :=
  LibcRows.c2_strlenGhost_rowOk lsmpl mmpl PredFs g extra hLook
    hExt hRx.strlen hRes.strlen_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `"strlen"` at `mpl := lsmpl`. -/
theorem c2_strlenGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "strlen" s0 → strlenEntryGuard lsmpl s0)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (guardOf "strlen")
      (strlenGhost lsmpl mmpl) :=
  LibcRows.c2_strlenGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hExt hRx.strlen hRes.strlen_eq hLs

/-- `GhostRowOk` re-export for `"bcmp"` at `mpl := lsmpl`. -/
theorem c2_bcmpGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (bcmpEntryGuard lsmpl)
      (bcmpGhost lsmpl mmpl) :=
  LibcRows.c2_bcmpGhost_rowOk lsmpl mmpl PredFs g extra hLook
    hExt hRx.bcmp hRes.bcmp_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `"bcmp"` at `mpl := lsmpl`. -/
theorem c2_bcmpGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "bcmp" s0 → bcmpEntryGuard lsmpl s0)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (guardOf "bcmp")
      (bcmpGhost lsmpl mmpl) :=
  LibcRows.c2_bcmpGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hExt hRx.bcmp hRes.bcmp_eq hLs

/-- `GhostRowOk` re-export for `"memmove"` at `mpl := lsmpl` (`hGMemcpy` and `hGMemset`
    discharged by the caller). -/
theorem c2_memmoveGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (memmoveEntryGuard lsmpl)
      (memmoveGhost lsmpl mmpl) :=
  MemmoveRow.c2_memmoveGhost_rowOk lsmpl mmpl PredFs g extra hLook hGMemcpy hGMemset
    hExt hRx.memmove hRes.memmove_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `"memmove"` at `mpl := lsmpl`. -/
theorem c2_memmoveGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "memmove" s0 → memmoveEntryGuard lsmpl s0)
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (guardOf "memmove")
      (memmoveGhost lsmpl mmpl) :=
  MemmoveRow.c2_memmoveGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hLook hGuard
    hGMemcpy hGMemset hExt hRx.memmove hRes.memmove_eq hLs

/-- `GhostRowOk` re-export for `lsCompress256Sym` (`sha2::sha256::compress256`) at
    `mpl := lsmpl`. -/
theorem c2_compress256Ghost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsCompress256Sym
      (compress256EntryGuard lsmpl)
      (compress256Ghost c2Compress256Pl) :=
  c2_compress256Ghost_rowOk_lsmpl_and_fs mmpl PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hRo.compress256K32Slice hExt hRx.compress256 hRes.compress256_eq hLs

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsCompress256Sym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `compress256EntryGuard lsmpl` is `True`). -/
theorem c2_compress256Ghost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hRx : C2Lib2RxSliceFacts lsmpl)
    (hRo : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsCompress256Sym
      (guardOf lsCompress256Sym)
      (compress256Ghost c2Compress256Pl) := by
  have hRow := c2_compress256Ghost_rowOk mmpl PredFs g extra hRes hRx hRo hExt hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsCompress256Sym) hRow.2⟩

/-- `GhostRowOk` re-export for `lsLibcruxHmacSym` (`libcrux_hmac::hmac`) at
    `mpl := lsmpl`. -/
theorem c2_libcruxHmacGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsLibcruxHmacSym
      (libcruxHmacEntryGuard lsmpl)
      (libcruxHmacGhost LibcruxHmac.keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) :=
  c2_libcruxHmacGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hRes.libcruxHmac_eq hLs hMm

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsLibcruxHmacSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `libcruxHmacEntryGuard lsmpl` is `True`). -/
theorem c2_libcruxHmacGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsLibcruxHmacSym
      (guardOf lsLibcruxHmacSym)
      (libcruxHmacGhost LibcruxHmac.keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim) := by
  have hRow := c2_libcruxHmacGhost_rowOk mmpl brkStart lim PredFs g extra hRes hExt hLs hMm
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsLibcruxHmacSym) hRow.2⟩

/-- Pointwise `HookOk` re-export for `libcruxHmacGhost` at `(γ, tp)`. -/
theorem c2_libcruxHmacGhost_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (libcruxHmacGhost LibcruxHmac.keepRxSeg libcruxHmacSubProg c2LibcruxHmacAddr mmpl brkStart lim)
      (libcruxHmacSpecOf mmpl brkStart lim γ tp) :=
  c2_libcruxHmacGhost_hookOk mmpl hMm hLsLsmpl brkStart lim γ tp

/-- `GhostRowOk` re-export for `lsAesEncSym` (`aes_256_cbc_encrypt`) at `mpl := lsmpl`. -/
theorem c2_aesEncGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesEncSym
      (aesEncEntryGuard lsmpl)
      (aesEncGhost AesCbc.keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) :=
  c2_aesEncGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hRes.aesEnc_eq hLs hMm hbrk

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsAesEncSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `aesEncEntryGuard lsmpl` is `True`). -/
theorem c2_aesEncGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesEncSym
      (guardOf lsAesEncSym)
      (aesEncGhost AesCbc.keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim) := by
  have hRow := c2_aesEncGhost_rowOk mmpl brkStart lim PredFs g extra hRes hExt hLs hMm hbrk
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsAesEncSym) hRow.2⟩

/-- `GhostRowOk` re-export for `lsAesDecSym` (`aes_256_cbc_decrypt`) at `mpl := lsmpl`. -/
theorem c2_aesDecGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (aesDecEntryGuard lsmpl)
      (aesDecGhost AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) :=
  c2_aesDecGhost_rowOk_lsmpl_and_fs mmpl brkStart lim PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hRes.aesDec_eq hLs hMm hbrk

/-- `guardOf`-adapted `GhostRowOk` re-export for `lsAesDecSym` at `mpl := lsmpl`
    (no `hGuard` premise needed because `aesDecEntryGuard lsmpl` is `True`). -/
theorem c2_aesDecGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hRes : C2ResolveFacts lsmpl)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hbrk : brkStart = f3StdLayout.brkStart := by decide) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsAesDecSym
      (guardOf lsAesDecSym)
      (aesDecGhost AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim) := by
  have hRow := c2_aesDecGhost_rowOk mmpl brkStart lim PredFs g extra hRes hExt hLs hMm hbrk
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsAesDecSym) hRow.2⟩

/-- Pointwise `HookOk` re-export for `aesEncGhost` at `(γ, tp)`. -/
theorem c2_aesEncGhost_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesEncGhost AesCbc.keepRxSeg aesCbcSubProg c2AesEncAddr mmpl brkStart lim)
      (aesEncSpecOf mmpl brkStart lim γ tp) :=
  c2_aesEncGhost_hookOk mmpl hMm hLsLsmpl brkStart lim γ tp

/-- Pointwise `HookOk` re-export for `aesDecGhost` at `(γ, tp)`. -/
theorem c2_aesDecGhost_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecGhost AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecSpecOf mmpl brkStart lim γ tp) :=
  c2_aesDecGhost_hookOk mmpl hMm hLsLsmpl brkStart lim γ tp

/-- Pointwise `HookOk` companion re-export for `aesDecGhost` at `aesDecWeakSpecOf`. -/
theorem c2_aesDecGhost_weak_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (aesDecGhost AesCbc.keepRxSeg aesCbcSubProg c2AesDecAddr mmpl brkStart lim)
      (aesDecWeakSpecOf mmpl brkStart lim γ tp) :=
  c2_aesDecGhost_weakHookOk mmpl hMm hLsLsmpl brkStart lim γ tp

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts
