/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time

/-!
# `GhostRowOk` Discharge for `sha2::sha256::compress256`

Assembles `c2_compress256Ghost_rowOk` and its `lsmpl` / `guardOf` specializations for
`lsCompress256Sym` (`sha2::sha256::compress256`) over `.text.lib2`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row

open Arm64 Arm64.Obj Arm64.Process ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsCompress256Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code (sha2K32Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl c2Compress256Pl_base c2Compress256Pl_k32 c2_compress256Lib_placeable
   c2_compress256_hKeep keepR_compress256_c2_noPanic keepR_compress256_c2_sub_rxProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2_f3CodeInv_and_fs_hInvKeep c2_f3CodeInv_hInvKeep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256Ghost compress256Ghost_rowOk compress256SubProg keepR_compress256)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3CodeInv_roDataAt_of_checkSegSlice f3RxSeg_realProg617_externAt_none)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Compress256Addr c2Compress256K32Addr)
open LibsignalBinary.Heap.Fine (f3StdLayout)

theorem c2_compress256_hCL
    (hRxComp : checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true)
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → (compress256SubProg c2Compress256Pl).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hRxComp

theorem c2_compress256_hRo
    (hSlice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2Compress256K32Addr sha256KBytes = true)
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → RoDataAt u.mem (c2Compress256Pl.ρ sha2K32Sym) sha256KBytes := by
  intro u hu
  rw [c2Compress256Pl_k32]
  exact f3CodeInv_roDataAt_of_checkSegSlice hLs (hInv u hu) c2Compress256K32Addr sha256KBytes hSlice

theorem c2_compress256_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress256 c2Compress256Pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W _ hkeep =>
    f3RxSeg_realProg617_externAt_none hExt W (keepR_compress256_c2_sub_rxProg hkeep)
      (keepR_compress256_c2_noPanic hkeep)

theorem c2_compress256Ghost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hSlice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2Compress256K32Addr sha256KBytes = true)
    (hExt : C2ExternTableFacts mpl)
    (hRxComp : checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true)
    (hResComp : libsignalSessionLib.resolve mpl lsCompress256Sym = c2Compress256Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowOk mpl mmpl InvS EG lsCompress256Sym (fun _ => True)
      (compress256Ghost c2Compress256Pl) :=
  compress256Ghost_rowOk mpl mmpl c2Compress256Pl InvS EG
    c2_compress256Lib_placeable
    (hResComp.trans c2Compress256Pl_base.symm)
    (c2_compress256_hCL hRxComp hInv)
    (c2_compress256_hRo hSlice hLs hInv)
    hInvKeep
    (fun _ hlr => c2_compress256_hKeep hLsLsmpl hlr)
    (c2_compress256_hRealHullNoExt hExt)

theorem c2_compress256Ghost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hSlice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2Compress256K32Addr sha256KBytes = true)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxComp : checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true)
    (hResComp : libsignalSessionLib.resolve lsmpl lsCompress256Sym = c2Compress256Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsCompress256Sym
      (fun _ => True) (compress256Ghost c2Compress256Pl) :=
  c2_compress256Ghost_rowOk_of_inv lsmpl mmpl
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hSlice hExt hRxComp hResComp hLs hLs
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep lsmpl mmpl PredFs)

theorem c2_compress256Ghost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hSlice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2Compress256K32Addr sha256KBytes = true)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxComp : checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true)
    (hResComp : libsignalSessionLib.resolve lsmpl lsCompress256Sym = c2Compress256Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsCompress256Sym
      (guardOf lsCompress256Sym) (compress256Ghost c2Compress256Pl) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_compress256Ghost_rowOk_lsmpl_and_fs mmpl PredFs EG hSlice hExt hRxComp hResComp hLs
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256Row
