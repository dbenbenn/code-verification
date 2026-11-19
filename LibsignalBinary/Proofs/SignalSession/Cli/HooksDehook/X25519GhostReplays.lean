/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import

/-!
# `GhostRowOk` and `HookNoAllocFailed` Discharges for X25519

Connects `Phase4GhostHooks` (`x25519PubFromSecretGhost`, `x25519DiffieHellmanGhost`) and
`CryptoX25519RowSpecs` (`X25519PubFromSecretRowSpec`, `X25519DiffieHellmanRowSpec`) to the
`cliExtraGhostSyms` infrastructure (`GhostRowSpecOk`, `GhostRowReplayOn`, `GhostRowOk`,
`HookNoAllocFailed`, and `F3CodeInv` → `x25519ActiveInvMem`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsDiffieHellmanSym lsPubFromSecretSym)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
  (X25519CliRoOk x25519MultiKeep)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
  (x25519ActiveInvMem x25519DiffieHellmanGhost x25519DiffieHellmanGhost_fs
   x25519DiffieHellmanGhost_fsT x25519DiffieHellmanGhost_rowReplayOn
   x25519DiffieHellmanGhost_trace x25519PubFromSecretGhost x25519PubFromSecretGhost_fs
   x25519PubFromSecretGhost_fsT x25519PubFromSecretGhost_rowReplayOn
   x25519PubFromSecretGhost_trace)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
  (ed25519BasepointTableBytes ed25519_basepoint_table fe51MontA24Bytes fe51OneBytes fe51_mont_a24
   fe51_one)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed hookNoAllocFailed_of_trace_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecs
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec x25519DiffieHellmanGhost_rowSpec
   x25519PubFromSecretGhost_rowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3CodeInv_roDataAt_of_checkSegSlice
   f3LsRetAddr624_rxRegion_guard isLinkedPanicAddr keepLib2Text keepLib2Text_sub_rxProg keepTextBPre
   keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)

/-! ## 1. Unconditional `HookNoAllocFailed` & `GhostRowSpecOk` -/

theorem x25519PubFromSecretGhost_noAllocFailed [LibsignalPlacement]
    (x25519Mpl : Obj.MultiPlacement) :
    HookNoAllocFailed (x25519PubFromSecretGhost x25519Mpl) :=
  hookNoAllocFailed_of_trace_eq _ (x25519PubFromSecretGhost_trace x25519Mpl)

theorem x25519DiffieHellmanGhost_noAllocFailed [LibsignalPlacement]
    (x25519Mpl : Obj.MultiPlacement) :
    HookNoAllocFailed (x25519DiffieHellmanGhost x25519Mpl) :=
  hookNoAllocFailed_of_trace_eq _ (x25519DiffieHellmanGhost_trace x25519Mpl)

theorem x25519PubFromSecretGhost_rowSpecOk [LibsignalPlacement]
    (x25519Mpl : Obj.MultiPlacement)
    (hArm : X25519PubFromSecretRowSpec (x25519PubFromSecretGhost x25519Mpl) →
      ExtraRowSpec lsPubFromSecretSym (x25519PubFromSecretGhost x25519Mpl)) :
    GhostRowSpecOk lsPubFromSecretSym (x25519PubFromSecretGhost x25519Mpl) where
  fs_eq := x25519PubFromSecretGhost_fs x25519Mpl
  fsT := x25519PubFromSecretGhost_fsT x25519Mpl
  rowSpec := hArm (x25519PubFromSecretGhost_rowSpec x25519Mpl)

theorem x25519DiffieHellmanGhost_rowSpecOk [LibsignalPlacement]
    (x25519Mpl : Obj.MultiPlacement)
    (hArm : X25519DiffieHellmanRowSpec (x25519DiffieHellmanGhost x25519Mpl) →
      ExtraRowSpec lsDiffieHellmanSym (x25519DiffieHellmanGhost x25519Mpl)) :
    GhostRowSpecOk lsDiffieHellmanSym (x25519DiffieHellmanGhost x25519Mpl) where
  fs_eq := x25519DiffieHellmanGhost_fs x25519Mpl
  fsT := x25519DiffieHellmanGhost_fsT x25519Mpl
  rowSpec := hArm (x25519DiffieHellmanGhost_rowSpec x25519Mpl)

/-! ## 2. Stock-ELF Layout Bundle (`C2X25519LayoutFacts`) & `F3CodeInv` Dischargers -/

/-- Stock-ELF layout witness bundle for `x25519CliMultiLib` (19 text blocks and 3 `.rodata`
    tables: `fe51_one`, `fe51_mont_a24`, `ed25519_basepoint_table`), discharged by boolean checks
    against the stock ELF. -/
structure C2X25519LayoutFacts (mpl x25519Mpl : Obj.MultiPlacement) : Prop where
  placeable : x25519CliMultiLib.Placeable x25519Mpl
  resolve_pubFromSecret : libsignalSessionLib.resolve mpl lsPubFromSecretSym = x25519Mpl.base 18
  resolve_diffieHellman : libsignalSessionLib.resolve mpl lsDiffieHellmanSym = x25519Mpl.base 17
  pubFromSecret_rxRegion :
    keepTextBPre (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = true ∨
      keepLib2Text (libsignalSessionLib.resolve mpl lsPubFromSecretSym) = true
  keep_sub_rxRegion : ∀ pc : BitVec 64,
    x25519MultiKeep x25519Mpl pc = true →
      keepTextBPre pc = true ∨ keepLib2Text pc = true
  keep_no_panic : ∀ pc : BitVec 64,
    x25519MultiKeep x25519Mpl pc = true →
      isLinkedPanicAddr pc = false
  rx_blocks : ∀ i : Nat, i < x25519CliMultiLib.blocks.length →
    checkProgCodeSubslice f3TrialRxProg (x25519CliMultiLib.blockProgram x25519Mpl i) = true
  ro_fe51_one : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
    seg.perm.rwx = Perm.ro ∧
    checkSegSlice seg seg.bytes.length (fe51_one x25519Mpl) fe51OneBytes = true
  ro_fe51_mont_a24 : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
    seg.perm.rwx = Perm.ro ∧
    checkSegSlice seg seg.bytes.length (fe51_mont_a24 x25519Mpl) fe51MontA24Bytes = true
  ro_ed25519_basepoint_table : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
    seg.perm.rwx = Perm.ro ∧
    checkSegSlice seg seg.bytes.length
      (ed25519_basepoint_table x25519Mpl) ed25519BasepointTableBytes = true

theorem c2_x25519_roOk_of_f3CodeInv {mpl mmpl x25519Mpl : Obj.MultiPlacement} {m : Memory}
    (hLay : C2X25519LayoutFacts mpl x25519Mpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    X25519CliRoOk x25519Mpl m where
  ro_fe51_one :=
    f3CodeInv_roDataAt_of_checkSegSlice hLs hInv (fe51_one x25519Mpl) fe51OneBytes hLay.ro_fe51_one
  ro_fe51_mont_a24 :=
    f3CodeInv_roDataAt_of_checkSegSlice hLs hInv
      (fe51_mont_a24 x25519Mpl) fe51MontA24Bytes hLay.ro_fe51_mont_a24
  ro_ed25519_basepoint_table :=
    f3CodeInv_roDataAt_of_checkSegSlice hLs hInv
      (ed25519_basepoint_table x25519Mpl) ed25519BasepointTableBytes
      hLay.ro_ed25519_basepoint_table

theorem c2_x25519_codeLoaded_of_f3CodeInv {mpl mmpl x25519Mpl : Obj.MultiPlacement} {m : Memory}
    (hLay : C2X25519LayoutFacts mpl x25519Mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    x25519CliMultiLib.CodeLoaded x25519Mpl m :=
  fun i hi => codeLoaded_of_checkProgCodeSubslice hInv.rxCode (hLay.rx_blocks i hi)

theorem c2_x25519_activeInvMem_of_f3CodeInv {mpl mmpl x25519Mpl : Obj.MultiPlacement} {m : Memory}
    (hLay : C2X25519LayoutFacts mpl x25519Mpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    x25519ActiveInvMem x25519Mpl m :=
  ⟨hLay.placeable,
   c2_x25519_codeLoaded_of_f3CodeInv hLay hInv,
   c2_x25519_roOk_of_f3CodeInv hLay hLs hInv⟩

theorem c2_x25519_keep_sub_rxProg {mpl x25519Mpl : Obj.MultiPlacement}
    (hLay : C2X25519LayoutFacts mpl x25519Mpl) {pc : BitVec 64}
    (hk : x25519MultiKeep x25519Mpl pc = true) :
    progKeep f3TrialRxProg pc = true := by
  rcases hLay.keep_sub_rxRegion pc hk with hb | hl
  · exact keepTextBPre_sub_rxProg hb
  · exact keepLib2Text_sub_rxProg hl

theorem c2_x25519_keep_lr_false [LibsignalPlacement] {x25519Mpl : Obj.MultiPlacement}
    (hLay : C2X25519LayoutFacts lsmpl x25519Mpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hRet : LsRetAddr624 lr) :
    x25519MultiKeep x25519Mpl lr = false :=
  (f3LsRetAddr624_rxRegion_guard hLs hRet hLay.pubFromSecret_rxRegion hLay.keep_sub_rxRegion).1

theorem c2_x25519_realNoExt {mpl mmpl x25519Mpl : Obj.MultiPlacement}
    (hLay : C2X25519LayoutFacts mpl x25519Mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) {pc : BitVec 64}
    (hk : x25519MultiKeep x25519Mpl pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  hExt.realRxNoExtern mmpl W (c2_x25519_keep_sub_rxProg hLay hk) (hLay.keep_no_panic pc hk)

/-! ## 3. Full `GhostRowOk` Discharges (`lsPubFromSecretSym`, `lsDiffieHellmanSym`) -/

private theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {g1 g2 : State → Prop} {f : State → State}
    (h : GhostRowReplayOn mpl mmpl InvS EG sym g1 f)
    (himp : ∀ s0, g2 s0 → g1 s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym g2 f :=
  ⟨h.preserves_execFrozen, fun W s0 sf hg2 => h.replay_at_stub W s0 sf (himp s0 hg2)⟩

theorem c2_x25519PubFromSecretGhost_rowOk [LibsignalPlacement]
    (mmpl x25519Mpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLay : C2X25519LayoutFacts lsmpl x25519Mpl)
    (hArm : X25519PubFromSecretRowSpec (x25519PubFromSecretGhost x25519Mpl) →
      ExtraRowSpec lsPubFromSecretSym (x25519PubFromSecretGhost x25519Mpl))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsPubFromSecretSym (guardOf lsPubFromSecretSym)
      (x25519PubFromSecretGhost x25519Mpl) :=
  ⟨x25519PubFromSecretGhost_rowSpecOk x25519Mpl hArm,
   ghostRowReplayOn_of_guard_imp
     (x25519PubFromSecretGhost_rowReplayOn lsmpl mmpl x25519Mpl
       (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
       hLay.placeable hLay.resolve_pubFromSecret
       (fun _ hu => c2_x25519_activeInvMem_of_f3CodeInv hLay hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2_x25519_keep_lr_false hLay hLs)
       (c2_x25519_realNoExt hLay hExt))
     (fun _ _ => trivial)⟩

theorem c2_x25519DiffieHellmanGhost_rowOk [LibsignalPlacement]
    (mmpl x25519Mpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLay : C2X25519LayoutFacts lsmpl x25519Mpl)
    (hArm : X25519DiffieHellmanRowSpec (x25519DiffieHellmanGhost x25519Mpl) →
      ExtraRowSpec lsDiffieHellmanSym (x25519DiffieHellmanGhost x25519Mpl))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsDiffieHellmanSym (guardOf lsDiffieHellmanSym)
      (x25519DiffieHellmanGhost x25519Mpl) :=
  ⟨x25519DiffieHellmanGhost_rowSpecOk x25519Mpl hArm,
   ghostRowReplayOn_of_guard_imp
     (x25519DiffieHellmanGhost_rowReplayOn lsmpl mmpl x25519Mpl
       (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
       hLay.placeable hLay.resolve_diffieHellman
       (fun _ hu => c2_x25519_activeInvMem_of_f3CodeInv hLay hLs hu.1)
       (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
       (c2_x25519_keep_lr_false hLay hLs)
       (c2_x25519_realNoExt hLay hExt))
     (fun _ _ => trivial)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays
