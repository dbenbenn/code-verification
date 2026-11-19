/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays -- proof-setup: allow-public-import

/-!
# Concrete `C2X25519LayoutFacts` and `GhostRowOk` Glue for X25519

Instantiates `X25519GhostReplays.C2X25519LayoutFacts mpl c2X25519Mpl` from
`C2RowLayoutFacts.X25519` so `T4Witness` discharges both X25519 rows (`lsPubFromSecretSym`,
`lsDiffieHellmanSym`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row

open Arm64 Arm64.Obj
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes libsignalSessionLib lsDiffieHellmanSym lsPubFromSecretSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
  (x25519DiffieHellmanGhost x25519PubFromSecretGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (HookNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519
  (c2X25519Mpl c2_x25519_keep_noPanic c2_x25519_keep_sub_rxRegion c2_x25519_placeable
   c2_x25519_pubFromSecret_rxRegion c2_x25519_resolve_diffieHellman c2_x25519_resolve_pubFromSecret
   c2_x25519_ro_ed25519_basepoint_table c2_x25519_ro_fe51_mont_a24 c2_x25519_ro_fe51_one
   c2_x25519_rx_blocks)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519GhostReplays
  (C2X25519LayoutFacts c2_x25519DiffieHellmanGhost_rowOk c2_x25519PubFromSecretGhost_rowOk
   x25519DiffieHellmanGhost_noAllocFailed x25519PubFromSecretGhost_noAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (ExtraRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)

theorem pubFromSecret_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : X25519PubFromSecretRowSpec f) : ExtraRowSpec lsPubFromSecretSym f := by
  unfold ExtraRowSpec
  iterate 35 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem diffieHellman_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : X25519DiffieHellmanRowSpec f) : ExtraRowSpec lsDiffieHellmanSym f := by
  unfold ExtraRowSpec
  iterate 36 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

/-- Concrete stock-ELF witness for `C2X25519LayoutFacts mpl c2X25519Mpl`. -/
theorem c2X25519LayoutFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2X25519LayoutFacts mpl c2X25519Mpl where
  placeable := c2_x25519_placeable
  resolve_pubFromSecret := c2_x25519_resolve_pubFromSecret hLs
  resolve_diffieHellman := c2_x25519_resolve_diffieHellman hLs
  pubFromSecret_rxRegion := c2_x25519_pubFromSecret_rxRegion hLs
  keep_sub_rxRegion := fun _ hk => c2_x25519_keep_sub_rxRegion hk
  keep_no_panic := fun _ hk => c2_x25519_keep_noPanic hk
  rx_blocks := c2_x25519_rx_blocks
  ro_fe51_one := c2_x25519_ro_fe51_one
  ro_fe51_mont_a24 := c2_x25519_ro_fe51_mont_a24
  ro_ed25519_basepoint_table := c2_x25519_ro_ed25519_basepoint_table

/-- Concrete `GhostRowOk` for `lsPubFromSecretSym` at `c2X25519Mpl` (`guardOf` form). -/
theorem c2_x25519PubFromSecretGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsPubFromSecretSym (guardOf lsPubFromSecretSym)
      (x25519PubFromSecretGhost c2X25519Mpl) :=
  c2_x25519PubFromSecretGhost_rowOk mmpl c2X25519Mpl PredFs EG guardOf
    (c2X25519LayoutFacts_of_linkedAt hLs) pubFromSecret_extraRowSpec hExt hLs

/-- Concrete `GhostRowOk` for `lsPubFromSecretSym` at `c2X25519Mpl` (`fun _ => True` form). -/
theorem c2_x25519PubFromSecretGhost_rowOk_true_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsPubFromSecretSym (fun _ => True)
      (x25519PubFromSecretGhost c2X25519Mpl) :=
  c2_x25519PubFromSecretGhost_rowOk_c2 mmpl PredFs EG (fun _ _ => True) hExt hLs

/-- Concrete `GhostRowOk` for `lsDiffieHellmanSym` at `c2X25519Mpl` (`guardOf` form). -/
theorem c2_x25519DiffieHellmanGhost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsDiffieHellmanSym (guardOf lsDiffieHellmanSym)
      (x25519DiffieHellmanGhost c2X25519Mpl) :=
  c2_x25519DiffieHellmanGhost_rowOk mmpl c2X25519Mpl PredFs EG guardOf
    (c2X25519LayoutFacts_of_linkedAt hLs) diffieHellman_extraRowSpec hExt hLs

/-- Concrete `GhostRowOk` for `lsDiffieHellmanSym` at `c2X25519Mpl` (`fun _ => True` form). -/
theorem c2_x25519DiffieHellmanGhost_rowOk_true_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsDiffieHellmanSym (fun _ => True)
      (x25519DiffieHellmanGhost c2X25519Mpl) :=
  c2_x25519DiffieHellmanGhost_rowOk_c2 mmpl PredFs EG (fun _ _ => True) hExt hLs

theorem c2_x25519PubFromSecretGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (x25519PubFromSecretGhost c2X25519Mpl) :=
  x25519PubFromSecretGhost_noAllocFailed c2X25519Mpl

theorem c2_x25519DiffieHellmanGhost_noAllocFailed [LibsignalPlacement] :
    HookNoAllocFailed (x25519DiffieHellmanGhost c2X25519Mpl) :=
  x25519DiffieHellmanGhost_noAllocFailed c2X25519Mpl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row
