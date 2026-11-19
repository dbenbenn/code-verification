/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Cutover-2 (`C2`) `.text.lib2` Dalek Entry-Guard Discharges (`C2RowLayoutFacts.Dalek`)

Discharges GK6c §19(d) for the three `.text.lib2` Dalek/generics rows (`lsBlackBoxSym`,
`lsSharedSecretDropSym`, `lsStaticSecretDropSym`):
1. Keyed strictly by symbol name (`libsignalSessionLib.resolve mpl <sym>`) and generator-emitted
   `Wp4LayoutGen` / `Lib2LayoutFacts` constants (`c2BlackBoxAddr`, `c2SharedSecretDropAddr`,
   `c2StaticSecretDropAddr`, `c2Lib2TextLo`, `c2Lib2TextHi`, `f3StartupLrVal`), with zero hex
   address literals.
2. Proves per-row hull inclusion `keepR_<row> mpl pc = true → keepLib2Text pc = true` on the C2
   placement (`C2DalekResolveFacts mpl`), then routes through unconditional
   `Lib2LayoutFacts.f3Lib2EntryGuard_of_startupLr` + `C2ExternTableFacts.lib2InKeep` (and direct
   `C2DalekResolveFacts`-only corollaries) to yield `blackBoxEntryGuard mpl s0`,
   `sharedSecretDropEntryGuard mpl s0`, and `staticSecretDropEntryGuard mpl s0` in the exact shapes
   consumed by `extraEntryGuard_{blackBox,sharedSecretDrop,staticSecretDrop}_arm` and
   `extraEntryGuard_singleton_{blackBox,sharedSecretDrop,staticSecretDrop}`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open CryptoVerification.SignalSession
  (libsignalSessionLib lsBlackBoxSym lsSharedSecretDropSym lsStaticSecretDropSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (ExtraEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap
  (blackBoxByteLen keepBlackBox keepBlackBox_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxEntryGuard_iff blackBoxGhost extraEntryGuard_blackBox_arm
   extraEntryGuard_singleton_blackBox keepR_blackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (keepSharedSecretDropHull keepSharedSecretDropHull_iff keepStaticSecretDrop
   keepStaticSecretDrop_iff sharedSecretDropHullByteLen staticSecretDropByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays
  (extraEntryGuard_sharedSecretDrop_arm extraEntryGuard_singleton_sharedSecretDrop
   keepR_sharedSecretDrop sharedSecretDropEntryGuard sharedSecretDropEntryGuard_iff
   sharedSecretDropGhost sharedSecretDropHullBase)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (extraEntryGuard_singleton_staticSecretDrop extraEntryGuard_staticSecretDrop_arm
   keepR_staticSecretDrop staticSecretDropEntryGuard staticSecretDropEntryGuard_iff
   staticSecretDropGhost)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3Lib2EntryGuard_of_startupLr f3Lib2_dehookedSym_in_keepLib2Text
   f3StartupLrVal isLinkedPanicAddr isLinkedPanicAddr_false_of_mid keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BlackBoxAddr c2Lib2DehookedSyms c2Lib2TextHi c2Lib2TextLo c2SharedSecretDropAddr
   c2StaticSecretDropAddr)

/-! ## 1. C2 Resolved-Address Witness & Symbol Membership in `c2Lib2DehookedSyms` -/

/-- C2 resolved-address witness for the 3 `.text.lib2` Dalek rows; closed at T4 on the C2-pinned
    `cliElfBytes` from `cliElf_linkedAt_unique` + `rfl`. -/
structure C2DalekResolveFacts (mpl : Obj.MultiPlacement) : Prop where
  blackBox_eq : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr
  sharedSecretDrop_eq :
    libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr
  staticSecretDrop_eq :
    libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr

/-! ## 2. Per-Row Hull Inclusion `keepR_<row> mpl pc = true → keepLib2Text pc = true` -/

private theorem keepLib2Text_of_sub_lt {base pc : BitVec 64} {len : Nat}
    (hsub : (pc - base).toNat < len)
    (hlo : c2Lib2TextLo.toNat ≤ base.toNat)
    (hhi : base.toNat + len ≤ c2Lib2TextHi.toNat) :
    keepLib2Text pc = true := by
  unfold keepLib2Text
  rw [decide_eq_true_eq]
  have htop : c2Lib2TextHi.toNat < 2 ^ 64 := BitVec.isLt c2Lib2TextHi
  generalize hd : pc - base = d at hsub
  have hpc_eq : pc = base + d := by subst hd; bv_omega
  have htoNat : pc.toNat = base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Unconditional C2 hull inclusion for `keepBlackBox c2BlackBoxAddr`. -/
theorem keepBlackBox_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepBlackBox c2BlackBoxAddr pc = true) :
    keepLib2Text pc = true := by
  rw [keepBlackBox_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- Unconditional C2 hull inclusion for `keepSharedSecretDropHull (c2SharedSecretDropAddr - sharedSecretDropEntryOff)`. -/
theorem keepSharedSecretDrop_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepSharedSecretDropHull (c2SharedSecretDropAddr - sharedSecretDropEntryOff) pc = true) :
    keepLib2Text pc = true := by
  rw [keepSharedSecretDropHull_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- Unconditional C2 hull inclusion for `keepStaticSecretDrop c2StaticSecretDropAddr`. -/
theorem keepStaticSecretDrop_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepStaticSecretDrop c2StaticSecretDropAddr pc = true) :
    keepLib2Text pc = true := by
  rw [keepStaticSecretDrop_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

theorem keepR_blackBox_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (pc : BitVec 64) (h : keepR_blackBox mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_blackBox] at h
  rw [hRes] at h
  exact keepBlackBox_c2_sub_keepLib2Text h

theorem keepR_sharedSecretDrop_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (pc : BitVec 64) (h : keepR_sharedSecretDrop mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_sharedSecretDrop, sharedSecretDropHullBase] at h
  rw [hRes] at h
  exact keepSharedSecretDrop_c2_sub_keepLib2Text h

theorem keepR_staticSecretDrop_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (pc : BitVec 64) (h : keepR_staticSecretDrop mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_staticSecretDrop] at h
  rw [hRes] at h
  exact keepStaticSecretDrop_c2_sub_keepLib2Text h

private theorem noPanic_of_mid_sub_lt {base pc : BitVec 64} {len : Nat}
    (hsub : (pc - base).toNat < len)
    (hlo : 0x47ac2c ≤ base.toNat)
    (hhi : base.toNat + len ≤ 0x4cb070) :
    isLinkedPanicAddr pc = false := by
  generalize hd : pc - base = d at hsub
  have hpc_eq : pc = base + d := by subst hd; bv_omega
  have htoNat : pc.toNat = base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact isLinkedPanicAddr_false_of_mid (by omega) (by omega)

theorem keepR_blackBox_noPanic {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (pc : BitVec 64) (h : keepR_blackBox mpl pc = true) :
    isLinkedPanicAddr pc = false := by
  dsimp only [keepR_blackBox] at h
  rw [hRes, keepBlackBox_iff] at h
  exact noPanic_of_mid_sub_lt h (by decide) (by decide)

theorem keepR_staticSecretDrop_noPanic {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (pc : BitVec 64) (h : keepR_staticSecretDrop mpl pc = true) :
    isLinkedPanicAddr pc = false := by
  dsimp only [keepR_staticSecretDrop] at h
  rw [hRes, keepStaticSecretDrop_iff] at h
  exact noPanic_of_mid_sub_lt h (by decide) (by decide)

/-! ## 3. Per-Row Entry Guards (`blackBoxEntryGuard`, `sharedSecretDropEntryGuard`, `staticSecretDropEntryGuard`) -/

/-! ## 4. Direct Instantiations of `extraEntryGuard_*_arm` & `extraEntryGuard_singleton_*` -/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
