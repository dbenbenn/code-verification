/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `.rodata` (`MlKemRoOk`) Discharger for `mlkemMultiLib`

Batches all 11 read-only `.rodata` tables of `mlkemMultiLib` (`ZETA_TABLE`, `KECCAK_RC`, and
`cst16.0`..`cst16.8`, 592 B total in `seg[0]`) into a single `rfl_kernel` slice check on
`f3PatchedElf`, discharging `MlKemRoOk c2MlkemMpl m` from `F3CodeInv`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRoData

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
  (mlkemData00Bytes mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes
   mlkemData05Bytes mlkemData06Bytes mlkemData07Bytes mlkemData08Bytes mlkemData09Bytes
   mlkemData10Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (rGetD_map_some_eq_getElem?)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3CodeInv_roDataAt_of_checkSegSlice)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)

private noncomputable def checkMlkemRoAll (elf : Process.ElfImage) : Bool :=
  match ProofLib.Placed.Split.rGetD (elf.segments.map some) f3StdLayout.roSegIdx none with
  | none => false
  | some seg =>
    let roLen := ProofLib.Placed.Split.rLen seg.bytes
    decide (seg.perm.rwx = Perm.ro) &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0")
      mlkemData00Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
      mlkemData01Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0") mlkemData02Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1") mlkemData03Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.2") mlkemData04Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.3") mlkemData05Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.4") mlkemData06Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.5") mlkemData07Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6") mlkemData08Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.7") mlkemData09Bytes &&
    checkSegSlice seg roLen
      (c2MlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.8") mlkemData10Bytes

set_option maxRecDepth 4000000 in
private theorem c2_mlkem_roSlices_ok : checkMlkemRoAll f3PatchedElf = true := by
  rfl_kernel

theorem c2_mlkem_roOk_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    MlKemRoOk c2MlkemMpl m := by
  have h := c2_mlkem_roSlices_ok
  unfold checkMlkemRoAll at h
  rw [rGetD_map_some_eq_getElem?] at h
  cases hseg : f3PatchedElf.segments[f3StdLayout.roSegIdx]? with
  | none => rw [hseg] at h; cases h
  | some seg =>
    rw [hseg] at h
    dsimp only at h
    simp only [ProofLib.Placed.Split.rLen_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hperm, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
    exact
      { zetaTable := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h0⟩
        keccakRc  := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h1⟩
        cst16_0   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h2⟩
        cst16_1   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h3⟩
        cst16_2   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h4⟩
        cst16_3   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h5⟩
        cst16_4   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h6⟩
        cst16_5   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h7⟩
        cst16_6   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h8⟩
        cst16_7   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h9⟩
        cst16_8   := f3CodeInv_roDataAt_of_checkSegSlice hLs hInv _ _ ⟨seg, hseg, hperm, h10⟩ }

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRoData
