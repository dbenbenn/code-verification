/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRoData -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks0
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks1
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks2
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks3
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks4
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks5

/-!
# Top-Level `mlkemMultiLib` Layout Facts

Combines `MlKemPlaceable`, `MlKemRoData`, and the 6 block-walk shards `MlKemBlocks0..5` into the
unified `32`-block RX subslice, `CodeLoaded`, and `Placeable ∧ CodeLoaded ∧ MlKemRoOk` bundle for
all 7 ML-KEM / Kyber entry points (`kyber1024::{encapsulate,decapsulate}` and
`mlkem768::incremental::{from_seed,encapsulate1,encapsulate2,decapsulate_compressed_key,validate_pk_bytes}`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem

open Arm64 Arm64.Obj
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks0
  (c2_mlkem_rx_blocks_0 mlkemShard0)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks1
  (c2_mlkem_rx_blocks_1 mlkemShard1)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks2
  (c2_mlkem_rx_blocks_2 mlkemShard2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks3
  (c2_mlkem_rx_blocks_3 mlkemShard3)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks4
  (c2_mlkem_rx_blocks_4 mlkemShard4)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemBlocks5
  (c2_mlkem_rx_blocks_5 mlkemShard5)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2MlkemMpl c2_mlkem_placeable)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemRoData
  (c2_mlkem_roOk_of_f3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)

private theorem mem_mlkemShards_of_lt {k : Nat} (hk : k < mlkemMultiLib.blocks.length) :
    k ∈ mlkemShard0 ∨ k ∈ mlkemShard1 ∨ k ∈ mlkemShard2 ∨
      k ∈ mlkemShard3 ∨ k ∈ mlkemShard4 ∨ k ∈ mlkemShard5 := by
  have hall :
      ∀ j ∈ List.range mlkemMultiLib.blocks.length,
        j ∈ mlkemShard0 ∨ j ∈ mlkemShard1 ∨ j ∈ mlkemShard2 ∨
          j ∈ mlkemShard3 ∨ j ∈ mlkemShard4 ∨ j ∈ mlkemShard5 := by
    decide
  exact hall k (List.mem_range.mpr hk)

/-- All 32 code blocks of `mlkemMultiLib` appear inside `f3TrialRxProg` (`seg[2]`). -/
theorem c2_mlkem_rx_blocks :
    ∀ k < mlkemMultiLib.blocks.length,
      checkProgCodeSubslice f3TrialRxProg (mlkemMultiLib.blockProgram c2MlkemMpl k) = true := by
  intro k hk
  rcases mem_mlkemShards_of_lt hk with h0 | h1 | h2 | h3 | h4 | h5
  · exact c2_mlkem_rx_blocks_0 k h0
  · exact c2_mlkem_rx_blocks_1 k h1
  · exact c2_mlkem_rx_blocks_2 k h2
  · exact c2_mlkem_rx_blocks_3 k h3
  · exact c2_mlkem_rx_blocks_4 k h4
  · exact c2_mlkem_rx_blocks_5 k h5

/-- Full `mlkemMultiLib.CodeLoaded c2MlkemMpl m` derived from `F3CodeInv`. -/
theorem c2_mlkem_codeLoaded_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    mlkemMultiLib.CodeLoaded c2MlkemMpl m :=
  fun k hk => codeLoaded_of_checkProgCodeSubslice hInv.rxCode (c2_mlkem_rx_blocks k hk)

/-- Combined `Placeable ∧ CodeLoaded ∧ MlKemRoOk` memory invariant bundle for `mlkemMultiLib`
    derived from `F3CodeInv`. -/
theorem c2_mlkem_invMem_of_f3CodeInv {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    mlkemMultiLib.Placeable c2MlkemMpl ∧
      mlkemMultiLib.CodeLoaded c2MlkemMpl m ∧
      MlKemRoOk c2MlkemMpl m :=
  ⟨c2_mlkem_placeable, c2_mlkem_codeLoaded_of_f3CodeInv hInv, c2_mlkem_roOk_of_f3CodeInv hLs hInv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem
