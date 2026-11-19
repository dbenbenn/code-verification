/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 2 `pqspkB` Clone and `is_same_account` Check (`0x0650 → 0x068c`)

Verifies Step C2 (`segC_step2_clone`: 1568-byte `pqspkB` allocation and `memcpy`, with OOM exit via
`alloc::raw_vec::handle_error`) and Step C3 (`segC_step3_sameAcct`: `<IdentityKey>::is_same_account`
returning `false` under `InitOk₀.distinctAcct`).
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16
  symtab_setPC_pre symtab_setMem_pre symtab_setPState_pre
  symtab_writeReg64_pre symtab_writeReg32_pre symtab_writeReg_pre symtab_writeVReg128_pre

theorem mr_280_staging_split (sp : BitVec 64) :
    memRegion (sp + 840#64) 280 =
      memRegion (sp + 840#64) 32 ∗
      memRegion (sp + 872#64) 32 ∗
      memRegion (sp + 904#64) 32 ∗
      memRegion (sp + 936#64) 32 ∗
      memRegion (sp + 968#64) 32 ∗
      memRegion (sp + 1000#64) 32 ∗
      memRegion (sp + 1032#64) 32 ∗
      memRegion (sp + 1064#64) 8 ∗
      memRegion (sp + 1072#64) 8 ∗
      memRegion (sp + 1080#64) 1 ∗
      memRegion (sp + 1081#64) 32 ∗
      memRegion (sp + 1113#64) 1 ∗
      memRegion (sp + 1114#64) 6 := by
  rw [mr_split (sp + 840#64) (sp + 872#64) 32 248 280 rfl (by bv_omega),
      mr_split (sp + 872#64) (sp + 904#64) 32 216 248 rfl (by bv_omega),
      mr_split (sp + 904#64) (sp + 936#64) 32 184 216 rfl (by bv_omega),
      mr_split (sp + 936#64) (sp + 968#64) 32 152 184 rfl (by bv_omega),
      mr_split (sp + 968#64) (sp + 1000#64) 32 120 152 rfl (by bv_omega),
      mr_split (sp + 1000#64) (sp + 1032#64) 32 88 120 rfl (by bv_omega),
      mr_split (sp + 1032#64) (sp + 1064#64) 32 56 88 rfl (by bv_omega),
      mr_split (sp + 1064#64) (sp + 1072#64) 8 48 56 rfl (by bv_omega),
      mr_split (sp + 1072#64) (sp + 1080#64) 8 40 48 rfl (by bv_omega),
      mr_split (sp + 1080#64) (sp + 1081#64) 1 39 40 rfl (by bv_omega),
      mr_split (sp + 1081#64) (sp + 1113#64) 32 7 39 rfl (by bv_omega),
      mr_split (sp + 1113#64) (sp + 1114#64) 1 6 7 rfl (by bv_omega)]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
