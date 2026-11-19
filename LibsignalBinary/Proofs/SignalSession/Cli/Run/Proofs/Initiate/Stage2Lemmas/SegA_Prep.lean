/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 Prefix Steps (`0x0390 → 0x0464`): Ephemeral Key Derivation and `get_identity_key_pair` Poll

Verifies the three Stage 2 preparation steps on `initProg` and `initProgExt`:
1. `segA_step1_coins` (`+912 → +952`): fresh `SessionRecord` header and 32-byte `coins_fill`.
2. `segA_step2_ek` (`+952 → +1036`): X25519 scalar clamping, `derive_public_key_bytes`, and `StaticSecret::drop`.
3. `segA_step3_poll` (`+1036 → +1124`): `get_identity_key_pair` shim and poll.
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

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
