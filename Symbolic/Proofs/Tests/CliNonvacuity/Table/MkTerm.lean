/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
public import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
public import Symbolic.Specifications.Concrete.MachineEvents
public import Symbolic.Specifications.Model.Composed
public import Symbolic.Specifications.Model.Instance
public import Symbolic.Specifications.Refinement.Concretization
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.LibsignalE2E.State

/-!
# Compact Term Constructors for Certified Non-Vacuity Tables

Provides short monomorphic wrappers around the 22 `DY.BytesF` constructors and common concrete byte
slices so generated `Table/Bytes*.lean` and `Table/Terms*.lean` modules elaborate without repeated
typeclass synthesis.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm

open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (litOf)
open CryptoVerification.E2E (pqxdhSessionParams)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myParams)

@[expose] def sendAddrABytes : HwBytes := ((pqxdhSessionParams myParams).sendAddrs .A).getD []

@[expose] def tRnd (ts sz : Nat) : DY.Bytes :=
  ({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack

@[expose] def tLit (bs : HwBytes) : DY.Bytes := litOf bs

@[expose] def tCat (lhs rhs : DY.Bytes) : DY.Bytes :=
  ({ lhs, rhs } : DY.Concat.Concat.SubF DY.Bytes).pack

@[expose] def tDhPk (sk : DY.Bytes) : DY.Bytes :=
  ({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack

@[expose] def tDh (pk sk : DY.Bytes) : DY.Bytes :=
  ({ pk, sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack

@[expose] def tKdf (salt ikm : DY.Bytes) : DY.Bytes :=
  ({ salt, ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack

@[expose] def tSym (key iv msg : DY.Bytes) : DY.Bytes :=
  ({ key, iv, msg } : DY.SymEnc.Enc.SubF DY.Bytes).pack

@[expose] def tTr8 (input : DY.Bytes) : DY.Bytes :=
  ({ input } : DY.Trunc.Trunc8.SubF DY.Bytes).pack

@[expose] def tVar (key : DY.Bytes) (torsion : Fin 8) (variation : Fin 4) : DY.Bytes :=
  ({ key, torsion, variation } : DY.X25519.Variant.SubF DY.Bytes).pack

@[expose] def tKemPk (sk : DY.Bytes) : DY.Bytes :=
  ({ sk } : DY.PQKem.Pk.SubF DY.Bytes).pack

@[expose] def tKemEnc (pk entropy : DY.Bytes) : DY.Bytes :=
  ({ pk, entropy } : DY.PQKem.Encap.SubF DY.Bytes).pack

@[expose] def tKemSS (pk entropy : DY.Bytes) : DY.Bytes :=
  ({ pk, entropy } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack

@[expose] def tVk (sk : DY.Bytes) : DY.Bytes :=
  ({ sk } : DY.Signature.Vk.SubF DY.Bytes).pack

@[expose] def tSig (sk nonce msg : DY.Bytes) : DY.Bytes :=
  ({ sk, nonce, msg } : DY.Signature.Sign.SubF DY.Bytes).pack

@[expose] def tSInit (authKey params : DY.Bytes) : DY.Bytes :=
  ({ authKey, params } : DY.Spqr.InitState.SubF DY.Bytes).pack

@[expose] def tSSendSt (st coins : DY.Bytes) : DY.Bytes :=
  ({ st, coins } : DY.Spqr.SendState.SubF DY.Bytes).pack

@[expose] def tSSendK (st coins : DY.Bytes) : DY.Bytes :=
  ({ st, coins } : DY.Spqr.SendKey.SubF DY.Bytes).pack

@[expose] def tSSendM (st coins : DY.Bytes) : DY.Bytes :=
  ({ st, coins } : DY.Spqr.SendMsg.SubF DY.Bytes).pack

@[expose] def tSRecvSt (st msg : DY.Bytes) : DY.Bytes :=
  ({ st, msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack

@[expose] def tSRecvK (st msg : DY.Bytes) : DY.Bytes :=
  ({ st, msg } : DY.Spqr.RecvKey.SubF DY.Bytes).pack

@[expose] def tSChain (authKey params idx : DY.Bytes) : DY.Bytes :=
  ({ authKey, params, idx } : DY.Spqr.ChainKey.SubF DY.Bytes).pack

@[expose] def tTrW (version : UInt8) (senderRatchetKey : DY.Bytes) (counter previousCounter : UInt32)
    (ciphertext pqRatchet : DY.Bytes)
    (encodingVariation : DY.TrWire.EncodingVariation) : DY.Bytes :=
  ({ version, senderRatchetKey, counter, previousCounter, ciphertext, pqRatchet,
     encodingVariation } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack

end Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
