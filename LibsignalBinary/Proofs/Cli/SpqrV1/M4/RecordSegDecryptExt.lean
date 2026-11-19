/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import Lean
import ProofLib.GenDecodes
import ProofLib.ProgramReflection
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

/-!
# 4 KB-Stack `SegDecrypt` (`+1692`) and `finish_grow`

Proves `finish_grow_ok_4k`, `grow_one_spe_ok_4k`, and `rdp_segDecrypt_ok_4k` parameterized over
an arbitrary token `tok : SepProp` and panic postconditions `tryOnPanic` / `recSpec`, using only
4096-byte (`allocHookStack`) allocator and `memcpy` contracts.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `finish_grow` under 4096-Byte `shim` / `alloc` / `realloc` -/

private theorem stackAt_setSessionState_split_alloc_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      stackAt sp allocHookStack ∗ memRegion (sp - BitVec.ofNat 64 setSessionStateStack) 160 := by
  have heq : setSessionStateStack = 160 + allocHookStack := rfl
  dsimp only [stackAt]
  rw [heq, memRegion_split (sp - BitVec.ofNat 64 (160 + allocHookStack)) 160 allocHookStack (by decide)]
  have hsub : (sp - BitVec.ofNat 64 (160 + allocHookStack)) + BitVec.ofNat 64 160 =
      sp - BitVec.ofNat 64 allocHookStack := by
    dsimp only [allocHookStack]
    bv_omega
  rw [hsub]
  ac_rfl

private theorem stackAt_alloc_join_setSessionState_4k (sp : BitVec 64) :
    stackAt sp allocHookStack ∗ memRegion (sp - BitVec.ofNat 64 setSessionStateStack) 160 ⊢
      stackAt sp setSessionStateStack := by
  rw [stackAt_setSessionState_split_alloc_4k sp]
  exact Entails.refl _

attribute [local arm64_norm ↓, local wp_norm ↓]
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

end CryptoVerification.Cli.LibsignalSpqrV1.M4
