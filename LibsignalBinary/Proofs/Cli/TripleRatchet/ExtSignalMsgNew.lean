/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtEncryptBody -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg1
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg2
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg3
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.TripleRatchet.Wire.New
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Stacked `<SignalMessage>::new` on `tripleRatchetProgAtExt`

Proves `SignalMessageNewOkExt32` (`17840` B stack) on `tripleRatchetProgAtExt img.base ext` under
`AllocContractsX`, `AllocContracts4K`, and stacked `SignalMessage::compute_mac`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNew

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? _root_.Arm64.Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack-Frame Splits -/

theorem stackAt_17424_to_4624 (sp : BitVec 64) :
    stackAt sp Statements.computeMacStackExt32 =
      stackAt sp computeMacStack ∗ memRegion (sp - 17424#64) 12800 := by
  simp only [stackAt, Statements.computeMacStackExt32, Statements.computeMacPkStackExt32,
    newFromSliceStack, extHookStack, computeMacStack, publicKeySerializeStack, allocHookStack]
  rw [show (544 + 2 ^ 14 + 496 : Nat) = 12800 + (4096 + 32 + 496) by decide,
    ProofLib.memRegion_split _ 12800 (4096 + 32 + 496) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (12800 + (4096 + 32 + 496)) = sp - 17424#64 := by bv_arith
  have e2 : sp - 17424#64 + BitVec.ofNat 64 12800 = sp - BitVec.ofNat 64 (4096 + 32 + 496) := by
    bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_17424_to_16912 (sp : BitVec 64) :
    stackAt sp Statements.computeMacStackExt32 =
      stackAt sp computeMacStackX ∗ memRegion (sp - 17424#64) 512 := by
  simp only [stackAt, Statements.computeMacStackExt32, Statements.computeMacPkStackExt32,
    newFromSliceStack, extHookStack, computeMacStackX, publicKeySerializeStackX]
  rw [show (544 + 2 ^ 14 + 496 : Nat) = 512 + (2 ^ 14 + 32 + 496) by decide,
    ProofLib.memRegion_split _ 512 (2 ^ 14 + 32 + 496) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (512 + (2 ^ 14 + 32 + 496)) = sp - 17424#64 := by bv_arith
  have e2 : sp - 17424#64 + BitVec.ofNat 64 512 = sp - BitVec.ofNat 64 (2 ^ 14 + 32 + 496) := by
    bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_17840_to_17328 (sp0 : BitVec 64) :
    stackAt sp0 ExtEncryptBody.signalMessageNewStackExt32 =
      stackAt sp0 signalMessageNewStackX ∗ memRegion ((sp0 - 416#64) - 17424#64) 512 := by
  simp only [stackAt, ExtEncryptBody.signalMessageNewStackExt32, Statements.computeMacStackExt32,
    Statements.computeMacPkStackExt32, newFromSliceStack, extHookStack,
    signalMessageNewStackX, computeMacStackX, publicKeySerializeStackX]
  rw [show (544 + 2 ^ 14 + 496 + 416 : Nat) = 512 + (2 ^ 14 + 32 + 496 + 416) by decide,
    ProofLib.memRegion_split _ 512 (2 ^ 14 + 32 + 496 + 416) (by decide)]
  have e1 : sp0 - BitVec.ofNat 64 (512 + (2 ^ 14 + 32 + 496 + 416)) =
      (sp0 - 416#64) - 17424#64 := by bv_arith
  have e2 : (sp0 - 416#64) - 17424#64 + BitVec.ofNat 64 512 =
      sp0 - BitVec.ofNat 64 (2 ^ 14 + 32 + 496 + 416) := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_signalMessageNewStackExt32_ready (sp0 : BitVec 64) :
    stackAt sp0 ExtEncryptBody.signalMessageNewStackExt32 =
      (∃∗ w408 : BitVec 64, ∃∗ w400 : BitVec 64, ∃∗ w392 : BitVec 64,
       ∃∗ w384 : BitVec 32, ∃∗ w380 : BitVec 32,
       ∃∗ w376 : BitVec 64, ∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64,
       ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64,
       ∃∗ w332 : BitVec 32,
       ∃∗ w328 : BitVec 64, ∃∗ w320 : BitVec 64,
       ∃∗ w176 : BitVec 64, ∃∗ w168 : BitVec 64, ∃∗ w160 : BitVec 64,
        stackAt (sp0 - 416#64) Statements.computeMacStackExt32 ∗
        newUnusedPad sp0 ∗
        ((sp0 - 408#64) ↦₆₄ w408) ∗
        ((sp0 - 400#64) ↦₆₄ w400) ∗
        ((sp0 - 392#64) ↦₆₄ w392) ∗
        ((sp0 - 384#64) ↦₃₂ w384) ∗
        ((sp0 - 380#64) ↦₃₂ w380) ∗
        ((sp0 - 376#64) ↦₆₄ w376) ∗
        ((sp0 - 368#64) ↦₆₄ w368) ∗
        ((sp0 - 360#64) ↦₆₄ w360) ∗
        ((sp0 - 352#64) ↦₆₄ w352) ∗
        ((sp0 - 344#64) ↦₆₄ w344) ∗
        ((sp0 - 332#64) ↦₃₂ w332) ∗
        ((sp0 - 328#64) ↦₆₄ w328) ∗
        ((sp0 - 320#64) ↦₆₄ w320) ∗
        memRegion (sp0 - 312#64) 24 ∗
        memRegion (sp0 - 288#64) 112 ∗
        ((sp0 - 176#64) ↦₆₄ w176) ∗
        ((sp0 - 168#64) ↦₆₄ w168) ∗
        ((sp0 - 160#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 152#64) 16 ∗
        cells (sp0 - 96#64) 12) := by
  rw [stackAt_17840_to_17328 sp0, stackAt_signalMessageNewStackX_ready sp0]
  simp only [sepExists_sepConj_left]
  refine congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ => ?_))))))))))))))))
  rw [stackAt_17424_to_16912 (sp0 - 416#64)]
  ac_rfl

/-! ## Combined Phase 3 (`+0x3dc → lr`) -/

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNew
