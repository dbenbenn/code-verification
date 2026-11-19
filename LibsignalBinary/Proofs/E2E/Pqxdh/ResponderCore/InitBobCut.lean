/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.CodeLayout

/-!
# `initialize_bob_session` (`0x21c80`): Rejecting Run and Cut at `spqr::initial_state`

Proves `initializeBobSession_err_ok` when `Model.acceptKeys P inp = none` and establishes the
entry-to-`spqr::initial_state` cut (`BobCutPost`) on the accepting branch.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
@[expose] def BobPanicOom (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

/-- The cells at Bob's `spqr::initial_state` call (`sp0` = `initialize_bob_session`'s entry `sp`,
`rkp` = its `x1`): the `Params` at `sp0 - 488` (`auth_key` = the `pqr_key` at `sp0 - 576`,
`max_jump = 25000`, `max_ooo = 2000`, `B2A`, `V1`, `V1`), the root key at `sp0 - 656`
(`= sp + 0x70`), the chain key at `sp0 - 624` (`= sp + 0x90`) and the ratchet pair at `rkp`. -/
@[expose] def bobSpqrCutCells (sp0 rkp : BitVec 64) (rk pq ck spkPk spkSk : Bytes) : SepProp :=
  ((sp0 - 488#64) ↦₆₄ (sp0 - 576#64)) ∗ ((sp0 - 480#64) ↦₆₄ 32#64) ∗
  ((sp0 - 472#64) ↦₃₂ 25000#32) ∗ ((sp0 - 468#64) ↦₆₄ 0x1000007d0#64) ∗
  ((sp0 - 460#64) ↦₆₄ 0x100000001#64) ∗
  ((sp0 - 576#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 656#64) ↦ₛ bytesToBv8 rk) ∗
  ((sp0 - 624#64) ↦ₛ bytesToBv8 ck) ∗
  (rkp ↦ₛ bytesToBv8 spkPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkSk)

@[expose] def BobCutPost (entry : BitVec 64) (s0 : State) (rkp : BitVec 64) (rk pq ck spkPk spkSk : Bytes)
    (K : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ bobSpqrCutCells s0.sp rkp rk pq ck spkPk spkSk ∗ K ∗ anyHeap) ∧
  sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
  sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
  sf.readReg64 (.gpr 20#5) = rkp ∧
  sf.readReg64 (.gpr 30#5) = entry + 252#64 ∧
  sf.trace = s0.trace

theorem bobCut_entails {P T K F : SepProp} (h : P ⊢ (T ∗ K) ∗ F) : P ⊢ T ∗ K ∗ anyHeap :=
  Entails.trans h (by
    rw [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

end CryptoVerification.E2E.Pqxdh.ResponderCore
