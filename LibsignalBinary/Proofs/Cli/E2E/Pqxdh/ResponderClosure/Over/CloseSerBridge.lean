/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBody
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClone
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `SessionRecord::serialize` (`Prev1`) Bridge and Contract Assembly

Bridges the internal 32-byte-output body contract `SerializePrev1BodyOkStmt` for
`SessionRecord::serialize` with one previous session to the 48-byte contract `SerializePrev1OkStmt`
and the canonical-ghost form `serializePrev1CanonSpecX`, closing both from `SerContractsX` and
`AllocContractsX`.
-/

public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin
open Proofs.libsignal.Hooks2

private theorem stackAt_sub_split_k5b (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

private theorem stackAt_recordSerialize_split_k5b (sp : BitVec 64) :
    stackAt sp CryptoVerification.E2E.Bin.recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 CryptoVerification.E2E.Bin.recordSerializeStack)
        (CryptoVerification.E2E.Bin.recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split_k5b sp serializeStackX CryptoVerification.E2E.Bin.recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

private theorem memRegion_48_split_32_16_k5b (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

theorem sessionRecordPrevAt_some_eq (A : RustAlloc) (r cap ptr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) (ps : List (List (BitVec 8))) :
    sessionRecordPrevAt A r ⟨cap, ptr, some G⟩ ps ⟨some s⟩ =
      prevVecAt A r cap ptr ps ∗ sessionStateReprAt A (r + 24#64) G s := by
  rw [sessionRecordPrevAt_eq, recCurAt_some]

/-- Canonical-ghost 32-byte-`out` contract for `SessionRecord::serialize` with one previous session
at `serializeStackX`. -/
@[expose] def serializePrev1CanonSpecX (A : RustAlloc) : Spec SerializePrev1BodyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonSession x.G x.sess ∧
      (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      memRegion x.out 32 ∗ A.pool ∗ stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecordPrev1 x.sess x.enc) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
