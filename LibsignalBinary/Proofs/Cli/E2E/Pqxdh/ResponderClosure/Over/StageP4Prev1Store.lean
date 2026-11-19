/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34Err
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrA
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Stage P4.4 (`store_session`) on 1-Element `previous_sessions`

Defines the `StorePrev1Ops` and `SessionPrev1KitOkSE` contract interface for
`SessionStore::store_session` on a record with `previous_sessions = [enc]` and proves Substage P4.4
(`+0x3cc → s0.readReg64 .x30`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

/-! ## `StorePrev1Ops` and `SessionPrev1KitOkSE` Contract Bundle -/

/-- Ghost call parameters for `SessionStore::store_session` poll on a 1-previous-session record. -/
structure StorePrev1Call where
  fut : BitVec 64
  out : BitVec 64
  addrA : BitVec 64
  addr : AddrGhost
  recA : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)

/-- Pure relation, state-update, and trace-event operations for `store_session` on a record with
current session `(G, sess)` and `previous_sessions = [enc]`. -/
structure StorePrev1Ops {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) where
  RecPrev1Ok : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop
  storeRelPrev1 : kit.StoreState → AddrVal → SessionGhost →
    Session (List (BitVec 8)) → List (BitVec 8) → Except Unit Unit → Prop
  storeUpdatePrev1 : kit.StoreState → AddrVal → SessionGhost →
    Session (List (BitVec 8)) → List (BitVec 8) → Except Unit Unit → kit.StoreState
  storeEvsPrev1 : AddrVal → SessionGhost →
    Session (List (BitVec 8)) → List (BitVec 8) → Except Unit Unit → List TraceEvent

/-- `store_session` poll specification on `sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩
[x.enc] ⟨some x.sess⟩`. -/
@[expose] def kitStorePollPrev1Spec {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ops : StorePrev1Ops kit) :
    Spec (StorePrev1Call × BitVec 64 × kit.StoreState) where
  pre := fun (x, self, st0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      ops.RecPrev1Ok x.G x.sess x.enc ∧ kit.addrOk x.addr.val⌝ ∗
      kit.storeBoxAt x.fut self x.addrA x.recA 0#8 ∗
      kit.storeAt self st0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.addr x.addrA ∗
      sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      A.pool ∗ stackAt s.sp kit.storePollStack
  post := fun (x, self, st0) s0 sf =>
    ∃∗ ans : Except Unit Unit,
      ⌜ops.storeRelPrev1 st0 x.addr.val x.G x.sess x.enc ans ∧
        sf.trace = s0.trace ++ ops.storeEvsPrev1 x.addr.val x.G x.sess x.enc ans⌝ ∗
      kit.storeBoxAt x.fut self x.addrA x.recA 1#8 ∗
      kit.storeAt self (ops.storeUpdatePrev1 st0 x.addr.val x.G x.sess x.enc ans) ∗
      storePollOutAt b x.out ans ∗
      protocolAddressAt A x.addr x.addrA ∗
      sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      A.pool ∗ stackAt s0.sp kit.storePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kitStorePollPrev1SpecE {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ops : StorePrev1Ops kit) :
    Spec (StorePrev1Call × BitVec 64 × kit.StoreState) :=
  withEnvPre (kitStorePollPrev1Spec kit ops) fun s => kit.envOk s.fs.files

theorem prevVecAt_sessionRecordPrevAt_fold (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss) :
    prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
    sessionStateAt A (coroPtr + 0xf8#64) G ss.state ⊢
      sessionRecordPrevAt A (coroPtr + 0xe0#64) ⟨prevCap, prevPtr, some G⟩ [enc] ⟨some ss⟩ := by
  unfold sessionRecordPrevAt recCurAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hExtra (Entails.refl _))

theorem prevVecAt_sessionRecordPrevAt_unfold (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordPrevAt A (coroPtr + 0xe0#64) ⟨prevCap, prevPtr, some G⟩ [enc] ⟨some ss⟩ ⊢
      prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
      sessionStateAt A (coroPtr + 0xf8#64) G ss.state := by
  unfold sessionRecordPrevAt recCurAt sessionStateReprAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_left fun _ => Entails.refl _)

private theorem coro2c8_16_split_eq_prev1 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u_2d0 : BitVec 64, ∃∗ u_2c8 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x2c8#64),
      ProofLib.memRegion_eight (coroPtr + 0x2d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem coro2c8_16_fold_prev1 (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x2c8#64) ↦₆₄ v0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ v1) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
