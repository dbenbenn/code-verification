/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

/-!
# Stage P2 Substage P2.6 Tail

Proves `stageP2_sub6_tail_v1_kits` and `stageP2_sub6_tail_v1_kits_ext` (`+0x0b3c → +0x1778`),
deallocating `regIdFutPtr`, promoting the 344-byte `SessionState` via
`SessionRecord::promote_state`, dropping `process_prekey_impl`, and setting up Stage P3 entry.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false

/-! ## 1. Session Byte Glue for Any 280-Byte `mid` (`p2BobSessHead56Bv8`) -/

theorem p2_sub6_bobSession344_split_56_288 (a p1 p2 : BitVec 64)
    (mid : List (BitVec 8)) :
    (a ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) =
      (a ↦₆₄ 33#64) ∗
      ((a + 0x8#64) ↦₆₄ p1) ∗
      ((a + 0x10#64) ↦₆₄ 33#64) ∗
      ((a + 0x18#64) ↦₆₄ 33#64) ∗
      ((a + 0x20#64) ↦₆₄ p2) ∗
      ((a + 0x28#64) ↦₆₄ 33#64) ∗
      ((a + 0x30#64) ↦₆₄ 32#64) ∗
      ((a + 0x38#64) ↦ₛ (mid ++ unpack64 0#64)) := by
  unfold p2BobSessHead56Bv8
  simp only [List.append_assoc]
  rw [pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem p2_sub6_bobSession288Rest_split_280_4_4 (a : BitVec 64)
    (mid : List (BitVec 8)) (hmid : mid.length = 280) :
    (a ↦ₛ (mid ++ unpack64 0#64)) =
      (a ↦ₛ mid) ∗
      ((a + 0x118#64) ↦₃₂ 0#32) ∗
      ((a + 0x11c#64) ↦₃₂ 0#32) := by
  have h0 : unpack64 0#64 = unpack32 0#32 ++ unpack32 0#32 := rfl
  rw [h0, pointsToBytes_append, hmid,
      pointsToBytes_append, unpack32_length,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt p2BobSessHead56Bv8

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem p2_sub6_bobSession344WithRegIds_fold (a p1 p2 : BitVec 64)
    (mid : List (BitVec 8)) (hmid : mid.length = 280)
    (remoteRegId localRegId : BitVec 32) :
    (a ↦₆₄ 33#64) ∗
    ((a + 0x8#64) ↦₆₄ p1) ∗
    ((a + 0x10#64) ↦₆₄ 33#64) ∗
    ((a + 0x18#64) ↦₆₄ 33#64) ∗
    ((a + 0x20#64) ↦₆₄ p2) ∗
    ((a + 0x28#64) ↦₆₄ 33#64) ∗
    ((a + 0x30#64) ↦₆₄ 32#64) ∗
    ((a + 0x38#64) ↦ₛ mid) ∗
    ((a + 0x150#64) ↦₃₂ remoteRegId) ∗
    ((a + 0x154#64) ↦₃₂ localRegId) =
      (a ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
        (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) := by
  have hfold :
      p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)) =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold p2BobSessHead56Bv8
    simp only [List.append_assoc]
  rw [hfold,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, hmid,
      pointsToBytes_append, unpack32_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem p2_sub6_bobSession344WithRegIds_length (p1 p2 : BitVec 64)
    (mid : List (BitVec 8)) (hmid : mid.length = 280)
    (remoteRegId localRegId : BitVec 32) :
    (p2BobSessHead56Bv8 p1 p2 ++
      (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId))).length = 344 := by
  simp only [List.length_append, p2BobSessHead56Bv8_length, hmid, unpack32_length]

theorem p2_sub6_bobSession344WithRegIds_head_split (a p1 p2 : BitVec 64)
    (mid : List (BitVec 8)) (remoteRegId localRegId : BitVec 32) :
    (a ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) =
      (a ↦₆₄ 33#64) ∗
      ((a + 8#64) ↦ₛ (unpack64 p1 ++ (unpack64 33#64 ++
        (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
        (unpack64 32#64 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId))))))))) := by
  have hfold :
      p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)) =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold p2BobSessHead56Bv8
    simp only [List.append_assoc]
  rw [hfold, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]

theorem p2_ro_intro_sub6 {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → s.mem ⊨ Ro ∗ R)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (Ro ∗ P) ∗ R := by rw [sepConj_assoc]; exact hro hm
  exact h R hm' hL

theorem p2_drop_left_sub6 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_drop_frame_sub6 {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ p2_drop_left_sub6 h

theorem p2_alloc_le_sub56_sub6 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    allocHookStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans p2_alloc_le_pure (p2_pure_le_sub56 skit)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

