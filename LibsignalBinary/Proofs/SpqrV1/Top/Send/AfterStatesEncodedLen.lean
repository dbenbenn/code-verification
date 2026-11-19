/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# `spqr::send`: `PqRatchetState` Encoded Length & Buffer Allocation

Symbolic execution of the inlined `PqRatchetState::encoded_len` computation and output buffer
allocation (`0x3191c..0x31e40`, `+4288..+5604`) in `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ProofLib.truncate32_ofNat64
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

/-! ## 1. Stack Split & Callee Address Helpers for `spqr::send` (`0x3085c`) -/

theorem stackAt_spqrSendCallee_split_enc (sp : BitVec 64) (subStack : Nat)
    (hle : subStack ≤ spqrSendCalleeStack) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - subStack) ∗
        stackAt sp subStack := by
  have h := ProofLib.stackAt_split_bottom sp subStack (spqrSendCalleeStack - subStack)
    (by unfold spqrSendCalleeStack at hle ⊢; omega)
  have heq : subStack + (spqrSendCalleeStack - subStack) = spqrSendCalleeStack := by omega
  simpa only [heq] using h

/-- Stack-equipped no-op shim contract at `s.sp` with `spqrSendCalleeStack`. -/
@[expose] def spqrSendShimStackSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp spqrSendCalleeStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp spqrSendCalleeStack

/-- Stack-equipped `__rust_alloc(sz, 1)` contract at `s.sp` with `spqrSendCalleeStack`. -/
@[expose] def spqrSendRustAllocStackSpec (A : RustAlloc) : Spec Nat where
  pre := fun sz s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63⌝ ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack
  post := fun sz s0 sf =>
    (if sf.readReg64 .x0 = 0#64 then
      ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz) ∗
      A.pool ∗ stackAt s0.sp spqrSendCalleeStack

theorem pqRatchetStatePBEncodedLen_pos_of_inner_some {st : PqRatchetState} {v1s : V1StatePB}
    (hin : st.inner = some (.v1 v1s)) :
    0 < pqRatchetStatePBEncodedLen st := by
  have hpos := optPqRatchetInnerPBFieldEncodedLen_pos (.v1 v1s)
  unfold pqRatchetStatePBEncodedLen
  rw [hin]
  omega

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

end CryptoVerification.SpqrV1.Top.Send
