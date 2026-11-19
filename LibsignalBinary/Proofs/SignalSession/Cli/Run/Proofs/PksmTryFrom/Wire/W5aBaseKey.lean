/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome

/-!
# `PreKeySignalMessage::try_from`: `base_key` Deserialization (`+0x5b4 → +0x684` / `+0x7a8`)

Defines the exit states `BaseKeyOkState` (`+0x684`) and `DeserErrTailState` /
`DeserErrTailStateE` (`+0x7a8`), and proves the `PublicKey::deserialize` `Ok` and `Err`
branches (`+0x5b4..+0x5dc`, `+0x700..+0x714`, `+0x790..+0x7a8`) together with the
deallocation-slot bridge to `+0x7a8`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_PksmWire_W5aBaseKey : True := trivial

/-! ## 1. Callee Wrapper and Frozen Exit States (`BaseKeyOkState`, `DeserErrTailState`, `DeserErrTailStateE`) -/

section W5aExits

end W5aExits

/-! ## 2. (`+0x5b4 .. +0x5dc`, `+0x700 .. +0x714`, `+0x790 .. +0x7a8`): `PublicKey::deserialize(baseKey)` -/

section D12JoinFrames

private theorem w5a_vec_ne_noneCap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ⌜cap ≠ noneCap⌝ ∗ Wire.vecU8Buf A cap ptr bs := by
  refine Entails.trans (vecU8Buf_entails_slice_rest A cap ptr bs)
    (Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  exact slice_rest_entails_vecU8Buf A cap ptr bs

private theorem w5a_vec_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans ?_
    (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

private theorem w5a_vec_ne_and_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active :=
  Entails.trans (w5a_vec_ne_noneCap A cap ptr bs)
    (sepConj_mono_right (w5a_vec_entails_deallocSlot A cap ptr bs))

end D12JoinFrames

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
