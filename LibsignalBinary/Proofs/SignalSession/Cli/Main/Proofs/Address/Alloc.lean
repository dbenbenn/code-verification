/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Exit and Allocation Paths for `signal_session::address`

Proofs of the `None` exit block (`+352 .. +380`) and the device sign-extension and name-allocation
path (`+256 .. +284`, `+384 .. +468`) of `signal_session::address`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout

abbrev AddrFrameCommon (A : RustAlloc) (resStack : Nat) (s0 : State) : SepProp :=
  A.pool ∗
  memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
  stackAt (s0.sp - 96#64) subStackSize ∗
  memRegion (s0.sp - 96#64) 32 ∗
  addrSavedRegs s0.sp s0

abbrev AddrGoalPost (A : RustAlloc) (resStack : Nat) (x : AddressCall) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (addressSpec A uuidTryParse resStack).post x s0 sf)

theorem bind_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let st := s; SepWPp prog ret st P Q Qp) :
    SepWPp prog ret s P Q Qp := h

theorem sepWPp_pull_pure3 {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 : SepProp} {φ : Prop} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A1 ∗ A2 ∗ Rest) Q Qp) :
    SepWPp prog ret s (A1 ∗ A2 ∗ ⌜φ⌝ ∗ Rest) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim h)

private theorem serviceIdParse_bv_props {name : List (BitVec 8)}
    {res : Bool × List.Vector (BitVec 8) 16}
    (h : serviceIdParse uuidTryParse name = some res) :
    0 < name.length ∧
      name.length < 2 ^ 63 ∧
      BitVec.extractLsb' 63 1 (BitVec.ofNat 64 name.length) = 0#1 ∧
      BitVec.ofNat 64 name.length ≠ 0#64 ∧
      (BitVec.ofNat 64 name.length == 0#64) = false ∧
      (BitVec.ofNat 64 name.length).toNat = name.length ∧
      LayoutOk name.length 1 := by
  rcases serviceIdParse_length h with hlen | hlen <;> rw [hlen] <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩

/-! ## `None` Exit (`step_none_exit`) -/

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
