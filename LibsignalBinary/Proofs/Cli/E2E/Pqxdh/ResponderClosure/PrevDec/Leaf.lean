/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafA
import ProofLib
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

public section

set_option autoImplicit false

/-!
# Handshake `prost::encoding::skip_field::<&mut &[u8]> [local#6]` (StartGroup and Assembly)

Verifies the `.startGroup` case (`skipField6_startGroup_ok`) and assembles full recursion-depth
induction (`skipField6_ok_ext`, `skipField6_ok`) for `prost::encoding::skip_field::<&mut &[u8]> [local#6]`
against `(skipField3Spec A).inImage img` (`LibsignalProtoCodec.skipField`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

/-! ## Case 7: `depth = d + 1`, `wt = .startGroup` -/

private abbrev skipGroupLoopPost6 (A : RustAlloc) (s0 : State) (d : Nat)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨
        (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜sf.trace = s0.trace⌝ ∗
            (bufRef ↦₆₄ slot) ∗
              A.pool ∗
                skipBelow3 s0.sp (d + 1) ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                    ((s0.sp - 48#64) ↦₆₄ x_5) ∗
                      ((s0.sp - 40#64) ↦₆₄ x_4) ∗
                        ((s0.sp - 32#64) ↦₆₄ x_3) ∗
                          ((s0.sp - 24#64) ↦₆₄ x_2) ∗
                            ((s0.sp - 16#64) ↦₆₄ x_1) ∗
                              ((s0.sp - 8#64) ↦₆₄ x) ∗
                                match res with
                                | some rest =>
                                  ⌜sf.readReg64 Reg.x0 = 0#64⌝ ∗
                                    sliceCursorAfter slot ptr bs rest
                                | none =>
                                  ⌜sf.readReg64 Reg.x0 ≠ 0#64⌝ ∗
                                    decodeErrorAtStackLen A (sf.readReg64 Reg.x0) 0 ∗
                                      memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev skipGroupLoopPanic6 (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  sf.mem ⊨ P_f ∗ R → (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
