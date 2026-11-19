/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

@[expose] def kemPubSerializeValAtStkSpec (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (boxPtr, pkBytes) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧ s.readReg64 .x1 = 1568#64 ∧ pkBytes.length = 1568⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗ A.pool ∗ stackAt s.sp calleeStk
  post := fun (boxPtr, pkBytes) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗
      ((sf.readReg64 .x0) ↦ₛ (8#8 :: pkBytes)) ∗ A.live (sf.readReg64 .x0) 1569 1 ∗
      A.pool ∗ stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private abbrev kemPubSerFixedStk : Nat := extHookStack + 48

private theorem stackAt_kemPubSerFixed (sp : BitVec 64) :
    stackAt sp kemPubSerFixedStk =
      stackAt (sp - 48#64) extHookStack ∗ ProofLib.cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_1569_split_local (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one]

private theorem sepWPp_pure_mid_local {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem panic_mem_of_trace_eq (s0 : State) {sp : State} {Pm R : SepProp}
    (htr : sp.trace = s0.trace ++ [allocFailedEvent]) (hm : sp.mem ⊨ Pm ∗ R) :
    sp.mem ⊨ ⌜allocFailedIn s0 sp ∧ s0.trace <+: sp.trace⌝ ∗ anyHeap ∗ R := by
  rw [← sepConj_assoc]
  exact Satisfies.mono
    (sepConj_mono_left
      (pure_sepConj_intro
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq htr)
        (entails_anyHeap Pm)))
    hm

private theorem sp_sub_48_add_48 (sp : BitVec 64) : (sp - 48#64) + 48#64 = sp := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_48_add_48 sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96
  BitVec.toNat_zero
end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
