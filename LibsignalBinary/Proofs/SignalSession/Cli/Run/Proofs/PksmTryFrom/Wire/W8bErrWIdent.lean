/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKey -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym

/-!
# `PreKeySignalMessage::try_from`: `identity_key` Deserialization Error Continuation (`PreKeyIdentErrW`)

Proves `preKeyIdentErrW_proof` (`+0x830 → +0x978 → +0x504 → ret`) from
`preKey_ident_err_830_to_978_wpE`, `ErrTailC.e_978_wpE`, and `w8b_errTail_close`.
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8bIdErr_exists4_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 P4 : Bool → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a b c d, SepWPp prog ret s (P1 a ∗ P2 b ∗ P3 c ∗ P4 d ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ a, P1 a) ∗ (∃∗ b, P2 b) ∗ (∃∗ c, P3 c) ∗ (∃∗ d, P4 d) ∗ F) Q Qp := by
  refine w8bErrW_exists_pre_frame fun a => ?_
  refine SepWPp.mono_pre (P' := (∃∗ b, P2 b) ∗ P1 a ∗ (∃∗ c, P3 c) ∗ (∃∗ d, P4 d) ∗ F)
    (by apply entails_of_eq; ac_rfl) ?_
  refine w8bErrW_exists_pre_frame fun b => ?_
  refine SepWPp.mono_pre (P' := (∃∗ c, P3 c) ∗ P1 a ∗ P2 b ∗ (∃∗ d, P4 d) ∗ F)
    (by apply entails_of_eq; ac_rfl) ?_
  refine w8bErrW_exists_pre_frame fun c => ?_
  refine SepWPp.mono_pre (P' := (∃∗ d, P4 d) ∗ P1 a ∗ P2 b ∗ P3 c ∗ F)
    (by apply entails_of_eq; ac_rfl) ?_
  refine w8bErrW_exists_pre_frame fun d => ?_
  exact SepWPp.mono_pre (by apply entails_of_eq; ac_rfl) (h a b c d)

/-- `kyberStageOut` entails an existential Kyber `boxSlot`. -/
theorem w8bIdErr_kyberStageOut_boxSlot (A : RustAlloc) (kpkVal : BitVec 32) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (kbPtr kbLen : BitVec 64) :
    kyberStageOut A kpkVal vb kpkOpt kyberOpt kbPtr kbLen ⊢
      ∃∗ boxAct : Bool, boxSlot A kbPtr kbLen boxAct := by
  cases kpkOpt with
  | some kpkId =>
    cases kyberOpt with
    | some kyberCt =>
      dsimp only [kyberStageOut]
      refine Entails.pure_left fun ⟨_, hlen, _⟩ => ?_
      subst hlen
      exact Entails.trans (boxU8Buf_entails_boxSlot A kbPtr kyberCt)
        (Entails.sepExists_intro (!kyberCt.isEmpty))
    | none =>
      dsimp only [kyberStageOut]
      exact Entails.pure_left_only False.elim
  | none =>
    cases kyberOpt with
    | some _ =>
      dsimp only [kyberStageOut]
      exact Entails.pure_left_only False.elim
    | none =>
      dsimp only [kyberStageOut]
      refine Entails.pure_left_only fun ⟨hptr, _⟩ => ?_
      subst hptr
      exact Entails.trans (boxSlot_of_null A kbLen) (Entails.sepExists_intro false)

/-- `Wire.vecU8Buf` entails an existential `deallocSlot`. -/
theorem w8bIdErr_vecU8Buf_dealloc (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Wire.vecU8Buf A cap ptr bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans ?_
    (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

theorem w8bIdErr_memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗ memRegion (sp' + 16#64) 96 ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 120 := by
  rw [show (296 : Nat) = 12 + (4 + (96 + (32 + (32 + 120)))) by decide,
    Prost.memRegion_split sp' 12 284 (by decide),
    Prost.memRegion_split (sp' + 12#64) 4 280 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64) 96 184 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64) 32 152 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64) 32 120 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem w8bIdErr_memRegion152_split48 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 48 ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        memRegion (sp' + 440#64) 8 := by
  rw [show (152 : Nat) = 16 + (48 + (72 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64) 48 88 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64) 72 16 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64 + 72#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
