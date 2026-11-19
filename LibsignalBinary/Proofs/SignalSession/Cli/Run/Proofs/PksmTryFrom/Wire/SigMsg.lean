/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym
import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict

/-!
# `PreKeySignalMessage::try_from`: `SignalMessage::try_from` and `try_clone_from_ref` Stage

Symbolic execution from `+0x864`: calls `SignalMessage::try_from` (`+0x864 → +0x878`),
branches to `SigMsgErrState` (`+0x9f0`) preserving the 6 error payload words on `.error e`,
or copies the 14 `Ok` words and calls `try_clone_from_ref` (`+0x878 → +0x8bc → +0x8c0 / +0xa68`).
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
open CryptoVerification.LibsignalTripleRatchet.Prost hiding memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Local kernel-checked BitVec normalizers -/

private theorem sm_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem sm_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem sm_bv_add_neg_8 (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem sm_bv_add_neg_16 (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem sm_bv_add_neg_24 (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem sm_bv_add_neg_32 (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem sm_bv_add_neg_40 (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem sm_bv_add_neg_48 (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem sm_bv_add_neg_55 (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem sm_bv_add_neg_56 (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem sm_bv_add_neg_64 (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem sm_bv_add_neg_72 (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem sm_bv_add_neg_80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem sm_bv_add_neg_87 (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem sm_bv_add_neg_88 (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem sm_bv_add_neg_96 (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem sm_bv_add_neg_104 (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem sm_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem sm_bv_add_neg_120 (x : BitVec 64) : x + bv% (2 ^ 64 - 120) = x - 120#64 := by bv_omega
private theorem sm_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem sm_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem sm_bv_add_neg_144 (x : BitVec 64) : x + bv% (2 ^ 64 - 144) = x - 144#64 := by bv_omega
private theorem sm_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem sm_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem sm_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem sm_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem sm_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem sm_bv_add_neg_186 (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem sm_bv_add_neg_191 (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem sm_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem sm_bv_add_neg_196 (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem sm_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem sm_bv_add_neg_216 (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem sm_bv_add_neg_512 (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sm_bv_sub_add_lit' sm_bv_sub_sub_lit BitVec.toNat_zero
  sm_bv_add_neg_8 sm_bv_add_neg_16 sm_bv_add_neg_24 sm_bv_add_neg_32 sm_bv_add_neg_40
  sm_bv_add_neg_48 sm_bv_add_neg_55 sm_bv_add_neg_56 sm_bv_add_neg_64 sm_bv_add_neg_72
  sm_bv_add_neg_80 sm_bv_add_neg_87 sm_bv_add_neg_88 sm_bv_add_neg_96 sm_bv_add_neg_104
  sm_bv_add_neg_112 sm_bv_add_neg_120 sm_bv_add_neg_128 sm_bv_add_neg_136 sm_bv_add_neg_144
  sm_bv_add_neg_152 sm_bv_add_neg_160 sm_bv_add_neg_168 sm_bv_add_neg_176 sm_bv_add_neg_184
  sm_bv_add_neg_186 sm_bv_add_neg_191 sm_bv_add_neg_192 sm_bv_add_neg_196 sm_bv_add_neg_200
  sm_bv_add_neg_216 sm_bv_add_neg_512

/-! ## 1. Stack-Split & Region Packing Helpers -/

theorem stackAt_skipFieldStackX_tryCloneX (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - LibsignalTripleRatchet.tryCloneFromRefStackX) ∗
        stackAt sp LibsignalTripleRatchet.tryCloneFromRefStackX :=
  stackAt_sub_split sp LibsignalTripleRatchet.tryCloneFromRefStackX (Prost.skipFieldStackX 100)
    (by decide) (by decide)

theorem stackAt_smallRoot_tryCloneX (sp : BitVec 64) :
    stackAt sp smallRootStack =
      memRegion (sp - BitVec.ofNat 64 smallRootStack)
        (smallRootStack - LibsignalTripleRatchet.tryCloneFromRefStackX) ∗
        stackAt sp LibsignalTripleRatchet.tryCloneFromRefStackX :=
  stackAt_sub_split sp LibsignalTripleRatchet.tryCloneFromRefStackX smallRootStack
    (by decide) (by decide)

/-- Packing the `IdentityKey::try_from` 40-byte output slot `sp' + 312..352` plus
`memRegion (sp' + 352) 8` and `memRegion (sp' + 360) 72` into `memRegion (sp' + 312) 120`
for `SignalMessage::try_from`. -/
theorem ident_slot_entails_memRegion120 (sp' tag : BitVec 64) (ipk : PublicKey) :
    ((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
      memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ⊢
      memRegion (sp' + 312#64) 120 := by
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ipk.bytes)
  rw [hik (sp' + 320#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact words5_memRegion8_72_entails_120 sp' tag ik0 ik1 ik2 ik3

/-! ## 2. Leaf L3a (`+0x864 .. +0x878` / `2148 .. 2168`): `SignalMessage::try_from` Call -/

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
