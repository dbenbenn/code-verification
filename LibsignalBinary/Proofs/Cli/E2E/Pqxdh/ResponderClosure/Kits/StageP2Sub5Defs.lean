/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux

/-!
# Stage P2 Substage P2.5 V1 Bundle and Combinators

Defines `p2BobSessV1At`, stack/error unpacking helpers, and `p2_call_inImage_oom_steps_frame` shared
by `StageP2Sub5Aux` and `StageP2Sub5V1`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-- The `0x700` stack bytes `initialize_bob_session` at SPQR V1 needs below `stageP2bStack`. -/
@[expose] def p2BobV1StackExtra (sp : BitVec 64) : SepProp :=
  memRegion (sp - 768#64 - BitVec.ofNat 64 SpqrV1.Top.InitialState.initialStateStack) 0x700

theorem p2BobV1StackExtra_join (sp : BitVec 64) :
    stackAt sp (stageP2bStack + 0x700) = p2BobV1StackExtra sp ∗ stackAt sp stageP2bStack := by
  unfold p2BobV1StackExtra
  have ha : sp - BitVec.ofNat 64 (stageP2bStack + 0x700) =
      sp - 768#64 - BitVec.ofNat 64 SpqrV1.Top.InitialState.initialStateStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add,
      show stageP2bStack + 0x700 = 768 + SpqrV1.Top.InitialState.initialStateStack by decide]
  rw [ProofLib.stackAt_split_bottom sp stageP2bStack 0x700 (by decide), ha]

/-- Bob's 344-byte V1 `SessionState` at `outPtr`, its SPQR vec buffer, and its 7 heap boxes. -/
@[expose] def p2BobSessV1At (A : RustAlloc) (outPtr : BitVec 64) (inp : AcceptKeysInput)
    (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey) (pq : List (BitVec 8)) : SepProp :=
  ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64, ∃∗ rootKeyBoxPtr : BitVec 64,
  ∃∗ baseKeyBoxPtr : BitVec 64, ∃∗ ratchetPubBoxPtr : BitVec 64,
  ∃∗ ratchetPrivBoxPtr : BitVec 64, ∃∗ chainKeyBoxPtr : BitVec 64,
  ∃∗ spqrCap : BitVec 64, ∃∗ spqrBufPtr : BitVec 64, ∃∗ pad_f4 : BitVec 32,
  ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
  ∃∗ c4 : BitVec 64, ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
    ⌜localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧ baseKeyBoxPtr ≠ 0#64 ∧
      ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧ chainKeyBoxPtr ≠ 0#64⌝ ∗
    (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length) ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    p2BobSpqrVecBuf A spqrCap spqrBufPtr pq ∗
    (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
    (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
    (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
    (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
    (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
    (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
    (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1

theorem p2BobSessV1At_intro (A : RustAlloc) (outPtr : BitVec 64) (inp : AcceptKeysInput)
    (ikBPk spkBPk : SignalPqxdh.Bytes) (drKey : DRKey) (pq : List (BitVec 8))
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64) (pad_f4 : BitVec 32)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (h1 : localIkBoxPtr ≠ 0#64) (h2 : remoteIkBoxPtr ≠ 0#64) (h3 : rootKeyBoxPtr ≠ 0#64)
    (h4 : baseKeyBoxPtr ≠ 0#64) (h5 : ratchetPubBoxPtr ≠ 0#64) (h6 : ratchetPrivBoxPtr ≠ 0#64)
    (h7 : chainKeyBoxPtr ≠ 0#64) :
    (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
      spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length) ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    p2BobSpqrVecBuf A spqrCap spqrBufPtr pq ∗
    (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
    (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
      A.live remoteIkBoxPtr 33 1 ∗
    (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
    (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
      A.live baseKeyBoxPtr 33 1 ∗
    (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
      A.live ratchetPubBoxPtr 33 1 ∗
    (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
    (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ⊢
      p2BobSessV1At A outPtr inp ikBPk spkBPk drKey pq := by
  unfold p2BobSessV1At
  refine Entails.sepExists_right localIkBoxPtr (Entails.sepExists_right remoteIkBoxPtr
    (Entails.sepExists_right rootKeyBoxPtr (Entails.sepExists_right baseKeyBoxPtr
    (Entails.sepExists_right ratchetPubBoxPtr (Entails.sepExists_right ratchetPrivBoxPtr
    (Entails.sepExists_right chainKeyBoxPtr (Entails.sepExists_right spqrCap
    (Entails.sepExists_right spqrBufPtr (Entails.sepExists_right pad_f4
    (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right d0
    (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_)))))))))))))))))
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (Entails.refl _)

theorem p2_entails_frame_v1 {P P₁ P₂ F Q : SepProp} (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : P₂ ∗ F ⊢ Q) : P ⊢ Q := by
  rw [hP]
  exact Entails.trans (sepConj_mono_left hent) h

/-- Unpack `initBobErrAt (sp + 0x3e0)` into `((sp + 0x3e0) ↦₆₄ -1) ∗ speWordsAt (sp + 0x3e8) ... ∗
memRegion (sp + 0x418) 288`. -/
theorem p2_initBobErrAt_entails_speWordsAt (sp : BitVec 64) :
    initBobErrAt (sp + 0x3e0#64) ⊢
      ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ⌜errTag ≠ 0xfffffffffffffffe#64 ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
        memRegion (sp + 0x418#64) 288 := by
  refine Entails.trans (initBobErrAt_entails sp) ?_
  refine Entails.sepExists_elim fun errTag => ?_
  rw [sp3f0_328_split_5words sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
    Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
    (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  dsimp only [speWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem p2_stageP2bStack_le_bobV1 :
    stageP2bStack ≤ stageP2bStack + 0x700 :=
  Nat.le_add_right _ _

theorem p2_isSameAccount_le_bobV1 :
    isSameAccountDistinctStack ≤ stageP2bStack + 0x700 := by
  decide

theorem p2_isSameAccountExt_le_bobExt :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt ≤
      768 + Initiator.pqxdhEntryStackExt := by
  decide

theorem p2_bobErr4K_le_bobExt :
    768 + Initiator.pqxdhEntryStackExt ≤ 768 + Initiator.pqxdhEntryStackExt :=
  Nat.le_refl _

theorem isSameAccountDistinctSpec_to_at {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry (isSameAccountDistinctSpec A parse)) :
    subroutine_ok prog entry (isSameAccountDistinctAtSpec A parse isSameAccountDistinctStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [isSameAccountDistinctAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
             IsSameAccountDistinctGhost), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [isSameAccountDistinctSpec, isSameAccountDistinctAtSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩

theorem isSameAccountDistinctSpecExt_to_at {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse)) :
    subroutine_ok prog entry
      (isSameAccountDistinctAtSpec A parse
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt) :=
  h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
