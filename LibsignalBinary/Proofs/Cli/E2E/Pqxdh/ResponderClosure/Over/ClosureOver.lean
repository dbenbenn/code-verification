/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Top
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveEnc
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Responder Closure Over-Path Scope Bridges and Stage P3/P4 Instantiations

Defines the archived previous-session validity predicate `OverPrevEncOK`, proves `clearPending`
canonicality and `< 2 ^ 32` length bounds from `Cli.Slots.scopeIn`, and instantiates over-path
Stages P3 and P4 (`previous_sessions = [enc]`) for general `RustAlloc` and `E2E.HooksE.A0`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem_eq_of_canon)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession

/-! ## Archived Previous-Session Predicates and `clearPending` Scope Bridges -/

@[expose] def OverPrevEncOKAt (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))) : Prop :=
  enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

@[expose] def OverPrevEncOK (enc : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

@[expose] def prevArchived1AtD2c (A : RustAlloc) (coroPtr : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
    ⌜prevCap' ≠ 0#64⌝ ∗
    prevVecAt A (coroPtr + 0xe0#64) prevCap' prevPtr'
      [CryptoVerification.E2E.Record.Serialization.encSessionMem
        (clearPendingGhost recG) (clearPending sess)]

theorem encSessionMem_clearPending_eq {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : CanonSession G s) :
    CryptoVerification.E2E.Record.Serialization.encSessionMem
      (clearPendingGhost G) (clearPending s) =
      CryptoVerification.E2E.Record.encSession (clearPending s) :=
  encSessionMem_eq_of_canon _ _ (canonSession_clearPending h)

theorem scopeIn_clearPending {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) :
    Cli.Slots.scopeIn ⟨some (clearPending s)⟩ := by
  rcases h with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  refine ⟨⟨?_, ?_, ?_⟩, clearPending s, rfl, ?_⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    have hin0 := hin s rfl
    exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [clearPending] at hk⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    exact hpq s rfl
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
    exact ⟨hr1, hr2, rfl, hr4⟩
  · exact ⟨hss.1, fun p hp => by simp [clearPending] at hp,
      fun k hk => by simp [clearPending] at hk, hss.2.2.2⟩

theorem overPrevEncOK_clearPending_of_scopeIn {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) (hver : s.state.sessionVersion = 4#32) :
    OverPrevEncOK (CryptoVerification.E2E.Record.encSession (clearPending s)) :=
  ⟨clearPending s, rfl, Cli.Slots.scopeKit_of_scopeIn (scopeIn_clearPending h), hver, rfl, rfl⟩

theorem lenField2_clearPending_length_lt {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) :
    (CryptoVerification.E2E.Record.lenField 2
      (CryptoVerification.E2E.Record.encSession (clearPending s))).length <
      2 ^ 31 + 2 ^ 21 + 40 := by
  have hc : Cli.Slots.scopeIn ⟨some (clearPending s)⟩ := scopeIn_clearPending h
  have hb_strip : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩ := by
    apply CryptoVerification.E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    rcases hc with ⟨⟨hin, _hpq, hrepr⟩, s', hs', hss⟩
    injection hs' with hs_eq; subst hs_eq
    refine ⟨⟨?_, ?_, ?_⟩, Cli.Slots.PqValid.stripPq (clearPending s), rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hin0 := hin (clearPending s) rfl
      exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hk⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr (clearPending s) rfl
      exact ⟨hr1, hr2, rfl, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hp,
        fun k hk => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hk, hss.2.2.2⟩
  have h21 :
      (CryptoVerification.E2E.Record.encodeRecord
        ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩).length < 2 ^ 21 :=
    CryptoVerification.E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (CryptoVerification.E2E.Record.encSession
        (Cli.Slots.PqValid.stripPq (clearPending s))).length ≤
        (CryptoVerification.E2E.Record.encodeRecord
          ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩).length := by
    unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    dsimp only [Option.map_some]
    exact CryptoVerification.E2E.RecordX.lenField_length_ge' 1
      (CryptoVerification.E2E.Record.encSession (Cli.Slots.PqValid.stripPq (clearPending s)))
  have heq :
      (CryptoVerification.E2E.Record.encSession (clearPending s)).length =
        (CryptoVerification.E2E.Record.encSession
          (Cli.Slots.PqValid.stripPq (clearPending s))).length +
          (CryptoVerification.E2E.Record.bytesField 15
            (clearPending s).state.pqRatchetState).length := by
    simp only [CryptoVerification.E2E.Record.encSession, Cli.Slots.PqValid.stripPq,
      show (CryptoVerification.E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (CryptoVerification.E2E.Record.bytesField 15
        (clearPending s).state.pqRatchetState).length ≤
        (clearPending s).state.pqRatchetState.length + 20 :=
    CryptoVerification.E2E.RecordX.bytesField_length_le' 15 (clearPending s).state.pqRatchetState
  have hpq31 : (clearPending s).state.pqRatchetState.length < 2 ^ 31 :=
    (hc.1.2.1 (clearPending s) rfl).2
  have hlf2 :
      (CryptoVerification.E2E.Record.lenField 2
        (CryptoVerification.E2E.Record.encSession (clearPending s))).length ≤
        (CryptoVerification.E2E.Record.encSession (clearPending s)).length + 20 :=
    CryptoVerification.E2E.RecordX.lenField_length_le' 2
      (CryptoVerification.E2E.Record.encSession (clearPending s))
  omega

/-! ## Stage P3 (`Prev1`) Instantiations -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
