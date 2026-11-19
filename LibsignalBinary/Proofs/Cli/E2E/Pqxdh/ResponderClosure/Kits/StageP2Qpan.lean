/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs

/-!
# Stage P2 Panic-Postcondition (`Qp`) Combinators

Polymorphic `{Qp : State → SepProp → Prop}` variants of the Stage P2 `SepWPp` sequencing and
subroutine-call combinators, lifting `(∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)` across stage
boundaries.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure

theorem p2_mono_panic {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp₁ Qp₂ : State → SepProp → Prop}
    (hpan : ∀ sf Pf, Qp₁ sf Pf → Qp₂ sf Pf)
    (h : SepWPp prog ret s P Q Qp₁) :
    SepWPp prog ret s P Q Qp₂ := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hp, P_f, hmf, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, P_f, hmf, hq⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hp, P_f, hmf, hpan sf P_f hqp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

theorem p2_cut_qpan {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (h : SepWPp prog mid s Pre (fun sm Pm => SepWPp prog ret sm Pm Q Qp) (PanicOomProp s0)) :
    SepWPp prog ret s Pre Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨hp, Pm, hmm, hqp⟩ | hoom⟩ := h R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ := hnext R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, Pm, hmm, hpan sm Pm hqp⟩)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem p2_bind_sepWPp_oom_frame_qpan {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, P_m ∗ F, hmm, hpan sm (P_m ∗ F) (fun R' hmR' => ?_)⟩)⟩
    rw [sepConj_assoc] at hmR'
    have h1 := hpanm (F ∗ R') hmR'
    rw [← sepConj_assoc] at h1
    exact allowPanic_frame id h1
  · exact (not_satisfies_false_sepConj hoom).elim

section InitBobErrOwned

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

/-- Owned heap payload of the `SignalProtocolError` returned by `pqxdhAccept` when
`Model.acceptKeys P inp = none`:
- `isStr = true`: tag 24 (`InvalidMessage`, `0x8000000000000018#64`) with heap `String` buffer at
  `(cap = w2, ptr = w3, len = w4)`,
- `isStr = false`: tag 10 (`InvalidKeyAgreement`, `0x800000000000000a#64`), plain payload. -/
@[expose] def pqxdhAcceptErrPayloadAt (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) : SepProp :=
  ∃∗ isStr : Bool,
    if isStr then
      ⌜errTag = 0x8000000000000018#64⌝ ∗
      ∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = w4 ∧ bs.length ≤ w2.toNat ∧ w2.toNat < 2 ^ 63 ∧ w3 ≠ 0#64⌝ ∗
        (if w2 = 0#64 then emp
         else A.live w3 w2.toNat 1 ∗ (w3 ↦ₛ bs) ∗
           memRegion (w3 + BitVec.ofNat 64 bs.length) (w2.toNat - bs.length))
    else ⌜errTag = 0x800000000000000a#64⌝

/-- Owned-payload refinement of `initBobErrAt` for the 344-byte
`Result<SessionState, SignalProtocolError>` sret slot `outPtr` of `initialize_bob_session`:
`Result::Err` discriminant (`-1`) at `outPtr`, 48-byte `SignalProtocolError` at `outPtr + 8#64`,
its `pqxdhAcceptErrPayloadAt`, and 288 trailing bytes at `outPtr + 56#64`. -/
@[expose] def initBobErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 288

end InitBobErrOwned

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

