/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Poll Trusted-Identity Branch

Proves `closure_trusted_ok` (and `Ext`-generalized `closure_trusted_of_stages_ext` /
`closure_trusted_ok_ext`): when `trusted = .ok true`, executes Stage P1 from entry to `+0x0868#64`,
folds the postcondition into `stageP2PostP1At`, and dispatches on `opt` to `closure_pathA_ok`
(`opt = none`) or `closure_pathB_ok` (`opt = some r`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust (trustCallStack)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- From `cliPollSessKit.loadRel StoresGhost.opened.sessions peer.val (.ok (some r))`, `r` satisfies
`Slots.scopeKit r` and `r ≠ ⟨none⟩`, hence `r.currentSession = some sess` for some `sess`. -/
theorem currentSession_some_of_cliPollSess_loadRel {A : RustAlloc} {b : BitVec 64}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {r : SessionRecord (List (BitVec 8))}
    (hload : (cliPollSessKit A b F0 Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r))) :
    ∃ sess : Session (List (BitVec 8)), r.currentSession = some sess := by
  obtain ⟨bs, _, hans⟩ := hload
  rcases bs with _ | ⟨x, xs⟩
  · cases hans
  · obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rcases hr_cur : r.currentSession with _ | sess
    · have hr_none : r = ⟨none⟩ := by cases r; simpa using hr_cur
      subst hr_none
      have hnil : E2E.Record.encodeRecord (⟨none⟩ : SessionRecord (List (BitVec 8))) = [] := rfl
      rw [hnil] at henc
      cases henc
    · exact ⟨sess, rfl⟩

/-- `trustUpdate` of `cliPollIdKit` is the identity on `ist`. -/
theorem cliPollId_trustUpdate_eq {A : RustAlloc} {b : BitVec 64}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    (ist : (cliPollIdKit A b F0 peer σ).IdState)
    (addr : AddrVal) (remoteIdKey : IdentityKey)
    (dir : CryptoGames.LibsignalSessionApi.Direction) (ans : Except Unit Bool) :
    (cliPollIdKit A b F0 peer σ).trustUpdate ist addr remoteIdKey dir ans = ist :=
  rfl

/-- Eliminate a leading `∃∗` quantifier in the precondition of `SepWPp`. -/
theorem sepWPp_sepExists_left {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Qpan : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qpan) :
    SepWPp prog ret s (∃∗ a, P a) Q Qpan := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hma⟩
  exact h a R hma hL

/-- Compose a Stage P1 `SepWPp` (`s0 → mid`) with a continuation `SepWPp` (`sm → ret`). -/
theorem sepWPp_bind_p1 {prog : Program} {mid ret : BitVec 64}
    {s0 : State} {P P_p1 F : SepProp}
    {Q1 : State → SepProp → Prop}
    {Q Qpan : State → SepProp → Prop}
    (hp1 : SepWPp prog mid s0 P_p1 Q1
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = P_p1 ∗ F)
    (hpan : ∀ sm P_m, Steps prog s0 sm →
      CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sm P_m → Qpan sm (P_m ∗ F))
    (hnext : ∀ sm P_m, Steps prog s0 sm → sm.pc = mid → sm.status = .Running →
      Q1 sm P_m → SepWPp prog ret sm (P_m ∗ F) Q Qpan) :
    SepWPp prog ret s0 P Q Qpan := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hq1⟩ | ⟨hpansm, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hp1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hsteps hpcm hrunm hq1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpansm, P_m ∗ F, hmm, hpan sm P_m hsteps hpanm⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
