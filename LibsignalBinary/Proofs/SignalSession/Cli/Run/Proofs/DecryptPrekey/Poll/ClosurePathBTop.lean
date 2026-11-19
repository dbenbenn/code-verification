/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll Matched-Session Stage P4 Continuation and Exit Packagers

Provides common exit stack recombination (`exit_entails_dpPollPost`), `genP3S5PanicProp` panic
adapters, and matched-session Stage P4 continuations (`closure_pathB_p4_cont`,
`closure_pathB_p4_cont_of_stageP4`, and `closure_pathB_p4_cont_ext`) from `+0x34dc` to
`s0.readReg64 .x30`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
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

/-! ## 1. Common Exit Stack & Postcondition Packager -/

theorem stackAt_poll_exit_join (sp0 : BitVec 64) (B : RunBudgets) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    memRegion (sp0 - 0xcd0#64) 3280 ∗
      stackAt (sp0 - 0xcd0#64) (dpClosSubStack B) ∗
      memRegion (sp0 - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
    stackAt sp0 stk' := by
  rw [stackAt_poll_entry_split sp0 B stk' hneed hstk63]
  sep_frame

/-- Under `DecPkOk₀`, `me` and `peer` are opposite `Party` addresses (`P` vs `P.other`), hence
have distinct parsed UUID service IDs (`DistinctSid uuidTryParse`). -/
theorem distinctSid_of_decPkOk₀ {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm) :
    DistinctSid uuidTryParse me.name.bytes peer.name.bytes :=
  distinctSid_of_decPkOk hd

/-- Preserves `SessionExtraRel` across `CloneRel recG G₁` and `G₁.AfterTryDecrypt true G'` into the
cleared post-decrypt session `{ sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }`. -/
theorem sessionExtraRel_of_clone_decRel {recG G₁ G' : SessionGhost}
    {sess : Session (List (BitVec 8))} {st' : SessionState (List (BitVec 8))}
    (hex : SessionExtraRel recG sess)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec : G₁.AfterTryDecrypt true G') :
    SessionExtraRel G'
      { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } := by
  obtain ⟨_, _, halice, hrem4, hloc4⟩ := hex
  obtain ⟨_, _, halice1, hreg1⟩ := hcl
  obtain ⟨⟨_, _, halice', hreg'⟩, hp', hkp'⟩ := hdec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hp', PendingRel]
  · simp [hkp', KyberRel]
  · dsimp only; rw [halice', halice1, halice]
  · dsimp only; rw [hreg', hreg1, hrem4]
  · dsimp only; rw [hreg', hreg1, hloc4]

theorem dpClosSubStack_le_pow64 (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    dpClosSubStack B ≤ 2 ^ 64 := by
  have := dpPollNeed_eq_frame_add_subStack B
  omega

theorem stageP4MatchedStack_le_pow64 {b : BitVec 64} {F0 : FsFiles} {peer : AddrGhost}
    (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    stageP4MatchedCallStack
      (cliPollSessKit E2E.HooksE.A0 b F0 Slots.scopeKit peer (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 b F0 peer (cliKitStk B)) ≤ 2 ^ 64 :=
  Nat.le_trans
    (cliPollStageP4MatchedStack_le_subStack E2E.HooksE.A0 b F0 Slots.scopeKit peer B)
    (dpClosSubStack_le_pow64 B hneed hstk63)

/-! ## 2. Matched-Session Stage P4 Continuation (`+0x34dc → s0.readReg64 .x30`) -/

theorem stageP4MatchedStack_le_pow64_ext {A : RustAlloc} {b : BitVec 64}
    {F0 : FsFiles} {peer : AddrGhost}
    (B : RunBudgets) {stk' : Nat}
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    stageP4MatchedCallStack
      (cliPollSessKit A b F0 Slots.scopeKit peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B)) ≤ 2 ^ 64 :=
  Nat.le_trans
    (cliPollStageP4MatchedStack_le_subStack A b F0 Slots.scopeKit peer B)
    (dpClosSubStack_le_pow64 B hneed hstk63)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
