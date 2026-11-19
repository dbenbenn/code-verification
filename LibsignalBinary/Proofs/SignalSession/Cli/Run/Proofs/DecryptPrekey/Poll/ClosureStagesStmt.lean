/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitFold -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Agree -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll Stage P2, P3, and P4 Interface Statements

Defines matched-session Path B Stage P4 spatial predicates (`stageP4MatchedPre`,
`stageP4MatchedExitAt`, `StageP4MatchedBranch`, `StageP4MatchedExtStmt`), shared post-`StageP1`
bundles at `+0x0868`, Path B and Path A Stage P2 contracts (`StageP2MatchedCliStmt`,
`StageP2PathACliStmt`), and the combined `ClosureStagesStmt` bundle.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Path B Stage P4 (`M4`) Spatial Entry/Exit & Three-Way Outcome (`StageP4MatchedBranch`) -/

/-- Unified stack budget for matched-session Path B Stage P4 (`save_identity` + `store_session` +
error unwinds; `mark_kyber_pre_key_used` and `remove_pre_key` are skipped). -/
@[expose] def stageP4MatchedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (storeSessionCallStack kit)

/-- Because `E2E.Record.encodeRecord ⟨none⟩ = []`, `Slots.loadRec Scope F peer =.ok opt` with
`opt.bind (·.currentSession) = none` forces `opt = none` (never `some ⟨none⟩`). -/
theorem opt_eq_none_of_loadRec_cur_none {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {opt : Option (SessionRecord (List (BitVec 8)))}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none) :
    opt = none := by
  cases opt with
  | none => rfl
  | some r =>
    have hr : r = ⟨none⟩ := by cases r; simpa using hcur
    subst hr
    unfold Slots.loadRec at hload
    rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
      _ | (_ | ⟨b, bs⟩) <;> rw [hget] at hload <;> dsimp only at hload
    · cases hload
    · cases hload
    · split at hload
      · rename_i hex
        simp only [Except.ok.injEq, Option.some.injEq] at hload
        have henc := (Classical.choose_spec hex).1
        have hnil : E2E.Record.encodeRecord (⟨none⟩ : SessionRecord (List (BitVec 8))) = [] := rfl
        rw [hload, hnil] at henc
        cases henc
      · cases hload

/-- Canonical coroutine + stack spatial bundle at `+0x0868` immediately after `StageP1OkExtStmt`,
shared by both Path B (`StageP2MatchedCliStmt`) and Path A (`StageP2PathACliStmt`). -/
@[expose] def stageP2PostP1At (A : RustAlloc)
    (coroPtr outPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr sessVt idStorePtr idVt
     preKeyStorePtr preKeyVt spkStorePtr spkVt
     kyberStorePtr kyberVt rngPtr
     sp v_a8 v_b8 v_d0 : BitVec 64) (s0 : State) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
  processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt
    spkStorePtr spkVt kyberStorePtr kyberVt ∗
  processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt
    spkStorePtr spkVt kyberStorePtr kyberVt ∗
  ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
  cells (coroPtr + 0x398#64) 2 ∗
  ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
  memRegion (coroPtr + 0x250#64) 48 ∗
  coroUnusedP1At coroPtr ∗
  (sp ↦₆₄ 0#64) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
  ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  closStackUnusedP1OkAt sp ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  A.pool

/-- Stack slots in `[sp.. sp + 0xc70)` framed untouched across Stage P3 (`+0x1778 → +0x34dc`)
and consumed by Stage P4 (`+0x34dc → x30`) and `clos_stack_3280_of_regions`. -/
@[expose] def stageP3StackFrameAt (sp remoteIkPtr remAddrPtr : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗
  spLowGapsAt sp ∗
  ((sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ remAddrPtr) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  memRegion (sp + 0x2b0#64) 192 ∗
  memRegion (sp + 0x394#64) 12 ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  memRegion (sp + 0x3ad#64) 27 ∗
  memRegion (sp + 0x538#64) 24 ∗
  spHighGapsAt sp

/-- Coroutine regions in `[coroPtr.. coroPtr + 2008)` framed untouched across Stage P3
(`+0x1778 → +0x34dc`) and consumed by Stage P4 (`+0x34dc → x30`) and `coro_regions_entails_dpFutDoneAt`. -/
@[expose] def stageP3CoroFrameAt
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr sessVt idStorePtr idVt
     preKeyStorePtr preKeyVt spkStorePtr spkVt
     kyberStorePtr kyberVt rngPtr : BitVec 64)
    (opkSlot coro2a0Slot : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  memRegion (coroPtr + 0x250#64) 48 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  coro2a0Slot ∗
  memRegion (coroPtr + 0x2ac#64) 8 ∗
  memRegion (coroPtr + 0x2b4#64) 12 ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  memRegion (coroPtr + 0x2d8#64) 184 ∗
  memRegion (coroPtr + 0x390#64) 1 ∗
  memRegion (coroPtr + 0x398#64) 16 ∗
  memRegion (coroPtr + 0x428#64) 64 ∗
  memRegion (coroPtr + 0x468#64) 40 ∗
  memRegion (coroPtr + 0x490#64) 32 ∗
  memRegion (coroPtr + 0x4f2#64) 1 ∗
  coroPostP2UnusedAt coroPtr

/-! ## 3. Path B Stage P2 Statement (`StageP2MatchedCliStmt`) -/

/-- Exact register state guaranteed by `StageP1OkExtStmt` at `+0x0868#64`. -/
@[expose] def StageP1PostRegs (s0 s1 : State) (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt : BitVec 64) : Prop :=
  s1.readReg64 .x8 = kyberStorePtr ∧
  s1.readReg64 .x9 = msgPtr ∧
  s1.readReg64 .x10 = kyberStoreVt ∧
  s1.readReg64 .x11 = preKeyStorePtr ∧
  s1.readReg64 .x12 = remoteAddrPtr ∧
  s1.readReg64 .x13 = preKeyStoreVt ∧
  s1.readReg64 .x14 = localAddrPtr ∧
  s1.readReg64 .x15 = idStorePtr ∧
  s1.readReg64 .x16 = idStoreVt ∧
  s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
  s1.readReg64 .x19 = coroPtr ∧
  s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
  s1.readReg64 .x22 = spkStorePtr ∧
  s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
  s1.readReg64 .x24 = spkStoreVt ∧
  s1.readReg64 .x25 = sp + 0x210#64 ∧
  s1.readReg64 .x28 = sp + 0xa90#64 ∧
  s1.readReg64 .x29 = s0.sp - 0x60#64 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
