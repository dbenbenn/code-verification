/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2TopPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3V3RejectPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Seed.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced

/-!
# `v4` Bad-KEM & Unified `pkToE? = none` Pre-Key Rejection

Defines the version-4 Bad-KEM message condition `MsgCondBadKem`, proves placed Stage-P2
entry unpacks and unified error-exit folds on Path A and Over-Path C, and combines `v3` and
`v4` Bad-KEM poll contracts into unified `pkToE? pm = none` slot rejection theorems.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding Bytes PqxdhHookContracts PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.Placed CryptoVerification.CliHandshake.RespClosurePlaced
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## 1. `v4` Bad-KEM Message Condition & Store-Kit Event Lemmas -/

theorem not_p2SessMatchesMsg_of_v4_badKem {sess : Session (List (BitVec 8))} {pm : PreKeySignalMessage}
    (kp : KyberPayload) (hv4 : pm.messageVersion = 4#8) (hnm : ¬ SessMatchesPm sess pm) :
    ¬ Over.SessMatchesMsg sess 4#8 (5#8 :: bytesToBv8 (mkBadKemHdr pm kp).ekAPk) := by
  rw [bytesToBv8_mkBadKemHdr_ekAPk]; change ¬ Over.SessMatchesMsg sess 4#8 pm.baseKey.serialize
  unfold Over.SessMatchesMsg SessMatchesPm at *; intro ⟨hver, hser⟩; exact hnm ⟨hv4.symm ▸ hver, hser⟩

/-- Version-4 Bad-KEM message condition: distinct service IDs (`¬ SameServiceId peer me`),
outer `messageVersion = 4`, a Kyber payload `kp` with `pkVecTag? 8 1568 kp.ciphertext = none`,
and no loaded active peer session matching `pm`. -/
@[expose] def MsgCondBadKem (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  ¬ RunProofs.SameServiceId peer me ∧ pm.messageVersion = 4#8 ∧
  (∃ kp : KyberPayload, pm.kyberPayload = some kp ∧ pkVecTag? 8#8 1568 kp.ciphertext = none) ∧
  ∀ r s, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = some s → ¬ SessMatchesPm s pm

theorem cliPollSpk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem cliPollKpk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {kid sid id : BitVec 32}
    {kbk : PublicKey} {σ : DpKitStk} (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem cliPollPk_getEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem cliPollPk_opkOkEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by cases opt <;> rfl

theorem cliPollPk_opkOkUpdate_eq (A : RustAlloc) [LibsignalPlacement] (F : FsFiles) (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk = StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem cliPollSelf_kpEvs_nil {A : RustAlloc} [LibsignalPlacement] {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem distinctSid_of_not_sameAcct_d3 {rem loc : AddrGhost} (hAcct : ¬ RunProofs.SameServiceId rem.val loc.val) :
    CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidTryParse loc.name.bytes rem.name.bytes :=
  fun sid hloc hrem => hAcct ⟨sid, hrem, hloc⟩

theorem stageP2OverV1CallStack_le_subStack_badKem_placed [LibsignalPlacement] {A : RustAlloc} (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B)) (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  Nat.max_le.mpr ⟨Poll.stageP2V1CallStack_le_subStack (A := A) 0#64 F0 peer spkId kpkId opkIdWord kbk B,
    Nat.le_trans (by decide : Over.stageP2OverPureAndErrStack ≤ 1048576 - 3280) (Nat.le_add_right _ _)⟩

/-! ## 2. Unified `pkToE? pm = none` Poll & Slot Combinators -/

/-! ## 3. Placed Stage P2 Spatial Entry Unpacks & Unified Error-Exit Fold -/

/-- Spatial frame preserved untouched across `stageP2_pathA_badKem_kits_*_placed` and `stageP2_over_badKem_kits_*_placed`. -/
@[expose] def badKemInnerFramePlaced [LibsignalPlacement] {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (kp : KyberPayload) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt (y.g.stores + 240#64) StoresGhost.opened.sessions ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 280#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗ memRegion (y.fut + 705#64) 7 ∗
  memRegion (y.fut + 913#64) 7 ∗ memRegion (y.fut + 1267#64) 5 ∗ memRegion (y.fut + 1922#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ∗ memRegion (sp + 216#64) 348 ∗ memRegion (sp + 592#64) 20 ∗ memRegion (sp + 633#64) 39 ∗
  memRegion (sp + 688#64) 36 ∗ memRegion (sp + 736#64) 36 ∗ memRegion (sp + 784#64) 36 ∗ memRegion (sp + 832#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗ signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  badKemMsgRemInnerAt y.g.msgG y.g.msgA y.g.msg kp

private theorem dup_pure_sepConj_right_d3 {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by ac_rfl

set_option maxHeartbeats 800000 in
/-! ## 4. Callee Transfers & Error-Word Helpers on `stageP1ProgPlaced` -/

theorem badKemSpeWords_entails_decResAt_anyHeap
    (A : RustAlloc) (out errTag w2 w3 w4 w5 w6 : BitVec 64)
    (err : ApiError AddrVal Unit) :
    speWordsAt out errTag w2 w3 w4 w5 w6 ∗
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ⊢
    decResAt A out (.error err) ∗ anyHeap := by
  unfold pqxdhBadKemErrPayloadAt
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun isStr => ?_
  cases isStr
  · simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun i => ?_
    rw [sepConj_comm]
    refine Entails.pure_left fun ⟨hi, htag⟩ => ?_
    subst htag
    exact Entails.trans
      (plainSpeWords_entails_decResAt_err A out i (show RunDrop.PlainSpeTag i from hi) w2 w3 w4 w5 w6 err)
      (entails_sepConj_anyHeap _)
  · simp only [↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (speWordsAt out errTag w2 w3 w4 w5 w6) ⌜errTag = speWord 24⌝,
        sepConj_assoc]
    refine Entails.pure_left fun htag => ?_
    subst htag
    have hstr := strSpeWords_entails_decResAt_anyHeap A out 24 (by decide) w2 w3 w4 w5 w6 emp err
    rwa [sepConj_emp] at hstr

end LibsignalBinary.Proofs.SignalSession.Cli.D3
