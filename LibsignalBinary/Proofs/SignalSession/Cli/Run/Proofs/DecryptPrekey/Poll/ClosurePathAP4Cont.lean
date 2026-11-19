/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
import LibsignalBinary.Proofs.E2E.HooksE.Common
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
import Arm64.Trusted.Object.Labels
import ProofLib.BV
import ProofLib.BV.MaskLemmas
import ProofLib.BV.PolyMul
import ProofLib.Hoare.MultiCodeROHook
import ProofLib.MallocngBridge
import ProofLib.Placed
import ProofLib.Placed.LabelsCheck
import ProofLib.Placed.LabelsCoverage
import ProofLib.Placed.LabelsInterned
import ProofLib.Placed.SharedCode
import ProofLib.Process.FsLemmas
import ProofLib.SepLogic.LoopTactics
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.StdStartup.Layout
import ProofLib.StdStartup.MemOps
import ProofLib.StdStartup.OutlineAtomics
import ProofLib.StdStartup.Strlen
import VerifiedLibraries.Mallocng.Spec
import VerifiedLibraries.Musl.Spec.Top
import VerifiedLibraries.RustStd.Spec
import VerifiedLibraries.RustStd.Spec.AllocFormatInner
import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
import VerifiedLibraries.RustStd.Spec.AllocStringClone
import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
import VerifiedLibraries.RustStd.Spec.CoreMemrchr
import VerifiedLibraries.RustStd.Spec.FsRead
import VerifiedLibraries.RustStd.Spec.FsWrite
import VerifiedLibraries.RustStd.Spec.Stdio
import VerifiedLibraries.RustStd.Spec.TimeAdd
import VerifiedLibraries.RustStd.Spec.TimeDurationSince
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll New-Session Path A Stage P4 Continuation

Proves parameterized and fixed-table Stage P4 continuation theorems
(`closure_pathA_p4_cont_of_stageP4`, `closure_pathA_p4_cont_ext`, and `closure_pathA_p4_cont`) from
`+0x34dc` to `s0.readReg64 .x30` on new-session Path A (`opt.bind (·.currentSession) = none`,
`trusted = .ok true`).
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

theorem pmOfE_preKeyId_spkId_baseKey_eq (m : PreKeyMessageFields) (i : SignalMessage) :
    (pmOfE m i).preKeyId = m.opkId ∧
    (pmOfE m i).signedPreKeyId = m.spkId ∧
    (pmOfE m i).baseKey = ⟨m.baseKey⟩ := by
  have hf := pmOfE_fields m i
  exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩

theorem cliPollKpk_markOk_of_pmOfE {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (m : PreKeyMessageFields) (i : SignalMessage) {pm : PreKeySignalMessage}
    (σ : DpKitStk) (_hpm : pm = pmOfE m i) :
    (cliPollKpkKit A b F0 m.kpkId m.spkId pm.baseKey σ).markOk m.kpkId m.spkId pm.baseKey :=
  ⟨rfl, rfl, rfl⟩

theorem cliPollPk_removeIdOk_of_pmOfE {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (m : PreKeyMessageFields) (i : SignalMessage) {pm : PreKeySignalMessage}
    (σ : DpKitStk) (hpm : pm = pmOfE m i) :
    ∀ opkId, m.opkId = some opkId →
      (cliPollPkKit A b F0 (pmPreKeyId pm) σ).removeIdOk opkId := by
  intro opkId hopk
  subst hpm
  have hpre : (pmOfE m i).preKeyId = m.opkId := (pmOfE_fields m i).2.2.1
  dsimp only [cliPollPkKit, cliPreKeyStoreSpec, pmPreKeyId]
  rw [hpre, hopk]
  rfl

theorem pathA_recOk_of_tryDecrypt {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    Slots.scopeKit ⟨some ses'⟩ ∧ (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
  have hok_pair : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk) with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st']; rw [hg]
    subst hr2
    rfl
  have htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq hd hver, hok_pair]
  exact tryDecryptFromRecord_preKey_recOk_of_scopeIn
    (pathAInitSession_scopeIn W meE k m dk).1 htry

/-! ## 1. `TraceFsSound` Exit/FS Helpers, `StageP4PathAV1ExtAt`, & `PollPathACallees` -/

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
