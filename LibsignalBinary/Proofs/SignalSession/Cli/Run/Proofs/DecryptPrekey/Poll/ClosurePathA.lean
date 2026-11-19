/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP3ExitFold -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll New-Session Path A Spatial and Exit Bridges

Allocator-parametric (`{A : RustAlloc}`) spatial and exit-packaging bridges for new-session Path A
(`opt = none` at `+0x0868`, `trusted = .ok true`), folding Stage P3 error exits and splitting the
Stage P3 `Ok` mid-state (`+0x34dc`) into 4-kit `Kits.stageP4Pre ∗ pathAP4RemAt`.
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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
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

/-! ## 1. Coroutine `opk_id` Collapse Helper -/

/-- Collapse `coroOpkIdAtP4 coroPtr opkId?` into `memRegion (coroPtr + 0x298#64) 8`. -/
theorem coroOpkIdAtP4_entails_memRegion8 (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) :
    coroOpkIdAtP4 coroPtr opkId? ⊢ memRegion (coroPtr + 0x298#64) 8 := by
  cases opkId? with
  | none =>
    unfold coroOpkIdAtP4
    exact Entails.sepExists_elim fun u => coro_298_words32_entails_memRegion8 coroPtr 0#32 u
  | some opkId =>
    exact coro_298_words32_entails_memRegion8 coroPtr 1#32 opkId

/-! ## 3. Spatial Split & Exit Fold for 4-Kit Stage P4 (`+0x34dc → x30`) on Path A -/

/-- When `pkStoreKeys F m = some k` and `m.opkId = some opkId`, `OneTimePreKeyFiles::remove_pre_key`
at `opkId` cannot fail with a read error (`removeRel... (.error e)` is uninhabited). -/
theorem cliPk_removeRel_not_err_of_pkStoreKeys {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    {pid opkId : BitVec 32} {σ : DpKitStk} {e : CliReadErr}
    (hk : pkStoreKeys F m = some k)
    (hopk : m.opkId = some opkId)
    (hrem : (cliPollPkKit A b F pid σ).removeRel StoresGhost.opened.oneTime opkId (.error e)) :
    False := by
  have hrem_err :
      (removePreKey cliIo.rd F StoresGhost.opened.oneTime opkId).1 = .error () := by
    simpa [cliPollPkKit, cliPreKeyStoreSpec] using hrem
  have hd_err :
      StoresGhost.opened.oneTime.get cliIo.rd F (keyName opkId) = .error () := by
    unfold removePreKey at hrem_err
    rcases hg : StoresGhost.opened.oneTime.get cliIo.rd F (keyName opkId) with _ | (_ | ⟨_, _⟩)
    · rfl
    · rw [hg] at hrem_err; cases hrem_err
    · rw [hg] at hrem_err; cases hrem_err
  have hget_err :
      getPreKey cliIo.rd F StoresGhost.opened.oneTime opkId = .error () := by
    unfold getPreKey
    rw [hd_err]
    rfl
  have hk_none : pkStoreKeys F m = none := by
    clear hk
    dsimp only [pkStoreKeys]
    rcases getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId with _ | sr <;>
      rcases StoresGhost.opened.kyber.get cliIo.rd F m.kpkId with _ | kr <;> try rfl
    dsimp only
    rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;>
      rcases pkVecTag? 8 1568 kr.signedPreKey.publicKey with _ | kpub <;>
      rcases pkVecTag? 8 3168 kr.signedPreKey.privateKey with _ | ksec <;> try rfl
    dsimp only
    rw [hopk]
    dsimp only
    rw [hget_err]
    rfl
  rw [hk_none] at hk
  cases hk

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
