/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP3ExitFold -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll Matched-Session Path B Spatial and Exit Helpers

Spatial exit folds for Stage P3 `Err` / `verNe` exits and Stage P3 -> Stage P4 resource splitting
(`pathBP4RemAt`) on matched-session Path B (`opt = some ⟨some sess⟩`, `trusted = .ok true`).
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

/-! ## 1. Shared `slotOutTr` & `SepWPp` Continuation Helpers -/

theorem slotOutTr_of_reject {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    (g' : StoresGhost) {err : ApiError AddrVal Unit} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDef X W Scope)
    (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
    (hdec : decPkDef X W Scope F peer me pm coins = some none) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.error err) tr0 trf := by
  refine ⟨fun h => hne_p (Except.error.inj h), fun h => hne_s (Except.error.inj h), ?_⟩
  rw [hS, hdec]

theorem slotOutTr_of_accept {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDef X W Scope)
    (hdec : decPkDef X W Scope F peer me pm coins = some (some (g', pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.ok pt) tr0 trf := by
  refine ⟨nofun, nofun, ?_⟩
  rw [hS, hdec]
  exact ⟨rfl, hwr⟩

/-! ## 2. Spatial Fold for Stage P3 `Err` / `verNe` Exits on Path B -/

theorem coro_298_words32_entails_memRegion8 (coroPtr : BitVec 64) (u0 u1 : BitVec 32) :
    ((coroPtr + 0x298#64) ↦₃₂ u0) ∗ ((coroPtr + 0x29c#64) ↦₃₂ u1) ⊢
      memRegion (coroPtr + 0x298#64) 8 := by
  rw [memRegion_split (coroPtr + 0x298#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ u0) (pointsTo32_entails_memRegion _ u1)

theorem coro_2c8_16_184_eq_200 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2c8#64) 16 ∗ memRegion (coroPtr + 0x2d8#64) 184 =
      memRegion (coroPtr + 0x2c8#64) 200 := by
  rw [memRegion_split (coroPtr + 0x2c8#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
