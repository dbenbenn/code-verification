/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4.2 Segments: `KyberPreKeyStore::mark_kyber_pre_key_used`

Basic-block `SepWP` segments (`+0x350 → markPoll`, `+0x180 → markFutDrop`, `+0x38c → removeShim` /
`+0x3cc` / `+0x550`) and vtable / poll-slot helpers for Substage P4.2 on
`tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Read-only `.rodata` vtable bundle for `kpkKit`'s `mark_kyber_pre_key_used` future. -/
@[expose] def markKyberVtablesAt {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) : SepProp :=
  ((b + kpkKit.markFutVtOff) ↦₆₄ᵣ (b + kpkKit.markFutDropOff)) ∗
  ((b + kpkKit.markFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.markBoxSize) ∗
  ((b + kpkKit.markFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + kpkKit.markFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kpkKit.markPollOff))

theorem speErrSpec_w0_ne_ok {E : Type} (S : SpeErrSpec E) (e : E) :
    S.w0 e + 2#64 ≠ 0#64 := by
  have h := S.w0_ne_ok e
  change S.w0 e ≠ 0xfffffffffffffffe#64 at h
  bv_omega

theorem speErrSpec_w0_ne_pend {E : Type} (S : SpeErrSpec E) (e : E) :
    S.w0 e + 3#64 ≠ 0#64 := by
  have h := S.w0_ne_pending e
  bv_omega

/-- Unpack `unitSpePollOutAt S p (.ok ())` (`kpkMarkPollOutAt` / `pkRemovePollOutAt`) into
`pollCellsAt p (-2) ...`. -/
theorem unitSpePollOk_eq_exists_pollCells {E : Type} (S : SpeErrSpec E) (p : BitVec 64) :
    unitSpePollOutAt S p (.ok ()) =
      ∃∗ o1 : BitVec 32, ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        pollCellsAt p 0xfffffffffffffffe#64 o1 o2 o3 o4 o5 o6 := by
  dsimp only [unitSpePollOutAt]
  change (p ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (p + 8#64) 40 = _
  rw [ProofLib.memRegion_split' (b := p + 8#64) (n := 4) (k := 36)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide),
      ← sepConj_assoc,
      ProofLib.memRegion_four (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o1 => ?_)
  rw [memRegion36_eq_exists_stagingCells (p + 0xc#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun o6 =>
    congrArg sepExists (funext fun o5 =>
    congrArg sepExists (funext fun o4 =>
    congrArg sepExists (funext fun o3 =>
    congrArg sepExists (funext fun o2 => ?_)))))
  unfold stagingCellsAt pollCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
