/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Sym
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

private theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (F := F) ?_ (by simpa only [sepConj_assoc] using hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem cells_26_split (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  ac_rfl

private theorem cells_sub_4_eq (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StorePollCli
