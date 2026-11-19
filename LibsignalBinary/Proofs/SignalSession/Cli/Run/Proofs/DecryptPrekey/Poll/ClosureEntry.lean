/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Poll Entry Unpacking and Stage P1/P3/P4 Frame Helpers

Unpacks `dpPollSpecState.inImage.pre` into pure invariants (`DpPollEntryPure` /
`DpPollEntryPureExt`) and spatial preconditions (`dpPollEntrySpatial` / `dpPollEntrySpatialExt`),
together with 3280-byte stack-splitting helpers and the `Ext`-generalized untrusted branch
`closure_untrusted_x_ext_ok`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure
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

/-- Untouched stack sub-regions of `memRegion sp 3280` for `StageP1OkExtStmt`. -/
@[expose] def closStackUnusedP1OkAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x8#64) 144 ∗
  memRegion (sp + 0x234#64) 428 ∗
  memRegion (sp + 0x550#64) 1824

/-- Split `memRegion (sp0 - 0xcd0#64) 3280` into the exact stack slots consumed by
`StageP1OkExtStmt` plus `closStackUnusedP1OkAt`. -/
theorem clos_stack_3280_split_for_p1_ok (sp0 : BitVec 64) :
    let sp := sp0 - 0xcd0#64
    memRegion sp 3280 =
      (∃∗ u_98 : BitVec 64, ∃∗ u_a0 : BitVec 64,
       ∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
       ∃∗ v_sp0 : BitVec 64,
        (sp ↦₆₄ v_sp0) ∗
        ((sp + 0x98#64) ↦₆₄ u_98) ∗
        ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
        ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
        ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp0 - 0x60#64) 12 ∗
        closStackUnusedP1OkAt sp) := by
  dsimp only
  let sp := sp0 - 0xcd0#64
  change memRegion sp 3280 = _
  rw [memRegion_split sp 8 3272 (by decide),
      memRegion_split (sp + 8#64) 144 3128 (by decide),
      memRegion_split (sp + 8#64 + 144#64) 64 3064 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64) 348 2716 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64) 428 2288 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64) 368 1920 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64 + 368#64) 1824 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h_c70 : sp + 0xc70#64 = sp0 - 0x60#64 := by dsimp only [sp]; bv_omega
  have h1 : memRegion sp 8 = (∃∗ v_sp0 : BitVec 64, sp ↦₆₄ v_sp0) := by
    rw [ProofLib.memRegion_cells sp 1 (by decide)]
    simp only [cells, sepConj_emp]
  have h8 : memRegion (sp + 0x98#64) 64 =
      (∃∗ u_98 : BitVec 64, ∃∗ u_a0 : BitVec 64,
       ∃∗ u_a8 : BitVec 64, ∃∗ u_b0 : BitVec 64, ∃∗ u_b8 : BitVec 64,
       ∃∗ u_c0 : BitVec 64, ∃∗ u_c8 : BitVec 64, ∃∗ u_d0 : BitVec 64,
        ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
        ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
        ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
        ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0)) := by
    rw [ProofLib.memRegion_cells (sp + 0x98#64) 8 (by decide)]
    simp only [cells_succ, cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_right]
  rw [h_c70, h1, h8,
      ProofLib.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  unfold closStackUnusedP1OkAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun u_98 => ?_)
  refine congrArg sepExists (funext fun u_a0 => ?_)
  refine congrArg sepExists (funext fun u_a8 => ?_)
  refine congrArg sepExists (funext fun u_b0 => ?_)
  refine congrArg sepExists (funext fun u_b8 => ?_)
  refine congrArg sepExists (funext fun u_c0 => ?_)
  refine congrArg sepExists (funext fun u_c8 => ?_)
  refine congrArg sepExists (funext fun u_d0 => ?_)
  refine congrArg sepExists (funext fun v_sp0 => ?_)
  dsimp only [sp]
  ac_rfl

/-- From `dpPollNeed B ≤ stk'` and `stk' ≤ s0.sp.toNat`, `(s0.sp - 0xcd0#64).toNat ≥ rootStack`
and `(s0.sp - 0xcd0#64).toNat ≥ dpClosSubStack B`. -/
theorem subStack_le_sp_of_dpPollNeed {B : RunBudgets} {stk' : Nat} {s0 : State}
    (hneed : dpPollNeed B ≤ stk') (hstk_sp : stk' ≤ s0.sp.toNat) :
    dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat ∧
      rootStack ≤ (s0.sp - 0xcd0#64).toNat := by
  have heq := dpPollNeed_eq_frame_add_subStack B
  have hroot := rootStack_le_subStack B
  have hsp_ge : 3280 ≤ s0.sp.toNat := by omega
  have hsub_toNat : (s0.sp - 0xcd0#64).toNat = s0.sp.toNat - 3280 := by
    have hlt := s0.sp.isLt
    bv_omega
  rw [hsub_toNat]
  omega

/-- Any `coroOpkIdAtP4 coroPtr opkId?` weakens to `memRegion (coroPtr + 0x298#64) 8` for exit
coroutine folding into `dpFutDoneAt`. -/
private theorem coroOpkIdAtP4_entails_memRegion8_entry (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) :
    coroOpkIdAtP4 coroPtr opkId? ⊢ memRegion (coroPtr + 0x298#64) 8 := by
  have hpair : ∀ lo hi : BitVec 32,
      ((coroPtr + 0x298#64) ↦₃₂ lo) ∗ ((coroPtr + 0x29c#64) ↦₃₂ hi) ⊢
        memRegion (coroPtr + 0x298#64) 8 := by
    intro lo hi
    rw [← coro298_split_eq coroPtr lo hi]
    exact ProofLib.pointsTo64_entails_memRegion _ _
  cases opkId? with
  | none =>
    dsimp only [coroOpkIdAtP4]
    exact Entails.sepExists_elim fun hi => hpair 0#32 hi
  | some opkId =>
    exact hpair 1#32 opkId

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

