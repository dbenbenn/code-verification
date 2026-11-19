/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveId
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Stage P4.4 Segments: `SessionStore::store_session` and `Ok(pt)` Exit

Basic-block `SepWP` segments (`+0x3cc → storeShim`, `+0x3e0 → storePoll`, `+0x3f8 → storeFutDrop`,
`+0x444 → dropSessionStructure3` / `+0x550`, `+0x48c → x30`) and vtable / representation helpers
for Substage P4.4 on `tripleRatchetProgAtExt img.base ext`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem stack_storeSession_to_alloc {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) allocHookStack
    (Nat.le_trans allocHookStack_le_errUnwind
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hn

theorem stack_storeSession_to_dropSS3 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) dropSessionStructureLocal2Stack
    (Nat.le_trans dropSS3Stack_le_errUnwind
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hn

/-- Unpack `storePollOutAt b p (.ok ())` into `pollCellsAt p (-2) ...`. -/
theorem storePollOk_eq_exists_pollCells (b p : BitVec 64) :
    storePollOutAt b p (.ok ()) =
      ∃∗ o1 : BitVec 32, ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        pollCellsAt p 0xfffffffffffffffe#64 o1 o2 o3 o4 o5 o6 := by
  dsimp only [storePollOutAt]
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

/-- Layout-independent unpack + repack of `storePollOutAt b p (.error ())` into `pollCellsAt`. -/
theorem storePollErr_unpack_repack (b p : BitVec 64) :
    storePollOutAt b p (.error ()) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
      ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32, ∃∗ H_err : SepProp,
        ⌜w0 = 0x800000000000001A#64 ∧
          (∀ outPtr : BitVec 64,
            pollCellsAt outPtr w0 o1 o2 o3 o4 o5 o6 ∗ H_err ⊢
              storePollOutAt b outPtr (.error ()))⌝ ∗
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ∗ H_err := by
  dsimp only [storePollOutAt]
  exact fiveWords_tail_unpack_repack p _ _ _ _ _ _ rfl

/-- Pure `Session` extra-field relation complementing `sessionStateAt` inside
`sessionStateReprAt`. -/
@[expose] def SessionExtraRel (G : SessionGhost) (ss : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending ss.pendingPreKey ∧
  KyberRel G.kyber ss.pendingKyberPreKey ∧
  G.alice.bytes = ss.aliceBaseKey ∧
  G.regIds.take 4 = leBytes 4 ss.remoteRegistrationId.toNat ∧
  (G.regIds.drop 4).take 4 = leBytes 4 ss.localRegistrationId.toNat

/-- Fold `sessionStateAt` + empty `previous_states` header into `sessionRecordAt` (`Some ss`). -/
theorem p4_sessionRecordAt_some_prev_of_state (A : RustAlloc) (r prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevPtr ≠ 0#64) (hExtra : SessionExtraRel G ss) :
    (r ↦₆₄ 0#64) ∗ ((r + 0x8#64) ↦₆₄ prevPtr) ∗ ((r + 0x10#64) ↦₆₄ 0#64) ∗
    sessionStateAt A (r + 0x18#64) G ss.state ⊢
    sessionRecordAt A r ⟨0#64, prevPtr, some G⟩ ⟨some ss⟩ := by
  unfold sessionRecordAt vecAt vecHeader vecBuf sessionStateReprAt
  have h10 : r + 16#64 = r + 0x10#64 := rfl
  have h8 : r + 8#64 = r + 0x8#64 := rfl
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h10, h8, h0, ↓reduceIte, sepConj_emp, emp_sepConj, List.length_nil, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.pure_right ⟨Nat.zero_le _, by decide, hprev_nz⟩ ?_
  exact Entails.pure_right hExtra (Entails.refl _)

/-- Unfold `sessionRecordAt` (`Some ss`) back into empty `previous_states` header + `sessionStateAt`. -/
theorem p4_sessionRecordAt_some_prev_to_state (A : RustAlloc) (r prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, prevPtr, some G⟩ ⟨some ss⟩ ⊢
    (r ↦₆₄ 0#64) ∗ ((r + 0x8#64) ↦₆₄ prevPtr) ∗ ((r + 0x10#64) ↦₆₄ 0#64) ∗
    sessionStateAt A (r + 0x18#64) G ss.state := by
  unfold sessionRecordAt vecAt vecHeader vecBuf sessionStateReprAt
  have h10 : r + 16#64 = r + 0x10#64 := rfl
  have h8 : r + 8#64 = r + 0x8#64 := rfl
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h10, h8, h0, ↓reduceIte, sepConj_emp, emp_sepConj, List.length_nil, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_left fun _ => Entails.pure_left fun _ => Entails.refl _)))

theorem sp370_36_split_eq' (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 =
      ∃∗ w_390 : BitVec 32, ∃∗ w_388 : BitVec 64, ∃∗ u_384 : BitVec 32,
      ∃∗ u_380 : BitVec 32, ∃∗ u_378 : BitVec 64, ∃∗ u_370 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u_370) ∗
        ((sp + 0x378#64) ↦₆₄ u_378) ∗
        ((sp + 0x380#64) ↦₃₂ u_380) ∗
        ((sp + 0x384#64) ↦₃₂ u_384) ∗
        ((sp + 0x388#64) ↦₆₄ w_388) ∗
        ((sp + 0x390#64) ↦₃₂ w_390) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 4) (k := 16)
        (b' := sp + 0x384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x384#64) (n := 4) (k := 12)
        (b' := sp + 0x388#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x388#64) (n := 8) (k := 4)
        (b' := sp + 0x390#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x370#64),
      ProofLib.memRegion_eight (sp + 0x378#64),
      ProofLib.memRegion_four (sp + 0x380#64),
      ProofLib.memRegion_four (sp + 0x384#64),
      ProofLib.memRegion_eight (sp + 0x388#64),
      ProofLib.memRegion_four (sp + 0x390#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pointsTo32_pair_sp380' (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0x380#64) ↦₃₂ lo) ∗ ((sp + 0x384#64) ↦₃₂ hi)) =
      ((sp + 0x380#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0x384#64 = (sp + 0x380#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair_eq]

theorem pointsTo32_pair_out1c' (outPtr : BitVec 64) (lo hi : BitVec 32) :
    ((outPtr + 0x1c#64) ↦₆₄ (hi ++ lo)) =
      (((outPtr + 0x1c#64) ↦₃₂ lo) ∗ ((outPtr + 0x20#64) ↦₃₂ hi)) := by
  have h : outPtr + 0x20#64 = (outPtr + 0x1c#64) + 4#64 := by bv_omega
  rw [h, ← pointsTo32_pair_eq]

theorem memRegion16_out20_fold' (outPtr w_24 : BitVec 64) (u_20 w_2c : BitVec 32) :
    ((outPtr + 0x20#64) ↦₃₂ u_20) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ⊢ memRegion (outPtr + 0x20#64) 16 := by
  rw [ProofLib.memRegion_split' (b := outPtr + 0x20#64) (n := 4) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))

/-- Fold the closure's `Ok(ptext)` sret cells and heap buffer into `vecResultAt A outPtr (.ok pt)`. -/
theorem p4_fold_decResultAt_ok (A : RustAlloc) (outPtr ptCap ptPtr : BitVec 64)
    (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
    memRegion (outPtr + 0x20#64) 16 ⊢
    vecResultAt A outPtr (.ok pt) := by
  have hhdr :
      ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) =
      vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) := by
    unfold vecHeader
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (words3_eq_head_mid_tail (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length)).symm
  have hbuf :
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
      (if ptCap = 0 then emp
       else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := by
    by_cases hcap : ptCap = 0#64
    · subst hcap
      have hnil : pt = [] := List.eq_nil_of_length_eq_zero (by simpa using hpt_le)
      subst hnil
      simp [pointsToBytes_nil, emp_sepConj]
    · have hcap0 : ptCap ≠ 0 := hcap
      simp only [hcap, hcap0, ↓reduceIte]
      ac_rfl
  dsimp only [vecResultAt]
  change _ ⊢ (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗ vecU8 A (outPtr + 0x8#64) pt ∗
    memRegion (outPtr + 0x20#64) 16
  have heq :
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32) ∗
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion (outPtr + 0x20#64) 16 =
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) ∗
      (if ptCap = 0 then emp
       else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion (outPtr + 0x20#64) 16 := calc
    _ = (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
        (((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
         ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
         ((outPtr + 0x14#64) ↦₆₄
           ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
         ((outPtr + 0x1c#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
        ((ptPtr ↦ₛ pt) ∗
         (if ptCap = 0#64 then emp
          else A.live ptPtr ptCap.toNat 1 ∗
            memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
        memRegion (outPtr + 0x20#64) 16 := by ac_rfl
    _ = (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
        vecHeader (outPtr + 0x8#64) ptCap ptPtr (BitVec.ofNat 64 pt.length) ∗
        (if ptCap = 0 then emp
         else A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt) ∗
           memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
        memRegion (outPtr + 0x20#64) 16 := by rw [hhdr, hbuf]
  refine Entails.trans (Entails.of_eq heq) ?_
  refine sepConj_mono_right ?_
  rw [← sepConj_assoc]
  refine sepConj_mono_left ?_
  unfold vecU8 vecU8At
  refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
  exact sepConj_mono_right (Entails.pure_right ⟨hpt_le, hcap_lt, hptr_nz⟩ (Entails.refl _))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
