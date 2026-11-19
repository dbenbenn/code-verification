/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6Aux

/-!
# Stage P2 Substage P2.6 at SPQR V1

Proves kit-parameterized Substage P2.6 (`+0x125c → +0x1778` on `Ok`, or `+0x09f4` Arm 6 on
`get_local_registration_id` error) for any 280-byte session middle `mid` (`mid.length = 280`) on
`tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

/-! ## 1. Stack Scratch (`sp + 0x3e0..0x538`) & Kit Precondition Helpers for P2.6 -/

/-- Six 64-bit words at `sp + 0x3e0..0x410` weaken to `memRegion (sp + 0x3e0) 48` for
`kitRegIdPollSpec`. -/
theorem p2_sp3e0_words6_entails_memRegion48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₆₄ w1) ∗
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗ ((sp + 0x3f8#64) ↦₆₄ w3) ∗
    ((sp + 0x400#64) ↦₆₄ w4) ∗ ((sp + 0x408#64) ↦₆₄ w5) ⊢
      memRegion (sp + 0x3e0#64) 48 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) w0)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e8#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) w3)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x400#64) w4)
      (pointsTo64_entails_memRegion (sp + 0x408#64) w5)))))
  have hm :
      memRegion (sp + 0x3e0#64) 8 ∗ (memRegion (sp + 0x3e8#64) 8 ∗
      (memRegion (sp + 0x3f0#64) 8 ∗ (memRegion (sp + 0x3f8#64) 8 ∗
      (memRegion (sp + 0x400#64) 8 ∗ memRegion (sp + 0x408#64) 8)))) =
      memRegion (sp + 0x3e0#64) 48 := by
    rw [(ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
          (b' := sp + 0x408#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 16)
          (b' := sp + 0x400#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
          (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 32)
          (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 40)
          (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide)).symm]
  exact hm ▸ h1

/-- `((sp + 0x410) ↦₆₄ w6) ∗ ((sp + 0x418) ↦ₛ ssRest)` (with `ssRest.length = 288`) weakens to
`memRegion (sp + 0x410) 296`. -/
theorem p2_sp410_word_bytes288_entails_memRegion296 (sp w6 : BitVec 64)
    (ssRest : List (BitVec 8)) (hlen : ssRest.length = 288) :
    ((sp + 0x410#64) ↦₆₄ w6) ∗ ((sp + 0x418#64) ↦ₛ ssRest) ⊢
      memRegion (sp + 0x410#64) 296 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x410#64) w6)
    (hlen ▸ ProofLib.pointsToBytes_entails_memRegion (sp + 0x418#64) ssRest)
  have hm : memRegion (sp + 0x410#64) 8 ∗ memRegion (sp + 0x418#64) 288 =
      memRegion (sp + 0x410#64) 296 :=
    (ProofLib.memRegion_split' (b := sp + 0x410#64) (n := 8) (k := 288)
      (b' := sp + 0x418#64) rfl (by bv_omega) (by decide)).symm
  exact hm ▸ h1

/-- Split the 36-byte trailing padding `memRegion (sp + 0x3ec) 36` of `regIdPollOutAt (.ok reg)`
into `(sp + 0x3ec ↦₃₂ u_3ec)` and four 64-bit words at `sp + 0x3f0..0x408` for `p2_seg6c_ext_wp`. -/
theorem p2_sp3ec_36_split_for_seg6c (sp : BitVec 64) :
    memRegion (sp + 0x3ec#64) 36 =
      ∃∗ u_3ec : BitVec 32, ∃∗ u_3f0 : BitVec 64, ∃∗ u_3f8 : BitVec 64,
      ∃∗ u_400 : BitVec 64, ∃∗ u_408 : BitVec 64,
        ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
        ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
        ((sp + 0x400#64) ↦₆₄ u_400) ∗ ((sp + 0x408#64) ↦₆₄ u_408) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 32)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 16)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight]
  simp only [sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

/-- Weaken the 48-byte `sp + 0x3e0..0x410` post-`seg6c` slot plus `memRegion (sp + 0x410) 296`
into `memRegion (sp + 0x3e0) 344`. -/
theorem p2_sp3e0_after_seg6c_entails_344 (sp w0 u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (reg u_3ec : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₃₂ reg) ∗ ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
    ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
    ((sp + 0x400#64) ↦₆₄ u_400) ∗ ((sp + 0x408#64) ↦₆₄ u_408) ∗
    memRegion (sp + 0x410#64) 296 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) w0)
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x3e8#64) reg)
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x3ec#64) u_3ec)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) u_3f0)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) u_3f8)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x400#64) u_400)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x408#64) u_408)
      (Entails.refl (memRegion (sp + 0x410#64) 296))))))))
  have hm :
      memRegion (sp + 0x3e0#64) 8 ∗ (memRegion (sp + 0x3e8#64) 4 ∗
      (memRegion (sp + 0x3ec#64) 4 ∗ (memRegion (sp + 0x3f0#64) 8 ∗
      (memRegion (sp + 0x3f8#64) 8 ∗ (memRegion (sp + 0x400#64) 8 ∗
      (memRegion (sp + 0x408#64) 8 ∗ memRegion (sp + 0x410#64) 296)))))) =
      memRegion (sp + 0x3e0#64) 344 := by
    rw [(ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296)
          (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304)
          (b' := sp + 0x408#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312)
          (b' := sp + 0x400#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320)
          (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 328)
          (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 332)
          (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336)
          (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide)).symm]
  exact hm ▸ h1

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_regIdShim_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.regIdShimStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_regIdPoll_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.regIdPollStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem p2_coro4f8_344_split_words7_288 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x4f8#64) 344 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x508#64) ↦₆₄ u2) ∗ ((coroPtr + 0x510#64) ↦₆₄ u3) ∗
        ((coroPtr + 0x518#64) ↦₆₄ u4) ∗ ((coroPtr + 0x520#64) ↦₆₄ u5) ∗
        ((coroPtr + 0x528#64) ↦₆₄ u6) ∗ memRegion (coroPtr + 0x530#64) 288 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 8) (k := 336)
        (b' := coroPtr + 0x500#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x500#64) (n := 8) (k := 328)
        (b' := coroPtr + 0x508#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x508#64) (n := 8) (k := 320)
        (b' := coroPtr + 0x510#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x510#64) (n := 8) (k := 312)
        (b' := coroPtr + 0x518#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x518#64) (n := 8) (k := 304)
        (b' := coroPtr + 0x520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x520#64) (n := 8) (k := 296)
        (b' := coroPtr + 0x528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x528#64) (n := 8) (k := 288)
        (b' := coroPtr + 0x530#64) rfl (by bv_omega) (by decide)]
  simp only [ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
