/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpper
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers

/-!
# Stage 3 (`one-time-pre-key` Helpers, Error Exits, and Stack Copy) of Arm `R1b` (`0x12dc → 0x24ec`)
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_ownedBytes_cap0_emp (A : RustAlloc) (ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A 0#64 ptr len bs ⊢ emp := by
  rw [r1b_ownedBytes_borrow A 0#64 ptr len bs]
  apply Entails.pure_left
  rintro ⟨_, hle, _, _⟩
  have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
  subst hnil
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [pointsToBytes_nil, r1b_ownedRest, h0, ↓reduceIte, emp_sepConj]
  exact Entails.refl _

theorem r1b_memRegion7_to_head7 (d : BitVec 64) :
    memRegion d 7 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        Wire.sevenBytesHeadAt d b0 b1 b2 b3 b4 b5 b6 := by
  rw [r1b_head7_init d]
  refine Entails.sepExists_elim fun v0 => Entails.sepExists_elim fun d4 =>
    Entails.sepExists_elim fun d5 => Entails.sepExists_elim fun d6 => ?_
  have hv0 : v0 = v0.extractLsb' 24 8 ++ v0.extractLsb' 16 8 ++
      v0.extractLsb' 8 8 ++ v0.extractLsb' 0 8 := by bv_bits
  refine Entails.sepExists_right (v0.extractLsb' 0 8)
    (Entails.sepExists_right (v0.extractLsb' 8 8)
    (Entails.sepExists_right (v0.extractLsb' 16 8)
    (Entails.sepExists_right (v0.extractLsb' 24 8)
    (Entails.sepExists_right d4 (Entails.sepExists_right d5
    (Entails.sepExists_right d6 ?_))))))
  dsimp only [Wire.sevenBytesHeadAt]
  rw [← hv0]
  exact Entails.refl _

/-- Stage-1 `opk` scratch layout at `0x24dc` / `0x24ec` (uniform across `opk = none` and `opk = some`; `w0e0.truncate 8 = b8`, `w0e4.truncate 8 = b7`). -/
@[expose] def r1b_opkStage1At (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    memRegion (fsp + 0x0f0#64) 0x20 ∗
    memRegion (fsp + 0x1d0#64) 0x50 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0xf8 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

theorem r1b_opkStage1_of_regions (fsp : BitVec 64) :
    (memRegion fsp 0x110 ∗
      memRegion (fsp + 0x1d0#64) 0x90 ∗
      memRegion (fsp + 0x2c0#64) 0x210) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
      ∃∗ w0e0 : BitVec 32, ∃∗ w0e4 : BitVec 32,
      ∃∗ w9 : BitVec 32, ∃∗ w13 : BitVec 16,
      ∃∗ w15 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ b31 : BitVec 8,
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 := by
  have hlow : memRegion fsp 0x110 =
      memRegion fsp 0x0e0 ∗
        memRegion (fsp + 0x0e0#64) 4 ∗ memRegion (fsp + 0x0e4#64) 4 ∗
        memRegion (fsp + 0x0e8#64) 8 ∗ memRegion (fsp + 0x0f0#64) 0x20 := by
    rw [ProofLib.memRegion_split fsp 0x0e0 0x30 (by decide),
      r1b_split_region fsp 0x0e0 4 0x2c,
      r1b_split_region fsp 0x0e4 4 0x28,
      r1b_split_region fsp 0x0e8 8 0x20]
  have hmid : memRegion (fsp + 0x1d0#64) 0x90 =
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        memRegion (fsp + 0x220#64) 8 ∗ memRegion (fsp + 0x228#64) 1 ∗
        memRegion (fsp + 0x229#64) 0x37 := by
    rw [r1b_split_region fsp 0x1d0 0x50 0x40,
      r1b_split_region fsp 0x220 8 0x38,
      r1b_split_region fsp 0x228 1 0x37]
  have hhi : memRegion (fsp + 0x2c0#64) 0x210 =
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 := by
    rw [r1b_split_region fsp 0x2c0 0xf8 0x118,
      r1b_split_region fsp 0x3b8 7 0x111,
      r1b_split_region fsp 0x3bf 0x19 0xf8,
      r1b_split_region fsp 0x3d8 4 0xf4,
      r1b_split_region fsp 0x3dc 2 0xf2]
  rw [hlow, hmid, hhi,
    ProofLib.memRegion_four (fsp + 0x0e0#64),
    ProofLib.memRegion_four (fsp + 0x0e4#64),
    ProofLib.memRegion_eight (fsp + 0x0e8#64),
    ProofLib.memRegion_eight (fsp + 0x220#64),
    ProofLib.memRegion_one (fsp + 0x228#64),
    ProofLib.memRegion_four (fsp + 0x3d8#64),
    ProofLib.memRegion_two (fsp + 0x3dc#64)]
  refine Entails.trans
    (r1b_entails_frame (by r1b_ac) (r1b_memRegion7_to_head7 (fsp + 0x3b8#64)) (by r1b_ac)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w13 =>
    Entails.sepExists_elim fun w9 =>
    Entails.sepExists_elim fun b31 =>
    Entails.sepExists_elim fun w23 =>
    Entails.sepExists_elim fun w15 =>
    Entails.sepExists_elim fun w0e4 =>
    Entails.sepExists_elim fun w0e0 =>
    Entails.sepExists_elim fun b0 =>
    Entails.sepExists_elim fun b1 =>
    Entails.sepExists_elim fun b2 =>
    Entails.sepExists_elim fun b3 =>
    Entails.sepExists_elim fun b4 =>
    Entails.sepExists_elim fun b5 =>
    Entails.sepExists_elim fun b6 => ?_
  refine Entails.sepExists_right b0 (Entails.sepExists_right b1
    (Entails.sepExists_right b2 (Entails.sepExists_right b3
    (Entails.sepExists_right b4 (Entails.sepExists_right b5
    (Entails.sepExists_right b6 (Entails.sepExists_right w0e0
    (Entails.sepExists_right w0e4 (Entails.sepExists_right w9
    (Entails.sepExists_right w13 (Entails.sepExists_right w15
    (Entails.sepExists_right w23 (Entails.sepExists_right b31 ?_)))))))))))))
  dsimp only [r1b_opkStage1At]
  exact Entails.of_eq (by r1b_ac)

theorem r1b_opkStage1_to_regions (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
      memRegion fsp 0x110 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗
        memRegion (fsp + 0x2c0#64) 0x210 := by
  dsimp only [r1b_opkStage1At]
  have hlow : memRegion fsp 0x110 =
      memRegion fsp 0x0e0 ∗
        memRegion (fsp + 0x0e0#64) 4 ∗ memRegion (fsp + 0x0e4#64) 4 ∗
        memRegion (fsp + 0x0e8#64) 8 ∗ memRegion (fsp + 0x0f0#64) 0x20 := by
    rw [ProofLib.memRegion_split fsp 0x0e0 0x30 (by decide),
      r1b_split_region fsp 0x0e0 4 0x2c,
      r1b_split_region fsp 0x0e4 4 0x28,
      r1b_split_region fsp 0x0e8 8 0x20]
  have hmid : memRegion (fsp + 0x1d0#64) 0x90 =
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        memRegion (fsp + 0x220#64) 8 ∗ memRegion (fsp + 0x228#64) 1 ∗
        memRegion (fsp + 0x229#64) 0x37 := by
    rw [r1b_split_region fsp 0x1d0 0x50 0x40,
      r1b_split_region fsp 0x220 8 0x38,
      r1b_split_region fsp 0x228 1 0x37]
  have hhi : memRegion (fsp + 0x2c0#64) 0x210 =
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 := by
    rw [r1b_split_region fsp 0x2c0 0xf8 0x118,
      r1b_split_region fsp 0x3b8 7 0x111,
      r1b_split_region fsp 0x3bf 0x19 0xf8,
      r1b_split_region fsp 0x3d8 4 0xf4,
      r1b_split_region fsp 0x3dc 2 0xf2]
  have h1 :
      memRegion fsp 0x0e0 ∗
        ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
        ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ memRegion (fsp + 0x0f0#64) 0x20 ⊢
        memRegion fsp 0x110 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _))) (by r1b_ac)) ?_
    rw [hlow]; exact Entails.of_eq (by r1b_ac)
  have h2 :
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
        memRegion (fsp + 0x229#64) 0x37 ⊢
        memRegion (fsp + 0x1d0#64) 0x90 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (r1b_cell8_to_region _ _)) (by r1b_ac)) ?_
    rw [hmid]; exact Entails.of_eq (by r1b_ac)
  have h3 :
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
        memRegion (fsp + 0x3bf#64) 0x19 ∗
        ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
        memRegion (fsp + 0x3de#64) 0xf2 ⊢
        memRegion (fsp + 0x2c0#64) 0x210 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo16_entails_memRegion _ _))) (by r1b_ac)) ?_
    rw [hhi]; exact Entails.of_eq (by r1b_ac)
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono h1 (sepConj_mono h2 h3)) (by r1b_ac)

/-! ## Error Exits (`0x1b98 → 0x2adc`, `0x2420 → 0x2aa8`) -/

private theorem r1b_pk4d0_ok_to_region48 (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
      Wire.pkLayoutAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (fsp + 0x4f1#64) 15 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
  refine Entails.trans (sepConj_mono (r1b_cell8_to_region _ _)
    (sepConj_mono_left (Wire.pkLayoutAt_entails_memRegion32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))) ?_
  rw [r1b_join_region fsp 0x4d1 32 15, r1b_join_region fsp 0x4d0 1 47]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.RunCompose
