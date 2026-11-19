/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model

/-!
# Stage 3 PQXDH Helpers

Byte/cell lemmas, `S3InvPrefix`, reusable `s3_calc_agree` call combinators for
`calculate_agreement`, and shared zero-DH unwind collapses (`s3_dh_collapse_common`,
`s3_dh_unwind_1544`).
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## Byte and Cell Helpers -/

private theorem pack8_extract0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_bits
private theorem pack8_extract8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_bits
private theorem pack8_extract16 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_bits
private theorem pack8_extract24 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_bits
private theorem pack8_extract32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_bits
private theorem pack8_extract40 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_bits
private theorem pack8_extract48 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_bits
private theorem pack8_extract56 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_bits

private theorem bytes8_exists_cell64 {l : List (BitVec 8)} (hl : l.length = 8) :
    ∃ w : BitVec 64, ∀ p : BitVec 64, (p ↦ₛ l) = (p ↦₆₄ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl
  refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun p => ?_⟩
  unfold Arm64.pointsTo64
  rw [pack8_extract0, pack8_extract8, pack8_extract16, pack8_extract24,
      pack8_extract32, pack8_extract40, pack8_extract48, pack8_extract56,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_nil]
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

theorem bytes32_exists_cells4 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ p : BitVec 64,
      (p ↦ₛ bs) =
        (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) := by
  obtain ⟨w0, hw0⟩ := bytes8_exists_cell64 (l := bs.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := bytes8_exists_cell64 (l := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := bytes8_exists_cell64 (l := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := bytes8_exists_cell64 (l := bs.drop 24) (by simp [h])
  refine ⟨w0, w1, w2, w3, fun p => ?_⟩
  have hbs : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h1 := (List.take_append_drop 8 bs).symm
    have h2 := (List.take_append_drop 8 (bs.drop 8)).symm
    have h3 := (List.take_append_drop 8 (bs.drop 16)).symm
    simp only [Nat.reduceAdd, List.drop_drop] at h2 h3
    conv_lhs => rw [h1]; arg 2; rw [h2]; arg 2; rw [h3]
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      show (bs.take 8).length = 8 from by simp [h],
      show ((bs.drop 8).take 8).length = 8 from by simp [h],
      show ((bs.drop 16).take 8).length = 8 from by simp [h],
      hw0, hw1, hw2, hw3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem allOnes64_4_eq_F_X25519 (p : BitVec 64) :
    (p ↦₆₄ (-1#64)) ∗ ((p + 8#64) ↦₆₄ (-1#64)) ∗
      ((p + 16#64) ↦₆₄ (-1#64)) ∗ ((p + 24#64) ↦₆₄ (-1#64)) =
      (p ↦ₛ bytesToBv8 F_X25519) := by
  have h1 : ∀ q : BitVec 64, (q ↦₆₄ (-1#64)) = (q ↦ₛ List.replicate 8 0xff#8) := fun q => by
    unfold Arm64.pointsTo64
    dsimp only [List.replicate]
    rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
        pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
        pointsToBytes_nil]
    simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    rfl
  have hf : bytesToBv8 F_X25519 =
      List.replicate 8 0xff#8 ++ (List.replicate 8 0xff#8 ++
        (List.replicate 8 0xff#8 ++ List.replicate 8 0xff#8)) := rfl
  rw [hf, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, List.length_replicate]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← h1]

theorem memRegion32_cells4 (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3, (p + 24#64) ↦₆₄ w3) := by
  rw [← memRegion_merge_at p 8 24 (p + 8#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 16 (p + 16#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 16#64) 8 8 (p + 24#64) (by bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64), ProofLib.memRegion_eight (p + 24#64)]

theorem cells3_to_memRegion24 (p w0 w1 w2 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ⊢ memRegion p 24 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))) ?_
  rw [memRegion_merge_at (p + 8#64) 8 8 (p + 16#64) (by bv_omega) (by decide),
      memRegion_merge_at p 8 16 (p + 8#64) (by bv_omega) (by decide)]
  exact Entails.refl _

theorem append_bv8_at (p : BitVec 64) (xs ys : SignalPqxdh.Bytes) (k : BitVec 64)
    (hk : BitVec.ofNat 64 xs.length = k) :
    (p ↦ₛ bytesToBv8 xs) ∗ ((p + k) ↦ₛ bytesToBv8 ys) = (p ↦ₛ bytesToBv8 (xs ++ ys)) := by
  unfold bytesToBv8
  rw [List.map_append, pointsToBytes_append, List.length_map, hk]

theorem stage3KeySlotsAt_repack_dh1 (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗ ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗ ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]; ac_rfl

/-! ## Invariant Bundle, `calculate_agreement`, and Unwind Helpers -/

namespace Ext

theorem calcAgreeSubStk_le_frame {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    ResponderCore.calculateAgreementStackExt ≤ stk - cliInitiateFrame :=
  Nat.le_trans
    (by dsimp only [ResponderCore.calculateAgreementStackExt,
          ResponderCore.calculateAgreementSubStackExt, Initiator.pqxdhHookStackExt]; decide)
    (stk_sub_ge_base hstk)

theorem pqxdhEntryStk_le_frame {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) :
    Initiator.pqxdhEntryStackExt ≤ stk - cliInitiateFrame :=
  Nat.le_trans (by dsimp only [Initiator.pqxdhEntryStackExt]; decide) (stk_sub_ge_base hstk)

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

