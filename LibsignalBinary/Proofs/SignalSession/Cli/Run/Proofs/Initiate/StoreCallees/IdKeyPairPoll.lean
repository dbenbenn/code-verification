/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# `IdentityFiles::get_identity_key_pair::{closure#0}` Poll Verification

Verifies `get_identity_key_pair::{closure#0}` against `idKeyPairPollSpec`, reading
`"identity-key-pair"` via `Dir::get` and decoding via `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace KpNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).trace = s.trace := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128)
    (w : RegWidth) (r : Reg) :
    (s.writeVReg128 idx v).readReg w r = s.readReg w r := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem pc_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem pstate_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).pstate = s.pstate := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem mem_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).mem = s.mem := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem status_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeVReg128_pre (s : State) (i j : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).readVReg128 j = if j == i then v else s.readVReg128 j := by
  cases s; simp [State.readVReg128, State.writeVReg128]

@[local arm64_norm ↓, local wp_norm ↓]
theorem speWord_one_eq : speWord 1 = asm64% speNicheBase + 1#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem okTagVec_eq_neg2 : okTagVec = -2#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_speWord1_two :
    (AddWithCarry64 (speWord 1) 2#64 false).2.z = false := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_okTagVec_two :
    (AddWithCarry64 okTagVec 2#64 false).2.z = true := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

end KpNorm

open KpNorm

/-! ## Symbolic Relative Offsets and `adrp` Lemma -/

private theorem close_panic_subgoal (s0 : State) {sf : State} {t : List TraceEvent} {F R : SepProp}
    (hm : sf.mem ⊨ ((⌜(allocFailedEvent ∈ List.drop t.length sf.trace) ∧ t <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R)
    (htr : t = s0.trace) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (F := F) ?_ (by simpa only [sepConj_assoc] using hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem utf8_read_len_eq : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  decide +kernel

/-! ## Frame and Layout Split/Join Helpers (`0xb0` = `176` B) -/

private theorem cells_22_kp (sp : BitVec 64) :
    cells (sp - 176#64) 22 =
      (∃∗ v0 : BitVec 64, (sp - 176#64) ↦₆₄ v0) ∗
      memRegion (sp - 168#64) 72 ∗
      memRegion (sp - 96#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  conv_lhs =>
    rw [show (22 : Nat) = 1 + 21 from rfl,
        ProofLib.cells_split_sub sp 176 168 1 21,
        show (21 : Nat) = 9 + 12 from rfl,
        ProofLib.cells_split_sub sp 168 96 9 12,
        show (12 : Nat) = 6 + 6 from rfl,
        ProofLib.cells_split_sub sp 96 48 6 6,
        show (6 : Nat) = 1 + 5 from rfl,
        ProofLib.cells_split_sub sp 48 40 1 5,
        show (5 : Nat) = 1 + 4 from rfl,
        ProofLib.cells_split_sub sp 40 32 1 4,
        show (4 : Nat) = 1 + 3 from rfl,
        ProofLib.cells_split_sub sp 32 24 1 3,
        show (3 : Nat) = 1 + 2 from rfl,
        ProofLib.cells_split_sub sp 24 16 1 2,
        show (2 : Nat) = 1 + 1 from rfl,
        ProofLib.cells_split_sub sp 16 8 1 1,
        ← ProofLib.memRegion_cells (sp - 168#64) 9 (by decide),
        ← ProofLib.memRegion_cells (sp - 96#64) 6 (by decide)]
  cells_unfold

private theorem getResultAt_err_sp_96 (A : RustAlloc) (sp : BitVec 64) :
    getResultAt A (sp - 96#64) (.error ()) =
      ∃∗ fnPtr : BitVec 64, ∃∗ sBs : List (BitVec 8), ∃∗ sCap : BitVec 64, ∃∗ sPtr : BitVec 64,
        ((sp - 96#64) ↦₆₄ speWord 1) ∗
        ((sp - 88#64) ↦₆₄ sCap) ∗ ((sp - 80#64) ↦₆₄ sPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 64#64) ↦₆₄ fnPtr) ∗ ((sp - 56#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") := by
  dsimp only [getResultAt, speAt, vecU8, strRefAt]
  simp_rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  rw [utf8_read_len_eq]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  have e40 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32, e40]

private theorem getResultAt_ok_sp_96 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 96#64) (.ok bs) =
      ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
        ⌜bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bPtr ≠ 0#64⌝ ∗
        ((sp - 96#64) ↦₆₄ okTagVec) ∗
        ((sp - 88#64) ↦₆₄ bCap) ∗ ((sp - 80#64) ↦₆₄ bPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bPtr ↦ₛ bs) ∗ Store.IdTrustPoll.Helpers.vecU8BufRest A bCap bPtr bs.length ∗
        memRegion (sp - 64#64) 16 := by
  dsimp only [getResultAt, vecResultAt, vecU8]
  simp_rw [Store.IdTrustPoll.Helpers.vecU8At_eq_expose]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32]
  congr 1; funext bCap; congr 1; funext bPtr
  ac_rfl

private theorem sp_96_cells4_fold_48 (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
      memRegion (sp - 64#64) 16 ⊢
    memRegion (sp - 96#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 40)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
        (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _)))))

private theorem sp_96_cells6_fold_48 (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
      ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢
    memRegion (sp - 96#64) 48 := by
  have h16 : ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢ memRegion (sp - 64#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
          (b' := sp - 56#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h16))))
    (sp_96_cells4_fold_48 sp w0 w1 w2 w3)

private theorem sp_168_err_split (sp : BitVec 64) :
    memRegion (sp - 168#64) 72 =
      (∃∗ b0 : BitVec 8, (sp - 168#64) ↦₈ b0) ∗
      memRegion (sp - 167#64) 7 ∗
      (∃∗ u0 : BitVec 64, (sp - 160#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp - 152#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (sp - 144#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (sp - 136#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (sp - 128#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp - 120#64) ↦₆₄ u5) ∗
      memRegion (sp - 112#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 168#64) (n := 1) (k := 71)
        (b' := sp - 167#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 167#64) (n := 7) (k := 64)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 56)
        (b' := sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 8) (k := 48)
        (b' := sp - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 40)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 32)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 24)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 168#64),
      ProofLib.memRegion_eight (sp - 160#64),
      ProofLib.memRegion_eight (sp - 152#64),
      ProofLib.memRegion_eight (sp - 144#64),
      ProofLib.memRegion_eight (sp - 136#64),
      ProofLib.memRegion_eight (sp - 128#64),
      ProofLib.memRegion_eight (sp - 120#64)]

private theorem sp_168_err_fold (A : RustAlloc) (sp sCap sPtr fnPtr : BitVec 64)
    (sBs : List (BitVec 8)) :
    ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
      ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
      ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
      (fnPtr ↦ᵣ utf8 "read") ∗
      memRegion (sp - 112#64) 16 ⊢
    idKeyPairOutAt A (sp - 168#64) (.error ()) := by
  dsimp only [idKeyPairOutAt]
  have e1 : sp - 168#64 + 1#64 = sp - 167#64 := by bv_omega
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e56 : sp - 168#64 + 0x38#64 = sp - 112#64 := by bv_omega
  rw [e1, e8, e56]
  have htop :
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗
        memRegion (sp - 112#64) 16 =
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        (((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
          ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
          ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read")) ∗
        memRegion (sp - 112#64) 16 := by
    ac_rfl
  rw [htop]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_ (Entails.refl _)))
  refine Entails.sepExists_right (.proto (utf8 "read") .invalidState) ?_
  dsimp only [RunDrop.speOwnedAt, speAt]
  have h40 : ((sp - 120#64) ↦₆₄ 4#64) =
      ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) := by
    rw [utf8_read_len_eq]
    have s40 : sp - 128#64 + 8#64 = sp - 120#64 := by bv_omega
    rw [s40]
  rw [h40]
  have s8 : sp - 160#64 + 8#64 = sp - 152#64 := by bv_omega
  have s32 : sp - 160#64 + 32#64 = sp - 128#64 := by bv_omega
  rw [s8, s32]
  have hvec :
      (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
        ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (sp - 152#64) bs := by
    have heq :
        (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs =
        vecU8At A (sp - 152#64) sCap sPtr sBs := by
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
      dsimp only [vecHeader]
      have v8 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
      have v16 : sp - 152#64 + 16#64 = sp - 136#64 := by bv_omega
      rw [v8, v16]
    rw [heq]
    exact Entails.sepExists_right sBs
      (Entails.sepExists_right sCap (Entails.sepExists_right sPtr (Entails.refl _)))
  have hstr :
      ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ⊢
      strRefAt (sp - 128#64) (utf8 "read") :=
    Entails.sepExists_right fnPtr (Entails.refl _)
  have hgrp :
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") =
      ((sp - 160#64) ↦₆₄ speWord 1) ∗
        ((((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs) ∗
        (((sp - 128#64) ↦₆₄ fnPtr) ∗
          ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
          (fnPtr ↦ᵣ utf8 "read")) := by
    ac_rfl
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (Entails.of_eq hgrp) ?_)
  exact sepConj_mono_right (sepConj_mono hvec hstr)

private theorem tryFrom_to_idKeyPairOutAt (A : RustAlloc) (p : BitVec 64)
    (r : Except SignalProtocolError IdentityKeyPair) :
    identityKeyPairResultAt A p r ⊢
      idKeyPairOutAt A p (match r with | .ok kp => .ok kp | .error _ => .error ()) := by
  cases r with
  | ok kp =>
    exact Entails.refl _
  | error e =>
    dsimp only [identityKeyPairResultAt, idKeyPairOutAt]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
    exact Entails.sepExists_right (.proto [] e) (Entails.refl _)

private theorem memRegion_72_eq_cells9 (p : BitVec 64) :
    memRegion p 72 =
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (p + 48#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (p + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (p + 64#64) ↦₆₄ w8) := by
  rw [memRegion_split p 8 64 (by decide),
    memRegion_split (p + 8#64) 8 56 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc]
  rfl

private theorem kp72_words_sp168 (sp out : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 72) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64),
      ((sp - 168#64) ↦ₛ bs) =
        ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗
        ((sp - 152#64) ↦₆₄ w2) ∗ ((sp - 144#64) ↦₆₄ w3) ∗
        ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
        ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗
        ((sp - 104#64) ↦₆₄ w8) ∧
      (out ↦ₛ bs) =
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗
        ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗
        ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
        ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗
        ((out + 64#64) ↦₆₄ w8) := by
  obtain ⟨q3, q0, q1, q2, w8, hforall⟩ := PollCommon.pointsToBytes72_split_qwords hlen
  refine ⟨q3.extractLsb' 0 64, q3.extractLsb' 64 64,
          q0.extractLsb' 0 64, q0.extractLsb' 64 64,
          q1.extractLsb' 0 64, q1.extractLsb' 64 64,
          q2.extractLsb' 0 64, q2.extractLsb' 64 64, w8, ?_, ?_⟩
  · rw [hforall (sp - 168#64)]
    unfold Arm64.pointsTo128
    have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
    have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
    have e24 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
    have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
    have e40 : sp - 136#64 + 8#64 = sp - 128#64 := by bv_omega
    have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
    have e56 : sp - 120#64 + 8#64 = sp - 112#64 := by bv_omega
    have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
    rw [e16, e32, e48, e64, e8, e24, e40, e56]
    ac_rfl
  · rw [hforall out]
    unfold Arm64.pointsTo128
    have o24 : out + 16#64 + 8#64 = out + 24#64 := by bv_omega
    have o40 : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
    have o56 : out + 48#64 + 8#64 = out + 56#64 := by bv_omega
    rw [o24, o40, o56]
    ac_rfl

private theorem kp72_words_fold_memRegion (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗
      ((sp - 152#64) ↦₆₄ w2) ∗ ((sp - 144#64) ↦₆₄ w3) ∗
      ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
      ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗
      ((sp - 104#64) ↦₆₄ w8) ⊢
    memRegion (sp - 168#64) 72 := by
  rw [memRegion_72_eq_cells9 (sp - 168#64)]
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
  have e24 : sp - 168#64 + 24#64 = sp - 144#64 := by bv_omega
  have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
  have e40 : sp - 168#64 + 40#64 = sp - 128#64 := by bv_omega
  have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
  have e56 : sp - 168#64 + 56#64 = sp - 112#64 := by bv_omega
  have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
  rw [e8, e16, e24, e32, e40, e48, e56, e64]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
          (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right w5 (Entails.refl _))
              (sepConj_mono (Entails.sepExists_right w6 (Entails.refl _))
                (sepConj_mono (Entails.sepExists_right w7 (Entails.refl _))
                  (Entails.sepExists_right w8 (Entails.refl _)))))))))

private def kpPostAns (A : RustAlloc) (out : BitVec 64)
    (expected : Except Unit IdentityKeyPair) (s0 sf : State) : SepProp :=
  ∃∗ ans : Except Unit IdentityKeyPair,
    ⌜ans = expected ∧ sf.trace = s0.trace⌝ ∗ idKeyPairOutAt A out ans

private theorem kpPostAns_intro (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 sf : State)
    (hB : idKeyPairOutAt A out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hpure : ans = expected ∧ sf.trace = s0.trace) :
    (out ↦ₛ bs) ∗ B bs ⊢ kpPostAns A out expected s0 sf := by
  have htrue : ((ans = expected ∧ sf.trace = s0.trace) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  have hlen_true : ((bs.length = 72) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hbs⟩
  unfold kpPostAns
  refine Entails.sepExists_right ans ?_
  rw [htrue, pure_true, emp_sepConj, hB]
  refine Entails.sepExists_right bs ?_
  rw [hlen_true, pure_true, emp_sepConj]
  exact Entails.refl _

private theorem focus_kpPostAns (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hB : idKeyPairOutAt A out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hf : P = ((out ↦ₛ bs) ∗ B bs) ∗ R)
    (hpure : ans = expected ∧ s_ret.trace = s0.trace)
    (hnext : SepWP prog ret_pc s_ret (kpPostAns A out expected s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken (kpPostAns_intro A out expected ans B bs s0 s_ret hB hbs hpure) (hf := hf) hnext

/-! ## Inner Specification and Symbolic Execution -/

abbrev kpCalleeStk (getStk : Nat) : Nat :=
  max (max getStk smallRootStack) extHookStack

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll
