/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCalls -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Vtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch

/-!
# Stage 5 Registration-ID Future Drop and Branch

Unpacks `idRegIdOutAt` into 6 sret words, drops and frees the 16-byte registration-ID future box
(`+0x14e4..+0x1630`), and branches at `+0x1634` (`cmn x26, #0x2`) between `stage5_err_cleanup_ok`
and `stage5_accept_ok`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Pure/spatial branch characterization of unpacked `idRegIdOutAt` words `rw0..rw5`. -/
@[expose] def regAnsBranchProp (A : RustAlloc) (retPtr : BitVec 64)
    (ans : Except Unit (BitVec 32)) (rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64) (SpeH : SepProp) : Prop :=
  match ans with
  | .ok reg => rw0 = 0xFFFFFFFFFFFFFFFE#64 ∧ rw1.setWidth 32 = reg ∧ SpeH = emp
  | .error () =>
    rw0 + 2#64 ≠ 0#64 ∧ ∃ k : RunDrop.SpeOwned,
      ((retPtr ↦₆₄ rw0) ∗ ((retPtr + 0x08#64) ↦₆₄ rw1) ∗ ((retPtr + 0x10#64) ↦₆₄ rw2) ∗
       ((retPtr + 0x18#64) ↦₆₄ rw3) ∗ ((retPtr + 0x20#64) ↦₆₄ rw4) ∗
       ((retPtr + 0x28#64) ↦₆₄ rw5) ∗ SpeH) ⊢ RunDrop.speOwnedAt A retPtr k

theorem unpack_idRegIdOutAt (A : RustAlloc) (fsp retPtr : BitVec 64)
    (ans : Except Unit (BitVec 32)) (R3 : SepProp) (m3 : Memory)
    (hm3 : m3 ⊨ idRegIdOutAt A (fsp + 0x1600#64) ans ∗ R3) :
    ∃ (rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64) (SpeH : SepProp),
      rw0 + 3#64 ≠ 0#64 ∧
      (m3 ⊨ ((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
            (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
            (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5) ∗
            (SpeH ∗ R3)) ∧
      regAnsBranchProp A retPtr ans rw0 rw1 rw2 rw3 rw4 rw5 SpeH := by
  cases ans with
  | ok reg =>
    dsimp only [idRegIdOutAt, regAnsBranchProp] at hm3 ⊢
    have hm4 : m3 ⊨ (((fsp + 0x1600#64) + 0x08#64) ↦₃₂ reg ∗
        memRegion ((fsp + 0x1600#64) + 0x0c#64) 36) ∗
        (((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ R3) :=
      sat_eq (by ac_rfl) hm3
    have hm5 := Satisfies.mono (sepConj_mono_left (u32_tail36_words5 (fsp + 0x1600#64) reg)) hm4
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm5
    obtain ⟨rw1, rw2, rw3, rw4, rw5, hm5⟩ := hm5
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm5
    obtain ⟨hrw1, hm5⟩ := hm5
    refine ⟨0xFFFFFFFFFFFFFFFE#64, rw1, rw2, rw3, rw4, rw5, emp, by decide, ?_, rfl, hrw1, rfl⟩
    exact sat_eq (by ac_rfl) hm5
  | error u =>
    cases u
    dsimp only [idRegIdOutAt, regAnsBranchProp] at hm3 ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm3
    obtain ⟨k, hm3⟩ := hm3
    obtain ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hne3, hne2, hmK, hfoldK⟩ :=
      speOwnedAt_words6 A (fsp + 0x1600#64) retPtr k R3 m3 hm3
    exact ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hne3, hmK, hne2, k, hfoldK⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
