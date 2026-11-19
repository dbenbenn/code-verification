/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Stage P2 Over-Path Substage P2.1 Outer `v4`

Proves `stageP2_over_sub1_v4_kits` and `stageP2_over_sub1_v4_kits_ext` (`+0x0868 → +0x0f14`, outer
`v4`) when `load_session` returned a populated 1-session record whose current session misses
(`PromoteMatchingMissAtProp`).
-/

public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

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

/-! ## Stack and Buffer Helpers -/

theorem p2_boxU8Buf_pk_serialize_entails (A : RustAlloc) (ptr : BitVec 64)
    (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  unfold boxU8Buf
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => Entails.refl _

theorem p2_serBytes_entails_memRegion33 (ptr : BitVec 64) (pk : PublicKey) :
    (ptr ↦ₛ pk.serialize) ⊢ memRegion ptr 33 := by
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  simpa only [hlen] using ProofLib.pointsToBytes_entails_memRegion ptr pk.serialize

theorem p2_sp3e0_16_rejoin (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
      memRegion (sp + 0x3e9#64) 7 ⊢
    memRegion (sp + 0x3e0#64) 16 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 8 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

theorem p2_sp3e0_24_split_16_8 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 24 =
      memRegion (sp + 0x3e0#64) 16 ∗ memRegion (sp + 0x3f0#64) 8 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 16 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem p2_sp3e0_24_rejoin (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
      memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 8 ⊢
    memRegion (sp + 0x3e0#64) 24 := by
  rw [p2_sp3e0_24_split_16_8]
  refine Entails.trans (Q :=
    (((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗ memRegion (sp + 0x3e9#64) 7) ∗
      memRegion (sp + 0x3f0#64) 8) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left (p2_sp3e0_16_rejoin sp w0 b8)

/-! ## Substage P2.1 Outer `v4` (`+0x0868 → +0x0f14`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
