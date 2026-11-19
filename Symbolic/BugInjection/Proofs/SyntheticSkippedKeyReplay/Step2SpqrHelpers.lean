/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2SpqrHelpersB

/-!
# Helper Congruence & Concrete Evaluation Lemmas for Alice SPQR Extraction
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

noncomputable section Step2Part2D

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.Composed
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
open ByteSpecs (hmacWith sha256With)
open _root_.Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

local macro "at?_localEncTr_tac" : tactic =>
  `(tactic| (dsimp only [localEncTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))


theorem p_c2_wire_eq_dag24 :
    p_c2.message.take (p_c2.message.length - 8) =
      DY.Libsignal.Refinement.trWireBytes cleanAddrBs DY.Libsignal.Refinement.canonicalVariation
        { version := DY.Libsignal.TripleRatchet.messageVersion.toNat,
          ratchetKey := dagBytes 73, counter := 1, previousCounter := 0,
          ciphertext := dagBytes 120 } (dagBytes 24) := by
  decide +kernel

theorem gamma_kdfRk_snd_congr {S : OpaqueSymbolSemantics} {g : Ghost}
    {rk₁ dh₁ rk₂ dh₂ : DY.Bytes}
    (hrk : gamma compI0 S g rk₁ = gamma compI0 S (gClean g) rk₂)
    (hdh : gamma compI0 S g dh₁ = gamma compI0 S (gClean g) dh₂) :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfRk rk₁ dh₁).2 =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.kdfRk rk₂ dh₂).2 := by
  have hlit_γ : ∀ ba : ByteArray,
      gamma compI0 S g (DY.Literal.literalToBytes ba) =
        gamma compI0 S (gClean g) (DY.Literal.literalToBytes ba) :=
    fun ba => congrArg ConcretizedTerm.bytes (gamma'_lit_eq_gClean S g ba).symm
  have hprk := gamma_hmac_congr_loc hrk hdh
  have hb1 : gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 (DY.Libsignal.TripleRatchet.hmac rk₁ dh₁) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")) =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.hkdfBlock1 (DY.Libsignal.TripleRatchet.hmac rk₂ dh₂) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock1
    exact gamma_hmac_congr_loc hprk (by simp only [gamma_concat_eq0, DY.Libsignal.TripleRatchet.lit, DY.Libsignal.TripleRatchet.litByte, hlit_γ])
  dsimp only [DY.Libsignal.TripleRatchet.kdfRk, DY.Libsignal.TripleRatchet.hkdfBlock2]
  refine gamma_hmac_congr_loc hprk ?_
  rw [gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0]
  dsimp only [DY.Libsignal.TripleRatchet.lit, DY.Libsignal.TripleRatchet.litByte]
  rw [hlit_γ, hlit_γ]
  exact congrArg (· ++ _) hb1

theorem gamma_trMsgKeys_congr {S : OpaqueSymbolSemantics} {g : Ghost}
    {s₁ sd₁ s₂ sd₂ : DY.Bytes}
    (hs : gamma compI0 S g s₁ = gamma compI0 S (gClean g) s₂)
    (hsd : gamma compI0 S g sd₁ = gamma compI0 S (gClean g) sd₂) :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).cipherKey =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).cipherKey ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).macKey =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).macKey ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).iv =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).iv := by
  have hlit_γ : ∀ ba : ByteArray,
      gamma compI0 S g (DY.Literal.literalToBytes ba) =
        gamma compI0 S (gClean g) (DY.Literal.literalToBytes ba) :=
    fun ba => congrArg ConcretizedTerm.bytes (gamma'_lit_eq_gClean S g ba).symm
  have hprk := gamma_hmac_congr_loc hs hsd
  have hck : gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).cipherKey =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).cipherKey := by
    dsimp only [DY.Libsignal.TripleRatchet.trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1]
    refine gamma_hmac_congr_loc hprk ?_
    rw [gamma_concat_eq0, gamma_concat_eq0]
    dsimp only [DY.Libsignal.TripleRatchet.lit, DY.Libsignal.TripleRatchet.litByte]
    rw [hlit_γ, hlit_γ]
  have hmk : gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).macKey =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).macKey := by
    have hck' := hck
    dsimp only [DY.Libsignal.TripleRatchet.trMsgKeys] at hck' ⊢
    unfold DY.Libsignal.TripleRatchet.hkdfBlock2
    refine gamma_hmac_congr_loc hprk ?_
    rw [gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0]
    dsimp only [DY.Libsignal.TripleRatchet.lit, DY.Libsignal.TripleRatchet.litByte]
    rw [hlit_γ, hlit_γ]
    exact congrArg (· ++ _) hck'
  have hiv : gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys s₁ sd₁).iv =
      gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.trMsgKeys s₂ sd₂).iv := by
    have hmk' := hmk
    dsimp only [DY.Libsignal.TripleRatchet.trMsgKeys] at hmk' ⊢
    unfold DY.Libsignal.TripleRatchet.hkdfBlock3
    refine gamma_hmac_congr_loc hprk ?_
    rw [gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0, gamma_concat_eq0]
    dsimp only [DY.Libsignal.TripleRatchet.lit, DY.Libsignal.TripleRatchet.litByte]
    rw [hlit_γ, hlit_γ]
    exact congrArg (· ++ _) hmk'
  exact ⟨hck, hmk, hiv⟩


theorem ev4_input_len_lt : ev4.input.length < 2 ^ 63 := by
  rw [ev4_input_eq_fast]; decide +kernel

theorem ev3_input_len_lt : ev3.input.length < 2 ^ 63 := by
  rw [ev3_input_eq_fast]; decide +kernel

theorem setupPublic_r0_6_eq_dag25 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hp : FitsPins r)
    (hpub : gamma compI0 S (gClean g) r.pqpkPubTerm = r.opaqueBytes (setupPublic r 6)) :
    gamma compI0 S (gClean g) pqpkBClean = dagBytes 25 := by
  unfold ProtocolSetup.pqpkPubTerm at hpub
  rw [hp.hpqpkPub, setupPublic_eq_of_fits hp 6, setupPublic_r0_6] at hpub
  exact hpub.trans (by decide +kernel)

theorem kyberPk_eq_dag25 : setup.kyberPk = dagBytes 25 := by decide +kernel
theorem setup_aliceId_eq_dag26 : setup.aliceId = dagBytes 26 := by decide +kernel
theorem setup_bobId_eq_dag29 : setup.bobId = dagBytes 29 := by decide +kernel
theorem setup_spk_eq_dag32 : setup.spk = dagBytes 32 := by decide +kernel
theorem fillFresh_11_eq_dag34 : fillFresh 11 64 = dagBytes 34 := by decide +kernel
theorem fillFresh_16_eq_dag35 : fillFresh 16 64 = dagBytes 35 := by decide +kernel
theorem fillFresh_17_eq_dag36 : fillFresh 17 64 = dagBytes 36 := by decide +kernel

theorem ev1_coins_take32 : List.take 32 ev1.coins = dagBytes 93 := by decide +kernel
theorem ev1_coins_take64 : List.take 64 ev1.coins = dagBytes 94 := by decide +kernel
theorem ev2_coins_take32 : List.take 32 ev2.coins = dagBytes 95 := by decide +kernel
theorem ev2_coins_take64 : List.take 64 ev2.coins = dagBytes 96 := by decide +kernel

theorem dagOp_21_lit : dagOp 21 = .lit (dagBytes 21) := dagOp_lit_eq rfl (by decide +kernel)
theorem dagOp_22_lit : dagOp 22 = .lit (dagBytes 22) := dagOp_lit_eq rfl (by decide +kernel)
theorem dagOp_23_lit : dagOp 23 = .lit (dagBytes 23) := dagOp_lit_eq rfl (by decide +kernel)
theorem dagOp_24_lit : dagOp 24 = .lit (dagBytes 24) := dagOp_lit_eq rfl (by decide +kernel)

theorem dagOp_105_eq_ev1 : dagOp 105 = .symEncPt 100 104 31 ev1.input :=
  congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel)

theorem ev1_input_len_lt8 : ev1.input.length < 8 := by decide +kernel

theorem dagOp_120_eq_ev2 : dagOp 120 = .symEncPt 115 119 38 ev2.input :=
  congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel)

theorem ev2_input_len_lt8 : ev2.input.length < 8 := by decide +kernel

theorem addr_ser_eq_cleanAddrBs :
    Cli.serializeAddresses ⟨Cli.aliceUuid, 1⟩ ⟨Cli.bobUuid, 1⟩ = cleanAddrBs := by
  decide +kernel

theorem dagBytes_22_ne_nil : dagBytes 22 ≠ [] := by decide +kernel
theorem dagBytes_24_ne_nil : dagBytes 24 ≠ [] := by decide +kernel

end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
