/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ExternWitness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs -- proof-setup: allow-public-import

/-!
# Symbolic CLI Extern Witness Satisfying the Real `libcrux_ml_kem` Equations (`MlKemExternWitness`)

Upgrades `Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ExternWitness` (`cliWitnessInterp`,
`cliWitnessHooks`, `comp_externsSatisfiable_cli`) so that the witness simultaneously satisfies:
1. `ExternInterpretationTotalOnUsedSymbols cliWitnessInterpMlKem`
2. `ExternContractsHoldCli cliWitnessInterpMlKem`
3. `HooksMatchInterpretation cliWitnessInterpMlKem cliWitnessHooksMlKem`
4. All three interim-headline `W.Q` equations:
   - `cliWitnessHooksMlKem.Q.encaps = kyber1024EncapsVec`
   - `cliWitnessHooksMlKem.Q.decaps = kyber1024DecapsVec`
   - `cliWitnessHooksMlKem.Q.K = mlkem768Incremental`

Because `ExternContractsHoldCli` (`ExternCryptoLawsHold`, `PubCanonical`, and the X25519 torsion
exclusion) inspects only X25519, AES-256-CBC, and HMAC symbols (none of which is
`kyberEncapsSymbol` or `kyberDecapsSymbol`), overriding `cliWitnessInterp` on `kyberEncapsSymbol`
and `kyberDecapsSymbol` with `kyber1024EncapsVec` / `kyber1024DecapsVec` preserves all symbolic
contracts while matching the real ML-KEM-1024 / ML-KEM-768 functions.
-/

set_option autoImplicit false

public section

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.MlKemExternWitness

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open CryptoVerification.SignalSession (CliHooks)
open DY.Libsignal.Composed.Refinement (ExternInterpretationTotalOnUsedSymbols ReturnsLength)
open DY.Libsignal.Composed.Refinement.Cli (
  CompExternsSatisfiableCli ExternContractsHoldCli HooksMatchInterpretation
)
open DY.Libsignal.PQXDH.Refinement (kyberDecapsSymbol kyberEncapsSymbol)
open DY.Libsignal.Refinement (
  ExternCryptoLawsHold aesCbcDecryptSymbol aesCbcEncryptSymbol sha256CompressFunction
  sha256CompressSymbol torsionShift x25519AgreementSymbol x25519PublicKeySymbol x25519TorsionSymbol
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec kyber1024EncapsVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli (
  cliWitnessHooks cliWitnessHooks_agree cliWitnessInterp cliWitnessInterp_contracts
  cliWitnessInterp_cryptoEquationsHold cliWitnessInterp_total
)

attribute [local irreducible] kyber1024EncapsVec kyber1024DecapsVec mlkem768Incremental

/-! ## 1. `cliWitnessInterpMlKem` & Symbol-Disjointness Lemmas -/

/-- `ExternInterpretation` realizing `kyberEncapsSymbol` and `kyberDecapsSymbol` via the verified
    `libcrux_ml_kem` functions `kyber1024EncapsVec` and `kyber1024DecapsVec` on well-sized byte
    slices (with constant-length zero fallback on ill-sized slices for totality), and delegating all
    other extern symbols to `cliWitnessInterp`. -/
noncomputable def cliWitnessInterpMlKem : ExternInterpretation :=
  fun s args =>
    if s = kyberEncapsSymbol then
      match args with
      | [pk, rand] =>
        if hpk : pk.length = 1568 then
          if hr : rand.length = 32 then
            let out := kyber1024EncapsVec ⟨pk, hpk⟩ ⟨rand, hr⟩
            some (out.1.toList ++ out.2.toList)
          else
            some (List.replicate 1600 0#8)
        else
          some (List.replicate 1600 0#8)
      | _ => some (List.replicate 1600 0#8)
    else if s = kyberDecapsSymbol then
      match args with
      | [sk, ct] =>
        if hsk : sk.length = 3168 then
          if hct : ct.length = 1568 then
            some (kyber1024DecapsVec ⟨sk, hsk⟩ ⟨ct, hct⟩).toList
          else
            some (List.replicate 32 0#8)
        else
          some (List.replicate 32 0#8)
      | _ => some (List.replicate 32 0#8)
    else
      cliWitnessInterp s args

private theorem cliWitnessInterpMlKem_other {s : String}
    (he : s ≠ kyberEncapsSymbol) (hd : s ≠ kyberDecapsSymbol) :
    cliWitnessInterpMlKem s = cliWitnessInterp s := by
  funext args
  simp [cliWitnessInterpMlKem, he, hd]

theorem sha256CompressFunction_cliWitnessInterpMlKem :
    sha256CompressFunction cliWitnessInterpMlKem = sha256CompressFunction cliWitnessInterp := by
  unfold sha256CompressFunction
  rw [cliWitnessInterpMlKem_other (by decide) (by decide)]

/-! ## 2. Totality (`ExternInterpretationTotalOnUsedSymbols`) & Contracts (`ExternContractsHoldCli`) -/

private theorem cliWitnessInterpMlKem_kyberEncaps_returns1600 (args : List ByteString) :
    ReturnsLength cliWitnessInterpMlKem kyberEncapsSymbol args 1600 := by
  unfold ReturnsLength cliWitnessInterpMlKem
  simp only [↓reduceIte]
  rcases args with _ | ⟨pk, _ | ⟨rand, _ | _⟩⟩
  · exact ⟨_, rfl, List.length_replicate⟩
  · exact ⟨_, rfl, List.length_replicate⟩
  · by_cases hpk : pk.length = 1568
    · by_cases hr : rand.length = 32
      · simp only [hpk, hr, ↓reduceDIte]
        refine ⟨_, rfl, ?_⟩
        rw [List.length_append, List.Vector.toList_length, List.Vector.toList_length]
      · simp only [hpk, hr, ↓reduceDIte]
        exact ⟨_, rfl, List.length_replicate⟩
    · simp only [hpk, ↓reduceDIte]
      exact ⟨_, rfl, List.length_replicate⟩
  · exact ⟨_, rfl, List.length_replicate⟩

private theorem cliWitnessInterpMlKem_kyberDecaps_returns32 (args : List ByteString) :
    ReturnsLength cliWitnessInterpMlKem kyberDecapsSymbol args 32 := by
  unfold ReturnsLength cliWitnessInterpMlKem
  have hne : kyberDecapsSymbol ≠ kyberEncapsSymbol := by decide
  simp only [hne, ↓reduceIte]
  rcases args with _ | ⟨sk, _ | ⟨ct, _ | _⟩⟩
  · exact ⟨_, rfl, List.length_replicate⟩
  · exact ⟨_, rfl, List.length_replicate⟩
  · by_cases hsk : sk.length = 3168
    · by_cases hct : ct.length = 1568
      · simp only [hsk, hct, ↓reduceDIte]
        exact ⟨_, rfl, List.Vector.toList_length _⟩
      · simp only [hsk, hct, ↓reduceDIte]
        exact ⟨_, rfl, List.length_replicate⟩
    · simp only [hsk, ↓reduceDIte]
      exact ⟨_, rfl, List.length_replicate⟩
  · exact ⟨_, rfl, List.length_replicate⟩

theorem cliWitnessInterpMlKem_total :
    ExternInterpretationTotalOnUsedSymbols cliWitnessInterpMlKem := by
  have htot := cliWitnessInterp_total
  refine
    ⟨fun pk rand _ _ => cliWitnessInterpMlKem_kyberEncaps_returns1600 [pk, rand],
     fun sk ct _ _ => cliWitnessInterpMlKem_kyberDecaps_returns32 [sk, ct],
     fun st blk hs hb => ?_,
     fun seed hs => ?_,
     fun pk1 rand hr => ?_,
     fun st pk2 hst hpk2 => ?_,
     fun sk ct1 ct2 hsk hc1 hc2 => ?_,
     fun pk1 pk2 => ?_,
     fun k d hk hd => ?_⟩
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.1 st blk hs hb
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.1 seed hs
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.2.1 pk1 rand hr
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.2.2.1 st pk2 hst hpk2
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.2.2.2.1 sk ct1 ct2 hsk hc1 hc2
  · rw [cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.2.2.2.2.1 pk1 pk2
  · rw [ReturnsLength, cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact htot.2.2.2.2.2.2.2.2 k d hk hd

theorem cliWitnessInterpMlKem_cryptoEquationsHold :
    ExternCryptoLawsHold cliWitnessInterpMlKem := by
  have ha : cliWitnessInterpMlKem x25519AgreementSymbol =
      cliWitnessInterp x25519AgreementSymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have hp : cliWitnessInterpMlKem x25519PublicKeySymbol =
      cliWitnessInterp x25519PublicKeySymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have ht : cliWitnessInterpMlKem x25519TorsionSymbol =
      cliWitnessInterp x25519TorsionSymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have henc : cliWitnessInterpMlKem aesCbcEncryptSymbol =
      cliWitnessInterp aesCbcEncryptSymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have hdec : cliWitnessInterpMlKem aesCbcDecryptSymbol =
      cliWitnessInterp aesCbcDecryptSymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have hhmac : cliWitnessInterpMlKem "libcrux_hmac::hmac" =
      cliWitnessInterp "libcrux_hmac::hmac" :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have hts : ∀ p t, torsionShift cliWitnessInterpMlKem p t =
      torsionShift cliWitnessInterp p t := fun p t => by
    unfold torsionShift; rw [ht]
  have hwEq := cliWitnessInterp_cryptoEquationsHold
  exact
    { x25519_agreement_commutes := fun a b => by
        simpa only [ha, hp] using hwEq.x25519_agreement_commutes a b
      x25519_agreement_length := fun a p => by
        simpa only [ha] using hwEq.x25519_agreement_length a p
      x25519_public_key_length := fun a => by
        simpa only [hp] using hwEq.x25519_public_key_length a
      x25519_agreement_reads_u_coordinate := fun a b b' hb hb' hu => by
        simpa only [ha] using hwEq.x25519_agreement_reads_u_coordinate a b b' hb hb' hu
      x25519_agreement_torsion_invariant := fun a p t => by
        simpa only [ha, hts] using hwEq.x25519_agreement_torsion_invariant a p t
      x25519_agreement_zero_iff_low_order := fun a b ha32 hb32 => by
        simpa only [ha] using hwEq.x25519_agreement_zero_iff_low_order a b ha32 hb32
      x25519_public_key_not_low_order := fun a ha32 => by
        simpa only [hp] using hwEq.x25519_public_key_not_low_order a ha32
      aes_cbc_decrypt_inverts_encrypt := fun pt k iv => by
        simpa only [henc, hdec] using hwEq.aes_cbc_decrypt_inverts_encrypt pt k iv
      aes_cbc_encrypt_of_decrypt := fun c k iv p hk hiv hd => by
        rw [hdec] at hd
        rw [henc]
        exact hwEq.aes_cbc_encrypt_of_decrypt c k iv p hk hiv hd
      hmac_tag_length := fun k d tag h => by
        rw [hhmac] at h
        exact hwEq.hmac_tag_length k d tag h }

theorem cliWitnessInterpMlKem_contracts : ExternContractsHoldCli cliWitnessInterpMlKem := by
  have hc := cliWitnessInterp_contracts
  have hp : cliWitnessInterpMlKem x25519PublicKeySymbol =
      cliWitnessInterp x25519PublicKeySymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have ht : cliWitnessInterpMlKem x25519TorsionSymbol =
      cliWitnessInterp x25519TorsionSymbol :=
    cliWitnessInterpMlKem_other (by decide) (by decide)
  have hts : ∀ p t, torsionShift cliWitnessInterpMlKem p t =
      torsionShift cliWitnessInterp p t := fun p t => by
    unfold torsionShift; rw [ht]
  refine ⟨cliWitnessInterpMlKem_cryptoEquationsHold, ?_, ?_⟩
  · intro s
    simpa only [hp] using hc.2.1 s
  · intro s t k hk hu hne heq
    rw [hp, hts] at hu
    rw [hp] at hne
    exact hc.2.2 s t k hk hu hne heq

/-! ## 3. `cliWitnessHooksMlKem`, `HooksMatchInterpretation`, & Strengthened `CompExternsSatisfiableCli` -/

/-- Concrete `CliHooks` instance agreeing with `cliWitnessInterpMlKem` AND satisfying all three
    interim-headline `W.Q` equations (`kyber1024EncapsVec`, `kyber1024DecapsVec`,
    `mlkem768Incremental`). -/
noncomputable def cliWitnessHooksMlKem : CliHooks :=
  { cliWitnessHooks with
    Q :=
      { cliWitnessHooks.Q with
        encaps := kyber1024EncapsVec
        decaps := kyber1024DecapsVec
        K := mlkem768Incremental } }

theorem cliWitnessHooksMlKem_encaps : cliWitnessHooksMlKem.Q.encaps = kyber1024EncapsVec := by
  unfold cliWitnessHooksMlKem; rfl

theorem cliWitnessHooksMlKem_decaps : cliWitnessHooksMlKem.Q.decaps = kyber1024DecapsVec := by
  unfold cliWitnessHooksMlKem; rfl

theorem cliWitnessHooksMlKem_K : cliWitnessHooksMlKem.Q.K = mlkem768Incremental := by
  unfold cliWitnessHooksMlKem; rfl

private theorem subtype_toList_eta {α : Type} {n : Nat} (v : List.Vector α n)
    (h : v.toList.length = n) : (⟨v.toList, h⟩ : List.Vector α n) = v :=
  Subtype.ext rfl

theorem cliWitnessHooksMlKem_agree :
    HooksMatchInterpretation cliWitnessInterpMlKem cliWitnessHooksMlKem := by
  have hag := cliWitnessHooks_agree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sha256CompressFunction_cliWitnessInterpMlKem]
    exact hag.1
  · intro p k iv hk hiv
    rw [cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact hag.2.1 p k iv hk hiv
  · intro c k iv hk hiv
    rw [cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact hag.2.2.1 c k iv hk hiv
  · intro a b
    rw [cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact hag.2.2.2.1 a b
  · intro a
    rw [cliWitnessInterpMlKem_other (by decide) (by decide)]
    exact hag.2.2.2.2.1 a
  · intro pk rand
    unfold cliWitnessInterpMlKem
    have hpk : pk.toList.length = 1568 := pk.toList_length
    have hr : rand.toList.length = 32 := rand.toList_length
    simp only [↓reduceIte, hpk, hr, ↓reduceDIte, subtype_toList_eta]
    rw [cliWitnessHooksMlKem_encaps]
  · intro sk ct
    unfold cliWitnessInterpMlKem
    have hne : kyberDecapsSymbol ≠ kyberEncapsSymbol := by decide
    have hsk : sk.toList.length = 3168 := sk.toList_length
    have hct : ct.toList.length = 1568 := ct.toList_length
    simp only [hne, ↓reduceIte, hsk, hct, ↓reduceDIte, subtype_toList_eta]
    rw [cliWitnessHooksMlKem_decaps]

/-- Strengthened `CompExternsSatisfiableCli` witness that additionally satisfies the interim
    headline `W.Q` equations (`kyber1024EncapsVec`, `kyber1024DecapsVec`, `mlkem768Incremental`). -/
theorem comp_externsSatisfiable_cli_mlkem :
    ∃ (interp : ExternInterpretation) (W : CliHooks),
      ExternInterpretationTotalOnUsedSymbols interp ∧
      ExternContractsHoldCli interp ∧
      HooksMatchInterpretation interp W ∧
      W.Q.encaps = kyber1024EncapsVec ∧
      W.Q.decaps = kyber1024DecapsVec ∧
      W.Q.K = mlkem768Incremental :=
  ⟨cliWitnessInterpMlKem, cliWitnessHooksMlKem, cliWitnessInterpMlKem_total,
   cliWitnessInterpMlKem_contracts, cliWitnessHooksMlKem_agree,
   cliWitnessHooksMlKem_encaps, cliWitnessHooksMlKem_decaps, cliWitnessHooksMlKem_K⟩

/-- Drop-in replacement for `comp_externsSatisfiable_cli` backed by the real ML-KEM functions. -/
theorem comp_externsSatisfiable_cli_of_mlkem : CompExternsSatisfiableCli :=
  ⟨cliWitnessInterpMlKem, cliWitnessHooksMlKem, cliWitnessInterpMlKem_total,
   cliWitnessInterpMlKem_contracts, cliWitnessHooksMlKem_agree⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.MlKemExternWitness
