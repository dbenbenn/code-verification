/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ElfBindingProofDefs
public import Symbolic.Proofs.Swarm.WIT.Pure -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip

/-!
# Extern Contract and Hook Satisfiability Witness for CLI Refinement

Proves `CompExternsSatisfiableCli` and `RealAes256ContractsSatisfiable` by constructing
`cliWitnessInterp` (realizing AES-256-CBC via PKCS#7-padded CBC over the FIPS 197
`CryptoGames.AES256.aes256Enc` / `aes256Dec` block cipher and delegating all remaining extern
symbols to `witnessInterpretation`) together with a matching `CliHooks` instance `cliWitnessHooks`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction x25519AgreementSymbol
  x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.Proofs.Swarm.WIT.Pure
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
  (aesCbcDecrypt_aes256Enc aesCbcEncrypt_of_aesCbcDecrypt)

/-- Witness `ExternInterpretation` realizing AES-256-CBC via PKCS#7-padded CBC over FIPS 197
`CryptoGames.AES256.aes256Enc` / `aes256Dec` and delegating all other symbols to
`witnessInterpretation`. -/
def cliWitnessInterp : ExternInterpretation := fun s args =>
  if s = aesCbcEncryptSymbol then
    match args with
    | [p, k, iv] =>
      some (CryptoGames.LibsignalSession.aesCbcEncrypt CryptoGames.AES256.aes256Enc
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p)
    | _ => none
  else if s = aesCbcDecryptSymbol then
    match args with
    | [c, k, iv] =>
      CryptoGames.LibsignalSession.aesCbcDecrypt CryptoGames.AES256.aes256Dec
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c
    | _ => none
  else witnessInterpretation s args

private theorem cliWitnessInterp_other {s : String}
    (he : s ≠ aesCbcEncryptSymbol) (hd : s ≠ aesCbcDecryptSymbol) :
    cliWitnessInterp s = witnessInterpretation s := by
  funext args; simp [cliWitnessInterp, he, hd]

private theorem cliWitnessInterp_of_witnessLength {s : String} {n : Nat}
    (hw : witnessLength s = some n) (args : List ByteString) :
    cliWitnessInterp s args = some (List.replicate n 0#8) := by
  have he : s ≠ aesCbcEncryptSymbol := by rintro rfl; cases hw
  have hd : s ≠ aesCbcDecryptSymbol := by rintro rfl; cases hw
  rw [cliWitnessInterp_other he hd]
  simp [witnessInterpretation, hw]

theorem cliWitnessInterp_total : ExternInterpretationTotalOnUsedSymbols cliWitnessInterp := by
  have rl : ∀ {s n}, witnessLength s = some n → ∀ args, ReturnsLength cliWitnessInterp s args n :=
    fun hw args => ⟨List.replicate _ 0#8, cliWitnessInterp_of_witnessLength hw args,
      List.length_replicate⟩
  exact
    ⟨fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ _ _ => rl (by decide) _,
     fun _ _ => by rw [cliWitnessInterp_of_witnessLength (n := 0) (by decide)]; rfl,
     fun _ _ _ _ => rl (by decide) _⟩

theorem cliWitnessInterp_cryptoEquationsHold : ExternCryptoLawsHold cliWitnessInterp := by
  have ha : cliWitnessInterp x25519AgreementSymbol = witnessInterpretation x25519AgreementSymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have hp : cliWitnessInterp x25519PublicKeySymbol = witnessInterpretation x25519PublicKeySymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have ht : cliWitnessInterp x25519TorsionSymbol = witnessInterpretation x25519TorsionSymbol :=
    cliWitnessInterp_other (by decide) (by decide)
  have hts : ∀ p t, DY.Libsignal.Refinement.torsionShift cliWitnessInterp p t =
      DY.Libsignal.Refinement.torsionShift witnessInterpretation p t := fun p t => by
    unfold DY.Libsignal.Refinement.torsionShift; rw [ht]
  have hwEq := witnessInterpretation_cryptoEquationsHold
  refine
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
        have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
        simp only [cliWitnessInterp, ↓reduceIte, hne, Option.getD_some]
        exact aesCbcDecrypt_aes256Enc _ _ pt
      aes_cbc_encrypt_of_decrypt := fun c k iv p _ _ hdec => by
        have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
        simp only [cliWitnessInterp, hne, ↓reduceIte] at hdec ⊢
        exact congrArg some (aesCbcEncrypt_of_aesCbcDecrypt hdec)
      hmac_tag_length := fun k d tag h => by
        have hm := cliWitnessInterp_other (s := "libcrux_hmac::hmac") (by decide) (by decide)
        rw [hm] at h
        exact hwEq.hmac_tag_length k d tag h }

theorem cliWitnessInterp_contracts : ExternContractsHoldCli cliWitnessInterp := by
  refine ⟨cliWitnessInterp_cryptoEquationsHold, ?_, ?_⟩
  · intro s
    rw [cliWitnessInterp_other (by decide) (by decide)]
    exact witnessInterpretation_pubCanonical s
  · intro s t k _ hu hne _
    apply hne
    have hts : DY.Libsignal.Refinement.torsionShift cliWitnessInterp
        ((cliWitnessInterp x25519PublicKeySymbol [s]).getD []) t =
        (cliWitnessInterp x25519PublicKeySymbol [s]).getD [] := by
      unfold DY.Libsignal.Refinement.torsionShift
      rw [cliWitnessInterp_other (by decide) (by decide),
        witnessInterpretation_of_none (by decide)]
      split <;> rfl
    rwa [hts] at hu

def cliWitnessMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

def cliWitnessBcmp (a b : List (BitVec 8)) : BitVec 64 :=
  if a == b then 0#64 else 1#64

theorem cliWitnessBcmp_ok (a b : List (BitVec 8)) (_ : a.length = b.length) :
    (cliWitnessBcmp a b).setWidth 32 = 0#32 ↔ a = b := by
  unfold cliWitnessBcmp
  by_cases h : a = b
  · simp [h]
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-- Concrete `CliHooks` instance agreeing with `cliWitnessInterp` on `HooksMatchPlaced` (pinning
`C.E = CryptoGames.AES256.aes256Enc` and `C.D = CryptoGames.AES256.aes256Dec`). -/
@[expose] def cliWitnessHooks : CliHooks where
  C :=
    { F := sha256CompressFunction cliWitnessInterp
      E := CryptoGames.AES256.aes256Enc
      D := CryptoGames.AES256.aes256Dec
      X := fun a b => ⟨exampleAgreement a.toList b.toList, length_exampleAgreement a.toList b.toList⟩
      pubKey := fun a =>
        ⟨exampleAgreement a.toList exampleBasepoint,
         length_exampleAgreement a.toList exampleBasepoint⟩ }
  Q :=
    { F512 := fun st _ => st
      encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
      decaps := fun _ _ => List.Vector.replicate 32 0#8
      K := cliWitnessMlKem }

private theorem toList_vector_replicate (n : Nat) (x : BitVec 8) :
    (List.Vector.replicate n x).toList = List.replicate n x := rfl

theorem cliWitnessHooks_agree : HooksMatchInterpretation cliWitnessInterp cliWitnessHooks := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _
    simp only [cliWitnessInterp, ↓reduceIte]
    rfl
  · intro c k iv _ _
    have hne : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
    simp only [cliWitnessInterp, hne, ↓reduceIte]
    rfl
  · intro a b
    rw [cliWitnessInterp_other (by decide) (by decide),
      witnessInterpretation_of_none (by decide)]
    rfl
  · intro a
    rw [cliWitnessInterp_other (by decide) (by decide),
      witnessInterpretation_of_none (by decide)]
    rfl
  · intro pk rand
    rw [cliWitnessInterp_of_witnessLength (n := 1600) (by decide)]
    dsimp only [cliWitnessHooks]
    rw [toList_vector_replicate, toList_vector_replicate, ← List.replicate_add]
  · intro sk ct
    rw [cliWitnessInterp_of_witnessLength (n := 32) (by decide)]
    rfl

theorem cliWitnessHooks_agree_placed : HooksMatchPlaced cliWitnessInterp cliWitnessHooks :=
  ⟨cliWitnessHooks_agree, rfl, rfl⟩

/-- Satisfiability of the CLI protocol extern contracts and hooks (`CompExternsSatisfiableCli`). -/
theorem comp_externsSatisfiable_cli : CompExternsSatisfiableCli :=
  ⟨cliWitnessInterp, cliWitnessHooks, cliWitnessInterp_total, cliWitnessInterp_contracts,
   cliWitnessHooks_agree⟩

theorem comp_externsSatisfiable_cli_proof : CompExternsSatisfiableCli :=
  comp_externsSatisfiable_cli

/-- Positive non-vacuity of the placed CLI extern contracts and FIPS 197 AES-256 hooks
(`RealAes256ContractsSatisfiable`). -/
theorem realAes256ContractsSatisfiable_cli_proof : RealAes256ContractsSatisfiable :=
  ⟨cliWitnessInterp, cliWitnessHooks, cliWitnessInterp_total, cliWitnessInterp_contracts,
   cliWitnessHooks_agree_placed⟩

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_externsSatisfiable_cli_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_externsSatisfiable_cli_proof

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.realAes256ContractsSatisfiable_cli_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms realAes256ContractsSatisfiable_cli_proof

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli
