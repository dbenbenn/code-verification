/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import Symbolic.Proofs.SpecLemmas.ElfBindingSha256
import Symbolic.Proofs.Swarm.WIT.RealX25519Laws
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.MlKemExternWitness

/-!
# Real-Primitive Admissibility Witness (`RP-ADM`)

Proves `real_prims_admissible_witness : RealPrimsAdmissible`, showing that there exists an extern
interpretation obeying `ExternContractsHoldCli` and agreeing with `realCliHooks` (`RealPrimsMatch`,
blueprint node `RP-ADM`).

- **Proof idea**: Construct a private `realCliInterp : ExternInterpretation` overriding
  `cliWitnessInterpMlKem` on `sha256CompressSymbol` (with FIPS 180-4 `sha256Compress` between
  `shaStateOfBytes` and `shaStateBytes`), `aesCbcEncryptSymbol` and `aesCbcDecryptSymbol` (with
  PKCS#7-padded CBC over FIPS 197 `aes256Enc` / `aes256Dec`), `x25519PublicKeySymbol` and
  `x25519AgreementSymbol` (with RFC 7748 `x25519Pubkey` / `x25519`), and `x25519TorsionSymbol`
  (`none`), delegating `kyberEncapsSymbol`, `kyberDecapsSymbol`, `libcruxHmacSymbol`, and all
  remaining symbols to `cliWitnessInterpMlKem`. Discharge `ExternContractsHoldCli` via
  `RealX25519Laws.externContractsHoldCli_of_realX25519`, `Aes256Roundtrip`, and
  `cliWitnessInterpMlKem_cryptoEquationsHold`, and `RealPrimsMatch` via
  `ElfBindingSha256.shaStateOfBytes_shaStateBytes`, `X25519Ref`, and `cliWitnessHooksMlKem_agree`.
- **Status**: `done` (Falsification: pairwise disjointness of all 9 extern `StubSymbol` strings via
  `decide`, boundary input slices on X25519 and SHA-256 overrides, and negative check
  `¬ RealPrimsMatch (fun _ _ => none)`; no counterexample).
- **Handoff**: Complete with `0 sorry` and no binary (`CliElf`) imports; wired into `RealPrims.lean`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsWitness

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Composed.Refinement.Cli (
  ExternContractsHoldCli RealPrimsAdmissible RealPrimsMatch shaStateOfBytes_shaStateBytes
)
open DY.Libsignal.PQXDH.Refinement (kyberDecapsSymbol kyberEncapsSymbol libcruxHmacSymbol)
open DY.Libsignal.Refinement (
  StubSymbol aesCbcDecryptSymbol aesCbcEncryptSymbol sha256CompressFunction sha256CompressSymbol
  shaStateBytes shaStateOfBytes x25519AgreementSymbol x25519PublicKeySymbol x25519TorsionSymbol
)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip (
  aesCbcDecrypt_aes256Enc aesCbcEncrypt_of_aesCbcDecrypt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  x25519 x25519PubFromSecretRef_toList x25519Pubkey x25519Ref_toList
)
open Symbolic.Proofs.Swarm.WIT.RealX25519Laws (externContractsHoldCli_of_realX25519)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.MlKemExternWitness (
  cliWitnessHooksMlKem_agree cliWitnessHooksMlKem_decaps cliWitnessHooksMlKem_encaps
  cliWitnessInterpMlKem cliWitnessInterpMlKem_cryptoEquationsHold
)

/-- Concrete `ExternInterpretation` realizing SHA-256 compression, AES-256-CBC, RFC 7748 X25519,
and round-3 Kyber-1024 to match `realCliHooks` while satisfying `ExternContractsHoldCli`. -/
private noncomputable def realCliInterp : ExternInterpretation := fun s args =>
  if s = sha256CompressSymbol then
    match args with
    | [stBytes, blk] =>
      some (shaStateBytes
        (CryptoVerification.LibsignalSpqrV1.sha256Compress (shaStateOfBytes stBytes) blk))
    | _ => none
  else if s = aesCbcEncryptSymbol then
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
  else if s = x25519PublicKeySymbol then
    match args with
    | [secret] => some (x25519Pubkey secret)
    | _ => none
  else if s = x25519AgreementSymbol then
    match args with
    | [secret, point] => some (x25519 secret point)
    | _ => none
  else if s = x25519TorsionSymbol then
    none
  else
    cliWitnessInterpMlKem s args

private theorem realCliInterp_publicKey (secret : ByteString) :
    realCliInterp x25519PublicKeySymbol [secret] = some (x25519Pubkey secret) := by
  have h1 : x25519PublicKeySymbol ≠ sha256CompressSymbol := by decide
  have h2 : x25519PublicKeySymbol ≠ aesCbcEncryptSymbol := by decide
  have h3 : x25519PublicKeySymbol ≠ aesCbcDecryptSymbol := by decide
  simp [realCliInterp, h1, h2, h3]

private theorem realCliInterp_agreement (secret point : ByteString) :
    realCliInterp x25519AgreementSymbol [secret, point] = some (x25519 secret point) := by
  have h1 : x25519AgreementSymbol ≠ sha256CompressSymbol := by decide
  have h2 : x25519AgreementSymbol ≠ aesCbcEncryptSymbol := by decide
  have h3 : x25519AgreementSymbol ≠ aesCbcDecryptSymbol := by decide
  have h4 : x25519AgreementSymbol ≠ x25519PublicKeySymbol := by decide
  simp [realCliInterp, h1, h2, h3, h4]

private theorem realCliInterp_torsion_none (args : List ByteString) :
    realCliInterp x25519TorsionSymbol args = none := by
  have h1 : x25519TorsionSymbol ≠ sha256CompressSymbol := by decide
  have h2 : x25519TorsionSymbol ≠ aesCbcEncryptSymbol := by decide
  have h3 : x25519TorsionSymbol ≠ aesCbcDecryptSymbol := by decide
  have h4 : x25519TorsionSymbol ≠ x25519PublicKeySymbol := by decide
  have h5 : x25519TorsionSymbol ≠ x25519AgreementSymbol := by decide
  simp [realCliInterp, h1, h2, h3, h4, h5]

private theorem realCliInterp_aesEnc (p k iv : ByteString) :
    realCliInterp aesCbcEncryptSymbol [p, k, iv] =
      some (CryptoGames.LibsignalSession.aesCbcEncrypt CryptoGames.AES256.aes256Enc
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p) := by
  have h1 : aesCbcEncryptSymbol ≠ sha256CompressSymbol := by decide
  simp [realCliInterp, h1]

private theorem realCliInterp_aesDec (c k iv : ByteString) :
    realCliInterp aesCbcDecryptSymbol [c, k, iv] =
      CryptoGames.LibsignalSession.aesCbcDecrypt CryptoGames.AES256.aes256Dec
        (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c := by
  have h1 : aesCbcDecryptSymbol ≠ sha256CompressSymbol := by decide
  have h2 : aesCbcDecryptSymbol ≠ aesCbcEncryptSymbol := by decide
  simp [realCliInterp, h1, h2]

private theorem realCliInterp_other {s : StubSymbol}
    (h1 : s ≠ sha256CompressSymbol)
    (h2 : s ≠ aesCbcEncryptSymbol)
    (h3 : s ≠ aesCbcDecryptSymbol)
    (h4 : s ≠ x25519PublicKeySymbol)
    (h5 : s ≠ x25519AgreementSymbol)
    (h6 : s ≠ x25519TorsionSymbol) :
    realCliInterp s = cliWitnessInterpMlKem s := by
  funext args
  simp [realCliInterp, h1, h2, h3, h4, h5, h6]

private theorem realCliInterp_contracts : ExternContractsHoldCli realCliInterp := by
  have hhmac_eq : realCliInterp libcruxHmacSymbol = cliWitnessInterpMlKem libcruxHmacSymbol :=
    realCliInterp_other (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact externContractsHoldCli_of_realX25519 realCliInterp
    realCliInterp_publicKey
    realCliInterp_agreement
    realCliInterp_torsion_none
    (fun pt k iv => by
      rw [realCliInterp_aesEnc, Option.getD_some, realCliInterp_aesDec]
      exact aesCbcDecrypt_aes256Enc _ _ pt)
    (fun c k iv p _ _ hdec => by
      rw [realCliInterp_aesDec] at hdec
      rw [realCliInterp_aesEnc]
      exact congrArg some (aesCbcEncrypt_of_aesCbcDecrypt hdec))
    (fun k d tag h => by
      rw [hhmac_eq] at h
      exact cliWitnessInterpMlKem_cryptoEquationsHold.hmac_tag_length k d tag h)

private theorem sha256CompressFunction_realCliInterp :
    sha256CompressFunction realCliInterp = CryptoVerification.LibsignalSpqrV1.sha256Compress := by
  funext st blk
  simp [sha256CompressFunction, realCliInterp, shaStateOfBytes_shaStateBytes]

private theorem realCliInterp_matches : RealPrimsMatch realCliInterp := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · exact sha256CompressFunction_realCliInterp.symm
  · intro p k iv _ _
    exact realCliInterp_aesEnc p k iv
  · intro c k iv _ _
    exact realCliInterp_aesDec c k iv
  · intro a b
    rw [realCliInterp_agreement]
    exact congrArg some (x25519Ref_toList a b).symm
  · intro a
    rw [realCliInterp_publicKey]
    exact congrArg some (x25519PubFromSecretRef_toList a).symm
  · intro pk rand
    have hkyb_enc : realCliInterp kyberEncapsSymbol = cliWitnessInterpMlKem kyberEncapsSymbol :=
      realCliInterp_other (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hag := cliWitnessHooksMlKem_agree.2.2.2.2.2.1 pk rand
    rw [cliWitnessHooksMlKem_encaps] at hag
    rw [hkyb_enc]
    exact hag
  · intro sk ct
    have hkyb_dec : realCliInterp kyberDecapsSymbol = cliWitnessInterpMlKem kyberDecapsSymbol :=
      realCliInterp_other (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hag := cliWitnessHooksMlKem_agree.2.2.2.2.2.2 sk ct
    rw [cliWitnessHooksMlKem_decaps] at hag
    rw [hkyb_dec]
    exact hag

/-- The closed ELF primitives (`realCliHooks`) obey all symbolic extern laws (`RealPrimsAdmissible`). -/
theorem real_prims_admissible_witness : RealPrimsAdmissible :=
  ⟨realCliInterp, realCliInterp_contracts, realCliInterp_matches⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsWitness
