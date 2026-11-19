/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges -- proof-setup: allow-public-import
public import Symbolic.Proofs.SpecLemmas.ElfBindingProofDefs -- proof-setup: allow-public-import
public import Symbolic.Proofs.Swarm.WIT.Pure -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding

/-!
# Real `(x25519Ref, x25519PubFromSecretRef)` Symbolic Witness & `ExternContractsHoldCli` (`WIT.RealX25519Laws`)

Discharges the symbolic X25519 algebraic laws (`ExternCryptoLawsHold`, `X25519PubCanonical`,
`X25519TorsionShiftsRejected`, `ExternContractsHoldCli`) when the toy additive `exampleAgreement`
witness is replaced by the real Curve25519 functions `(x25519, x25519Pubkey)` /
`(x25519Ref, x25519PubFromSecretRef)` and `sha512CompressState`:

1. **Codec Equivalence (`leValue_map_toNat_eq_leBytesToNat`, `uCoord_map_toNat_eq_decodeU255_mod`,
   `isLowOrderKey_map_toNat_eq`):** bridges `DY.X25519` little-endian `uCoord` and `isLowOrderKey`
   directly to `CryptoX25519.ConsumerBridges`.
2. **Generic `ExternInterpretation` Combinators (`externCryptoLawsHold_of_realX25519`,
   `externContractsHoldCli_of_realX25519`):** any `ExternInterpretation` agreeing with
   `x25519Pubkey` on `x25519PublicKeySymbol`, `x25519` on `x25519AgreementSymbol`, and `none` on
   `x25519TorsionSymbol` satisfies all X25519 clauses of `ExternCryptoLawsHold`,
   `X25519PubCanonical`, and `X25519TorsionShiftsRejected` (combining cleanly with the
   `cliWitnessInterp` AES-256-CBC witness or any future real-AES/HMAC/SHA-256 witness).
3. **Concrete `realX25519WitnessInterpretation`:** overrides `witnessInterpretation` on
   `x25519PublicKeySymbol` and `x25519AgreementSymbol` and proves
   `ExternInterpretationTotalOnUsedSymbols` + `ExternContractsHoldCli`.
-/

set_option autoImplicit false

public section

namespace Symbolic.Proofs.Swarm.WIT.RealX25519Laws

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SignalSession (CliHooks)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ExternInterpretationTotalOnUsedSymbols ReturnsLength X25519PubCanonical)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionShiftsRejected libcruxHmacSymbol)
open DY.Libsignal.Refinement
  (ExternCryptoLawsHold StubSymbol aesCbcDecryptSymbol aesCbcEncryptSymbol sha256CompressFunction
   torsionShift x25519AgreementSymbol x25519PublicKeySymbol x25519TorsionSymbol)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.ConsumerBridges
  (isLowOrderX25519 isLowOrderX25519_eq_nat_rec isLowOrderX25519_x25519Pubkey
   leBytesToNat_eq_nat_rec leBytesToNat_x25519Pubkey_lt_p25519 x25519Pubkey_out_length
   x25519_congr_of_decodeU255_mod_eq x25519_dh_comm x25519_eq_zero_iff_isLowOrderX25519
   x25519_out_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (decodeU255 x25519 x25519PubFromSecretRef x25519Pubkey x25519Ref)
open Symbolic.Proofs.Swarm.WIT.Pure
  (witnessInterpretation witnessInterpretation_cryptoEquationsHold witnessInterpretation_of_none
   witnessLength)
open VerifiedLibraries.Common (leBytesToNat p25519)

/-! ## 1. `DY.X25519` ↔ `CryptoX25519` Codec Bridges -/

private theorem dy_p25519_eq : DY.X25519.p25519 = p25519 :=
  rfl

private theorem dy_leValue_eq_nat_rec :
    ∀ ns : List Nat,
      DY.X25519.leValue ns = List.rec 0 (fun x _ acc => x + 256 * acc) ns
  | [] => rfl
  | n :: ns => by
    simp only [DY.X25519.leValue, dy_leValue_eq_nat_rec ns]

theorem leValue_map_toNat_eq_leBytesToNat (bs : HwBytes) :
    DY.X25519.leValue (bs.map BitVec.toNat) = leBytesToNat bs :=
  (dy_leValue_eq_nat_rec (bs.map BitVec.toNat)).trans (leBytesToNat_eq_nat_rec bs).symm

theorem uCoord_map_toNat_eq_decodeU255_mod {bs : HwBytes} (hbs : bs.length = 32) :
    DY.X25519.uCoord (bs.map BitVec.toNat) = decodeU255 bs % p25519 := by
  unfold DY.X25519.uCoord decodeU255
  rw [dy_p25519_eq, leValue_map_toNat_eq_leBytesToNat,
      List.take_of_length_le (Nat.le_of_eq hbs)]

theorem isLowOrderKey_map_toNat_eq (bs : HwBytes) :
    DY.X25519.isLowOrderKey (bs.map BitVec.toNat) = isLowOrderX25519 bs := by
  unfold DY.X25519.isLowOrderKey DY.X25519.uCoord
  rw [dy_leValue_eq_nat_rec, isLowOrderX25519_eq_nat_rec]
  rfl

/-! ## 2. Generic Real-X25519 `ExternCryptoLawsHold` & `ExternContractsHoldCli` Combinators -/

/-- Any `ExternInterpretation` agreeing with `(x25519Pubkey, x25519)` on the two X25519 symbols and
    returning `none` on `x25519TorsionSymbol` satisfies `ExternCryptoLawsHold` once the 3 non-X25519
    clauses (AES-CBC invertibility/injectivity and HMAC tag length) are supplied. -/
theorem externCryptoLawsHold_of_realX25519 (I : ExternInterpretation)
    (hpub : ∀ a : ByteString, I x25519PublicKeySymbol [a] = some (x25519Pubkey a))
    (hagree : ∀ a p : ByteString, I x25519AgreementSymbol [a, p] = some (x25519 a p))
    (htors : ∀ args : List ByteString, I x25519TorsionSymbol args = none)
    (haes_dec : ∀ plaintext key iv : ByteString,
      I aesCbcDecryptSymbol
        [(I aesCbcEncryptSymbol [plaintext, key, iv]).getD [], key, iv] = some plaintext)
    (haes_enc : ∀ ciphertext key iv plaintext : ByteString,
      key.length = 32 → iv.length = 16 →
      I aesCbcDecryptSymbol [ciphertext, key, iv] = some plaintext →
      I aesCbcEncryptSymbol [plaintext, key, iv] = some ciphertext)
    (hhmac : ∀ k d tag : ByteString, I libcruxHmacSymbol [k, d] = some tag → tag.length = 32) :
    ExternCryptoLawsHold I where
  x25519_agreement_commutes a b := by
    simp only [hpub, hagree, Option.getD_some, x25519_dh_comm]
  x25519_agreement_length a p := by
    simp only [hagree, Option.getD_some, x25519_out_length]
  x25519_public_key_length a := by
    simp only [hpub, Option.getD_some, x25519Pubkey_out_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [hagree]
    rw [uCoord_map_toNat_eq_decodeU255_mod hb, uCoord_map_toNat_eq_decodeU255_mod hb'] at hu
    exact congrArg some (x25519_congr_of_decodeU255_mod_eq a hu)
  x25519_agreement_torsion_invariant a p t := by
    unfold torsionShift
    split
    · rfl
    · rw [htors]
  x25519_agreement_zero_iff_low_order a b _ hb32 := by
    simp only [hagree, Option.getD_some, isLowOrderKey_map_toNat_eq]
    exact x25519_eq_zero_iff_isLowOrderX25519 a hb32
  x25519_public_key_not_low_order a _ := by
    simp only [hpub, Option.getD_some, isLowOrderKey_map_toNat_eq]
    exact isLowOrderX25519_x25519Pubkey a
  aes_cbc_decrypt_inverts_encrypt := haes_dec
  aes_cbc_encrypt_of_decrypt := haes_enc
  hmac_tag_length := hhmac

theorem x25519PubCanonical_of_realX25519 (I : ExternInterpretation)
    (hpub : ∀ s : ByteString, I x25519PublicKeySymbol [s] = some (x25519Pubkey s)) :
    X25519PubCanonical I := by
  intro s
  rw [hpub s, Option.getD_some, leValue_map_toNat_eq_leBytesToNat, dy_p25519_eq]
  exact leBytesToNat_x25519Pubkey_lt_p25519 s

theorem x25519TorsionShiftsRejected_of_torsion_none (I : ExternInterpretation)
    (htors : ∀ args : List ByteString, I x25519TorsionSymbol args = none) :
    X25519TorsionShiftsRejected I := by
  intro s t k _ hu hne _
  apply hne
  have hts : torsionShift I ((I x25519PublicKeySymbol [s]).getD []) t =
      (I x25519PublicKeySymbol [s]).getD [] := by
    unfold torsionShift
    split
    · rfl
    · rw [htors]
  rwa [hts] at hu

/-- Full `ExternContractsHoldCli I` combinator for any `ExternInterpretation` realizing X25519 via
    `(x25519Pubkey, x25519)` with `I x25519TorsionSymbol _ = none`. -/
theorem externContractsHoldCli_of_realX25519 (I : ExternInterpretation)
    (hpub : ∀ a : ByteString, I x25519PublicKeySymbol [a] = some (x25519Pubkey a))
    (hagree : ∀ a p : ByteString, I x25519AgreementSymbol [a, p] = some (x25519 a p))
    (htors : ∀ args : List ByteString, I x25519TorsionSymbol args = none)
    (haes_dec : ∀ plaintext key iv : ByteString,
      I aesCbcDecryptSymbol
        [(I aesCbcEncryptSymbol [plaintext, key, iv]).getD [], key, iv] = some plaintext)
    (haes_enc : ∀ ciphertext key iv plaintext : ByteString,
      key.length = 32 → iv.length = 16 →
      I aesCbcDecryptSymbol [ciphertext, key, iv] = some plaintext →
      I aesCbcEncryptSymbol [plaintext, key, iv] = some ciphertext)
    (hhmac : ∀ k d tag : ByteString, I libcruxHmacSymbol [k, d] = some tag → tag.length = 32) :
    ExternContractsHoldCli I :=
  ⟨externCryptoLawsHold_of_realX25519 I hpub hagree htors haes_dec haes_enc hhmac,
   x25519PubCanonical_of_realX25519 I hpub,
   x25519TorsionShiftsRejected_of_torsion_none I htors⟩

/-! ## 3. Concrete `realX25519WitnessInterpretation` & `CliHooks` Agreement -/

/-- `witnessInterpretation` overridden on `x25519PublicKeySymbol` and `x25519AgreementSymbol` by the
    real Curve25519 functions `(x25519Pubkey, x25519)`. -/
@[expose] def realX25519WitnessInterpretation : ExternInterpretation := fun s args =>
  if s = x25519PublicKeySymbol then
    match args with
    | [secret] => some (x25519Pubkey secret)
    | _ => none
  else if s = x25519AgreementSymbol then
    match args with
    | [secret, point] => some (x25519 secret point)
    | _ => none
  else
    witnessInterpretation s args

theorem realX25519WitnessInterpretation_publicKey (secret : ByteString) :
    realX25519WitnessInterpretation x25519PublicKeySymbol [secret] = some (x25519Pubkey secret) := by
  simp [realX25519WitnessInterpretation]

theorem realX25519WitnessInterpretation_agreement (secret point : ByteString) :
    realX25519WitnessInterpretation x25519AgreementSymbol [secret, point] =
      some (x25519 secret point) := by
  have hne : x25519AgreementSymbol ≠ x25519PublicKeySymbol := by decide
  simp [realX25519WitnessInterpretation, hne]

theorem realX25519WitnessInterpretation_other {s : StubSymbol}
    (h1 : s ≠ x25519PublicKeySymbol) (h2 : s ≠ x25519AgreementSymbol) :
    realX25519WitnessInterpretation s = witnessInterpretation s := by
  funext args
  simp [realX25519WitnessInterpretation, h1, h2]

theorem realX25519WitnessInterpretation_of_witnessLength {s : StubSymbol} {n : Nat}
    (hw : witnessLength s = some n) (args : List ByteString) :
    realX25519WitnessInterpretation s args = some (List.replicate n 0#8) := by
  have h1 : s ≠ x25519PublicKeySymbol := by
    have hn : witnessLength x25519PublicKeySymbol = none := by decide
    rintro rfl; rw [hn] at hw; cases hw
  have h2 : s ≠ x25519AgreementSymbol := by
    have hn : witnessLength x25519AgreementSymbol = none := by decide
    rintro rfl; rw [hn] at hw; cases hw
  rw [realX25519WitnessInterpretation_other h1 h2]
  simp [witnessInterpretation, hw]

theorem realX25519WitnessInterpretation_total :
    ExternInterpretationTotalOnUsedSymbols realX25519WitnessInterpretation := by
  have rl : ∀ {s n}, witnessLength s = some n → ∀ args,
      ReturnsLength realX25519WitnessInterpretation s args n := fun hw args =>
    ⟨List.replicate _ 0#8, realX25519WitnessInterpretation_of_witnessLength hw args,
     List.length_replicate⟩
  exact
    ⟨fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ => rl (by decide) _,
     fun _ _ _ => rl (by decide) _,
     fun _ _ _ _ => rl (by decide) _,
     fun _ _ _ _ _ _ => rl (by decide) _,
     fun _ _ => by
       rw [realX25519WitnessInterpretation_of_witnessLength (n := 0) (by decide)]; rfl,
     fun _ _ _ _ => rl (by decide) _⟩

private theorem realX25519WitnessInterpretation_torsion_none (args : List ByteString) :
    realX25519WitnessInterpretation x25519TorsionSymbol args = none := by
  rw [realX25519WitnessInterpretation_other (by decide) (by decide),
      witnessInterpretation_of_none (by decide)]
  simp [Symbolic.Proofs.Swarm.WIT.Pure.exampleInterpretation, x25519TorsionSymbol,
    x25519PublicKeySymbol, x25519AgreementSymbol, aesCbcEncryptSymbol, aesCbcDecryptSymbol]

theorem realX25519WitnessInterpretation_contracts :
    ExternContractsHoldCli realX25519WitnessInterpretation := by
  have hw := witnessInterpretation_cryptoEquationsHold
  have henc : realX25519WitnessInterpretation aesCbcEncryptSymbol =
      witnessInterpretation aesCbcEncryptSymbol :=
    realX25519WitnessInterpretation_other (by decide) (by decide)
  have hdec : realX25519WitnessInterpretation aesCbcDecryptSymbol =
      witnessInterpretation aesCbcDecryptSymbol :=
    realX25519WitnessInterpretation_other (by decide) (by decide)
  have hhmac_eq : realX25519WitnessInterpretation libcruxHmacSymbol =
      witnessInterpretation libcruxHmacSymbol :=
    realX25519WitnessInterpretation_other (by decide) (by decide)
  exact externContractsHoldCli_of_realX25519 realX25519WitnessInterpretation
    realX25519WitnessInterpretation_publicKey
    realX25519WitnessInterpretation_agreement
    realX25519WitnessInterpretation_torsion_none
    (fun pt k iv => by simpa only [henc, hdec] using hw.aes_cbc_decrypt_inverts_encrypt pt k iv)
    (fun c k iv p hk hiv h => by
      rw [hdec] at h; rw [henc]; exact hw.aes_cbc_encrypt_of_decrypt c k iv p hk hiv h)
    (fun k d tag h => by rw [hhmac_eq] at h; exact hw.hmac_tag_length k d tag h)

/-- Witness `MlKem` bundle for `realX25519WitnessHooksOfAes`. -/
def realX25519WitnessMlKem : MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ := fun _ => List.Vector.replicate 32 0#8
  validPk _ _ := true

/-- Canonical `CliHooks` builder setting `C.X := x25519Ref`,
    `C.pubKey := x25519PubFromSecretRef`, and `Q.F512 := sha512CompressState` so all three
    equations hold definitionally (`rfl`), parameterized by `(interp, E, D)` so the
    AES-256-CBC witness plugs straight in. -/
@[expose] def realX25519WitnessHooksOfAes (interp : ExternInterpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    CliHooks where
  C :=
    { F := sha256CompressFunction interp
      E := E
      D := D
      X := x25519Ref
      pubKey := x25519PubFromSecretRef }
  Q :=
    { F512 := sha512CompressState
      encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
      decaps := fun _ _ => List.Vector.replicate 32 0#8
      K := realX25519WitnessMlKem }

theorem realX25519WitnessHooksOfAes_X (interp : ExternInterpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    (realX25519WitnessHooksOfAes interp E D).C.X = x25519Ref :=
  rfl

theorem realX25519WitnessHooksOfAes_pubKey (interp : ExternInterpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    (realX25519WitnessHooksOfAes interp E D).C.pubKey = x25519PubFromSecretRef :=
  rfl

theorem realX25519WitnessHooksOfAes_F512 (interp : ExternInterpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    (realX25519WitnessHooksOfAes interp E D).Q.F512 = sha512CompressState :=
  rfl

private theorem toList_vector_replicate (n : Nat) (x : BitVec 8) :
    (List.Vector.replicate n x).toList = List.replicate n x :=
  rfl

/-- `HooksMatchInterpretation` combinator for `realX25519WitnessHooksOfAes interp E D`. -/
theorem hooksMatchInterpretation_realX25519WitnessHooksOfAes (interp : ExternInterpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (hpub : ∀ a : ByteString, interp x25519PublicKeySymbol [a] = some (x25519Pubkey a))
    (hagree : ∀ a p : ByteString, interp x25519AgreementSymbol [a, p] = some (x25519 a p))
    (henc : ∀ p k iv : ByteString, k.length = 32 → iv.length = 16 →
      interp aesCbcEncryptSymbol [p, k, iv] =
        some (CryptoGames.LibsignalSession.aesCbcEncrypt E
          (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p))
    (hdec : ∀ c k iv : ByteString, k.length = 32 → iv.length = 16 →
      interp aesCbcDecryptSymbol [c, k, iv] =
        CryptoGames.LibsignalSession.aesCbcDecrypt D
          (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c)
    (hkyb_enc : ∀ pk rand,
      interp DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [pk, rand] =
        some (List.replicate 1600 0#8))
    (hkyb_dec : ∀ sk ct,
      interp DY.Libsignal.PQXDH.Refinement.kyberDecapsSymbol [sk, ct] =
        some (List.replicate 32 0#8)) :
    HooksMatchInterpretation interp (realX25519WitnessHooksOfAes interp E D) := by
  refine ⟨rfl, henc, hdec, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hagree]
    rfl
  · intro a
    rw [hpub]
    rfl
  · intro pk rand
    rw [hkyb_enc]
    dsimp only [realX25519WitnessHooksOfAes]
    rw [toList_vector_replicate, toList_vector_replicate, ← List.replicate_add]
  · intro sk ct
    rw [hkyb_dec]
    rfl

end Symbolic.Proofs.Swarm.WIT.RealX25519Laws
