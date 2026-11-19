/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ByteSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompI0Laws
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol sha256CompressFunction CryptoEquationsHold)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol mlkem768FromSeedSymbol mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol X25519TorsionFree X25519TorsionShiftsRejected)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (Records Sem Ghost randTerm leBytes X25519PubCanonical ReturnsLength ExternInterpretationTotalOnUsedSymbols)
open DY.Libsignal.Composed.Refinement.Cli (HooksMatchInterpretation HooksMatchPlaced ExternContractsHoldCli)
open CryptoVerification.SignalSession (CliHooks)
@[simp]
theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih (v / 256)]
theorem compI0_publicKey (sk : HwBytes) : compI0 x25519PublicKeySymbol [sk] = some (compLookupPub sk) := rfl
theorem compI0_agreement (sk pk : HwBytes) : compI0 x25519AgreementSymbol [sk, pk] = some (compLookupDh sk pk) := rfl
theorem compI0_torsion (pt : HwBytes) (b : BitVec 8) : compI0 x25519TorsionSymbol [pt, [b]] = compLookupTorsion pt b := rfl
theorem compI0_aesEncrypt (text k iv : HwBytes) : compI0 aesCbcEncryptSymbol [text, k, iv] = some (compAesPerm k iv text) := rfl
theorem compI0_aesDecrypt (text k iv : HwBytes) : compI0 aesCbcDecryptSymbol [text, k, iv] = compAesDec k iv text := rfl
theorem compI0_kyberEncaps (pk e : HwBytes) : compI0 kyberEncapsSymbol [pk, e] = some (compKyberEncaps e) := rfl
theorem compI0_kyberDecaps (sk ct : HwBytes) : compI0 kyberDecapsSymbol [sk, ct] = some (compKyberDecaps ct) := rfl
theorem compI0_hmac (k d : HwBytes) : compI0 libcruxHmacSymbol [k, d] = some (compHmac k d) := rfl
theorem compPubOfOpt_length (o : Option (Fin 12)) : (compPubOfOpt o).length = 32 := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPubOfOpt_lt_p25519 (o : Option (Fin 12)) : leValue ((compPubOfOpt o).map BitVec.toNat) < p25519 := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPubOfOpt_not_lowOrder (o : Option (Fin 12)) : isLowOrderKey ((compPubOfOpt o).map BitVec.toNat) = false := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compPointIdx_compPubOfOpt (o : Option (Fin 12)) : compPointIdx (compPubOfOpt o) = o := by
  cases o with
  | none => decide
  | some i => revert i; decide
theorem compDhByIdx_comm : ∀ i j : Fin 12, compDhByIdx i j = compDhByIdx j i := by decide
theorem compDhByIdx_length : ∀ i j : Fin 12, (compDhByIdx i j).length = 32 := by decide
theorem compDhByIdx_ne_zero : ∀ i j : Fin 12, compDhByIdx i j ≠ List.replicate 32 0#8 := by decide
theorem compDefaultDh_length : compDefaultDh.length = 32 := leBytes_length 32 _
theorem compDefaultDh_ne_zero : compDefaultDh ≠ List.replicate 32 0#8 := by decide
theorem compEkAPub_length : compEkAPub.length = 32 := leBytes_length 32 _
theorem compEkATorsion_length : compEkATorsion.length = 32 := leBytes_length 32 _
theorem compEkAPub_not_lowOrder : isLowOrderKey (compEkAPub.map BitVec.toNat) = false := by decide
theorem compEkATorsion_not_lowOrder : isLowOrderKey (compEkATorsion.map BitVec.toNat) = false := by decide
theorem compPointIdx_ekATorsion_eq_ekAPub : compPointIdx compEkATorsion = compPointIdx compEkAPub := by decide
theorem compLookupPub_length (s : HwBytes) : (compLookupPub s).length = 32 := compPubOfOpt_length (compSecretIdx s)
theorem compLookupPub_lt_p25519 (s : HwBytes) : leValue ((compLookupPub s).map BitVec.toNat) < p25519 := compPubOfOpt_lt_p25519 (compSecretIdx s)
theorem compLookupPub_not_lowOrder (s : HwBytes) : isLowOrderKey ((compLookupPub s).map BitVec.toNat) = false := compPubOfOpt_not_lowOrder (compSecretIdx s)
theorem compPointIdx_compLookupPub (s : HwBytes) : compPointIdx (compLookupPub s) = compSecretIdx s := compPointIdx_compPubOfOpt (compSecretIdx s)
theorem compLookupDh_comm (a b : HwBytes) : compLookupDh a (compLookupPub b) = compLookupDh b (compLookupPub a) := by
  unfold compLookupDh; rw [compLookupPub_not_lowOrder b, compLookupPub_not_lowOrder a]; simp only [Bool.false_eq_true, ↓reduceIte, compPointIdx_compLookupPub]
  cases compSecretIdx a <;> cases compSecretIdx b <;> simp [compDhByIdx_comm]
theorem compLookupDh_length (s p : HwBytes) : (compLookupDh s p).length = 32 := by
  unfold compLookupDh
  split
  · simp
  · cases compSecretIdx s <;> cases compPointIdx p <;>
      simp [compDhByIdx_length, compDefaultDh_length]
theorem compLookupDh_ne_zero_of_not_lowOrder (s p : HwBytes) (hlo : isLowOrderKey (p.map BitVec.toNat) = false) : compLookupDh s p ≠ List.replicate 32 0#8 := by
  unfold compLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases compSecretIdx s <;> cases compPointIdx p
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · next i j => exact compDhByIdx_ne_zero i j
private theorem fin8_bv_ne_one : ∀ t : Fin 8, t.val ≠ 1 → BitVec.ofNat 8 t.val ≠ 1#8 := by decide
theorem torsionShift_compI0 (p : HwBytes) (t : Fin 8) : torsionShift compI0 p t = if t.val = 1 ∧ p = compEkAPub then compEkATorsion else p := by
  unfold torsionShift; rw [compI0_torsion]; unfold compLookupTorsion
  by_cases ht1 : t.val = 1
  · have hbv : BitVec.ofNat 8 t.val = 1#8 := by rw [ht1]
    have ht0 : t ≠ 0 := by intro h; subst h; nomatch ht1
    rw [hbv]; simp only [ht1, ht0, false_or, true_and, ↓reduceIte]
    by_cases hp : p = compEkAPub
    · subst hp; simp [compEkAPub_length, compEkATorsion_length]
    · have hbeq : (p == compEkAPub) = false := beq_false_of_ne hp; simp [hp, hbeq]
  · have hbv : BitVec.ofNat 8 t.val ≠ 1#8 := fin8_bv_ne_one t ht1; simp [ht1, hbv]
theorem compLookupDh_torsionShift (s p : HwBytes) (t : Fin 8) : compLookupDh s (torsionShift compI0 p t) = compLookupDh s p := by
  rw [torsionShift_compI0]
  split
  · next h =>
    rcases h with ⟨_, rfl⟩
    unfold compLookupDh; rw [compEkATorsion_not_lowOrder, compEkAPub_not_lowOrder, compPointIdx_ekATorsion_eq_ekAPub]
  · rfl
private theorem cbcEncrypt_eq (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      CryptoGames.CBC.cbcEncrypt f iv P = ByteSpecs.cbcEncrypt f iv P
  | _, 0, _ => rfl
  | iv, _ + 1, P => by
    simp only [CryptoGames.CBC.cbcEncrypt, ByteSpecs.cbcEncrypt]
    rw [cbcEncrypt_eq f (f (P.head ^^^ iv)) P.tail]
private theorem aesCbcEncrypt_eq_byteSpecs
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (p : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p =
      (ByteSpecs.cbcEncrypt (E k) iv
        (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList.flatMap
        ByteSpecs.blockToBytesLE := by
  let vp : List.Vector (BitVec 8) p.length := ⟨p, rfl⟩
  change (CryptoGames.CBC.cbcEncrypt (E k) iv (CryptoGames.CBC.pkcs7Blocks vp)).toList.flatMap
      CryptoGames.CBC.blockToBytesLE =
    (ByteSpecs.cbcEncrypt (E k) iv (ByteSpecs.pkcs7Blocks vp)).toList.flatMap
      ByteSpecs.blockToBytesLE
  have hpk : CryptoGames.CBC.pkcs7Blocks vp = ByteSpecs.pkcs7Blocks vp := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  rw [hbl]
  exact congrArg (fun v => v.toList.flatMap ByteSpecs.blockToBytesLE)
    (hpk ▸ cbcEncrypt_eq (E k) iv (ByteSpecs.pkcs7Blocks vp))
private theorem length_flatMap_blockToBytesLE :
    ∀ (cs : List ByteSpecs.Block),
      (cs.flatMap ByteSpecs.blockToBytesLE).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
    have h16 : (ByteSpecs.blockToBytesLE c).length = 16 := by simp [ByteSpecs.blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, h16, length_flatMap_blockToBytesLE cs,
      List.length_cons]
    omega
theorem compAesDec_compAesPerm (k iv text : HwBytes) :
    compAesDec k iv (compAesPerm k iv text) = some text :=
  LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip.aesCbcDecrypt_aes256Enc
    (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text
theorem compAesPerm_of_compAesDec {k iv ct pt : HwBytes}
    (h : compAesDec k iv ct = some pt) :
    compAesPerm k iv pt = ct :=
  LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip.aesCbcEncrypt_of_aesCbcDecrypt h
theorem compAesPerm_length (k iv text : HwBytes) :
    (compAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold compAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]
  rfl
theorem compAesPerm_length_ge_16 (k iv text : HwBytes) :
    16 ≤ (compAesPerm k iv text).length := by
  rw [compAesPerm_length]; omega
theorem compAesPerm_length_of_lt_16 (k iv text : HwBytes) (h : text.length < 16) :
    (compAesPerm k iv text).length = 16 := by
  rw [compAesPerm_length, Nat.div_eq_zero_iff.mpr (Or.inr h)]
theorem compAesPerm_pt0 : compAesPerm compAesK0 compAesIv0 compAesPt0 = compAesCt0 := by decide
theorem compAesPerm_ne_fillFresh64 (k iv text : HwBytes) (t : Nat)
    (hlen : text.length / 16 ≠ 3) :
    compAesPerm k iv text ≠ Symbolic.BugInjection.fillFresh t 64 := by
  intro h
  have hl : (compAesPerm k iv text).length = 64 := by rw [h]; rfl
  rw [compAesPerm_length] at hl
  omega
theorem compDefaultHmac_length (k d : HwBytes) : (compDefaultHmac k d).length = 32 := by simp [compDefaultHmac, compTag4, compHmacMix28]
theorem compHmac_length (k d : HwBytes) : (compHmac k d).length = 32 := by
  unfold compHmac
  split
  · dsimp only
    split
    · exact leBytes_length 32 _
    · split
      · exact leBytes_length 32 _
      · split
        · exact leBytes_length 32 _
        · exact compDefaultHmac_length k d
  · exact compDefaultHmac_length k d
theorem compI0_cryptoEquationsHold : CryptoEquationsHold compI0 where
  x25519_agreement_commutes a b := by simp only [compI0_publicKey, compI0_agreement, Option.getD_some]; exact congrArg some (compLookupDh_comm a b)
  x25519_agreement_length a p := by simp [compI0_agreement, compLookupDh_length]
  x25519_public_key_length a := by simp [compI0_publicKey, compLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [compI0_agreement]; congr 1; have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := (by simp only [isLowOrderKey, List.length_map, hb, hb']; exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu)
    have hp : compPointIdx b = compPointIdx b' := by simp only [compPointIdx, hb, hb', hu]
    unfold compLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by simp only [compI0_agreement]; exact congrArg some (compLookupDh_torsionShift secret point t)
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [compI0_agreement, Option.getD_some]; cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]; exact compLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold compLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [compI0_publicKey, compLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [compI0_aesEncrypt, compI0_aesDecrypt, Option.getD_some]
    exact compAesDec_compAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [compI0_aesDecrypt] at h
    rw [compI0_aesEncrypt]
    exact congrArg some (compAesPerm_of_compAesDec h)
  hmac_tag_length k d t h := by rw [compI0_hmac, Option.some.injEq] at h; rw [← h]; exact compHmac_length k d
theorem compI0_pubCanonical : X25519PubCanonical compI0 := by intro s; rw [compI0_publicKey, Option.getD_some]; exact compLookupPub_lt_p25519 s
private theorem not_x25519TorsionFree_of_uCoord_ekATorsion (k : HwBytes) (hk : k.length = 32)
    (hu : uCoord (k.map BitVec.toNat) = uCoord (compEkATorsion.map BitVec.toNat)) :
    ¬ X25519TorsionFree k := by
  have hek : uCoord (compEkATorsion.map BitVec.toNat) =
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.ekATorsionNat := by
    decide
  have hdec : LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs.decodeU255 k %
      VerifiedLibraries.Common.p25519 =
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.ekATorsionNat := by
    have hmod :=
      LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.decodeU255_mod_p_eq_nat_rec_of_length_32
        leValue rfl (fun _ _ => rfl) hk
    exact hmod.symm.trans (hu.trans hek)
  rw [X25519TorsionFree,
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.signalMontLiftEd_torsionFree_iff_dalekPrimsRef hk]
  rintro ⟨pt, hmont, htf⟩
  have hf :=
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge.dalekPrimsRef_isTorsionFree_ekATorsion_false_of_mod_p
      (u := ⟨k, hk⟩) hdec hmont
  rw [hf] at htf
  cases htf
theorem compI0_torsionShiftsRejected : X25519TorsionShiftsRejected compI0 := by
  intro s t k hk hu hne htf
  rw [compI0_publicKey, Option.getD_some, torsionShift_compI0] at hu
  rw [compI0_publicKey, Option.getD_some] at hne
  split at hu
  · exact not_x25519TorsionFree_of_uCoord_ekATorsion k hk hu htf
  · exact hne hu
theorem compI0_externContractsHoldCli : ExternContractsHoldCli compI0 :=
  ⟨compI0_cryptoEquationsHold, compI0_pubCanonical, compI0_torsionShiftsRejected⟩
private theorem compKyberCt0_length : compKyberCt0.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt1_length : compKyberCt1.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt2_length : compKyberCt2.length = 1568 := leBytes_length 1568 _
private theorem compDefaultKyberCt_length : compDefaultKyberCt.length = 1568 := List.length_replicate
private theorem compKyberSs0_length : compKyberSs0.length = 32 := leBytes_length 32 _
private theorem compKyberSs1_length : compKyberSs1.length = 32 := leBytes_length 32 _
private theorem compKyberSs2_length : compKyberSs2.length = 32 := leBytes_length 32 _
private theorem compDefaultKyberSs_length : compDefaultKyberSs.length = 32 := List.length_replicate
theorem compKyberEncaps_length (e : HwBytes) : (compKyberEncaps e).length = 1600 := by
  unfold compKyberEncaps
  repeat (first | simp only [List.length_append, compKyberCt0_length, compKyberCt1_length, compKyberCt2_length, compDefaultKyberCt_length, compKyberSs0_length, compKyberSs1_length, compKyberSs2_length, compDefaultKyberSs_length] | split)
theorem compKyberDecaps_length (ct : HwBytes) : (compKyberDecaps ct).length = 32 := by
  unfold compKyberDecaps
  repeat (first | exact compKyberSs0_length | exact compKyberSs1_length | exact compKyberSs2_length | exact compDefaultKyberSs_length | split)
theorem compToEdwards_length (u : HwBytes) (sign : BitVec 8) : (compToEdwards u sign).length = 160 := by
  unfold compToEdwards compToEdOut0 compToEdOut1 compToEdOut2
  repeat (first | exact leBytes_length 160 _ | exact List.length_replicate | split)
def compMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true
def compBcmp0 (a b : List (BitVec 8)) : BitVec 64 :=
  if a == b then 0#64 else 1#64
theorem compBcmp0_ok (a b : List (BitVec 8)) (_ : a.length = b.length) :
    (compBcmp0 a b).setWidth 32 = 0#32 ↔ a = b := by
  unfold compBcmp0
  by_cases h : a = b
  · simp [h]
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]
def compHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction compI0
      E := compAesBlock
      D := compAesInvBlock
      X := fun a b => ⟨compLookupDh a.toList b.toList, compLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨compLookupPub a.toList, compLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st _ => st
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := compMlKem0 }
theorem compI0_hooksMatch : HooksMatchInterpretation compI0 compHooks0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [compI0_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (compKyberEncaps rand.toList)).symm
  · intro sk ct; rfl
private theorem compKyberCt1_beq_ct0 : (compKyberCt1 == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberCt2_beq_ct0 : (compKyberCt2 == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberCt2_beq_ct1 : (compKyberCt2 == compKyberCt1) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct0 : (compDefaultKyberCt == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct1 : (compDefaultKyberCt == compKyberCt1) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compDefaultKyberCt_beq_ct2 : (compDefaultKyberCt == compKyberCt2) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)
private theorem compKyberDecaps_ct0 : compKyberDecaps compKyberCt0 = compKyberSs0 := by simp [compKyberDecaps]
private theorem compKyberDecaps_ct1 : compKyberDecaps compKyberCt1 = compKyberSs1 := by simp [compKyberDecaps, compKyberCt1_beq_ct0]
private theorem compKyberDecaps_ct2 : compKyberDecaps compKyberCt2 = compKyberSs2 := by simp [compKyberDecaps, compKyberCt2_beq_ct0, compKyberCt2_beq_ct1]
private theorem compKyberDecaps_default : compKyberDecaps compDefaultKyberCt = compDefaultKyberSs := by simp [compKyberDecaps, compDefaultKyberCt_beq_ct0, compDefaultKyberCt_beq_ct1, compDefaultKyberCt_beq_ct2]
private theorem take_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).take n = l1 := by subst h; exact List.take_left
private theorem drop_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left
theorem compI0_kyberCorrectOn (r : Records) (cts : List HwBytes) : ∀ ct ∈ cts, ∀ e ss, e.length = 32 → DY.Libsignal.Composed.Refinement.kyberEncapsBytes compI0 r e = some (ct, ss) → DY.Libsignal.Composed.Refinement.kyberDecapsBytes compI0 r ct = some ss := by
  intro ct _ e ss _ he; unfold DY.Libsignal.Composed.Refinement.kyberEncapsBytes DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm at he; rw [compI0_kyberEncaps, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨hct, hss⟩ := he; unfold DY.Libsignal.Composed.Refinement.kyberDecapsBytes; rw [compI0_kyberDecaps, Option.some.injEq]; unfold compKyberEncaps at hct hss
  split at hct <;> rename_i h0
  · simp only [h0, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt0_length] at hct; rw [drop_append_of_eq_length compKyberCt0_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct0]
  · split at hct <;> rename_i h1
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt1_length] at hct; rw [drop_append_of_eq_length compKyberCt1_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct1]
    · split at hct <;> rename_i h2
      · simp only [h0, h1, h2, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compKyberCt2_length] at hct; rw [drop_append_of_eq_length compKyberCt2_length] at hss; rw [← hct, ← hss, compKyberDecaps_ct2]
      · simp only [h0, h1, h2, Bool.false_eq_true, ↓reduceIte] at hss; rw [take_append_of_eq_length compDefaultKyberCt_length] at hct; rw [drop_append_of_eq_length compDefaultKyberCt_length] at hss; rw [← hct, ← hss, compKyberDecaps_default]
end Symbolic.BugInjection.Proofs.Common443.CompI0Laws
