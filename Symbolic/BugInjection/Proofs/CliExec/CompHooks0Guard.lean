/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.Model -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref -- proof-setup: allow-public-import
meta import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3OverlapGates
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.CodecInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.InputsInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongr
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongrD7
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.XIndep
public import Symbolic.Proofs.SpecLemmas.ElfBindingSha256 -- proof-setup: allow-public-import

/-!
# `Sha256AgreesOnInput compHooks0` Witness Guard Lemmas

Reduces `Sha256AgreesOnInput compHooks0 i` (over all matching `PqParty` states `st` in
`PqxdhPartyInSpecDomain`) on concrete witness `Inputs` to decidable model equality on the unique
concrete party state `st₀` whose encoded directory matches `i`.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
open scoped ProofLib.ProgramReflection
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (ShaState keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey GhostState IdentityKey InvalidMessageReason InvalidSessionReason KeyPair
  MessageKeyGenerator MessageType PrivateKey PublicKey ReceiverChain SenderChain SessionState
  SignalMessage SignalProtocolError initializeInitiatorSession initializeRecipientSession
)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressBlock_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref (
  beU32OfBytes sha256BigSigma0 sha256BigSigma1 sha256Ch sha256CompressBlock sha256K sha256Maj
  sha256Round sha256Schedule sha256SmallSigma0 sha256SmallSigma1
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure)
open CryptoVerification.E2E (
  LocalIdentity PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras ResponderPreKeySecrets
  UnreachedPqxdhPrimitives acceptInput blockLevelPrims djbKey encodeRecordUnderExtras initiateInput
  initiateState initiateTapeLen initiatorRecordExtras keyPairOf ofU8 partyAddressName partyDeviceId
  partyIdentityKey pqxdhSessionParams pqxdhSpqrSession recvPrekeyState responderRecordExtras u8Vec
  wirePrekey wireWhisper
)
open CryptoVerification.SignalSession (
  Cmd Inputs PqParty PqSessionMatches PqxdhPartyInSpecDomain addressFile baseKeysBytes baseKeysFile
  bundleDir coinsFile encodeDir fileCapBytes filesOf identityFile identityKeyPairFile
  kyberRecordBytes lastResortKyberPreKeyFile le32 oneTimeKyberPreKeyFile oneTimePreKeyFile
  oneTimeRecordBytes partyAddress partyDirs preKeysNamedBy pqInitInputs pqInitModel pqInputs
  pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel publicBundleOf
  registrationIdFile sessionFile signedPreKeyFile signedRecordBytes textBytes
)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (PreKeyFields leBytes parsePreKey)
open DY.Libsignal.Composed.Refinement.Cli (
  InputsEquiv PqFieldsMatch Sha256AgreesOnInput bundleFilesFlat_publicBundleOf parseBundleFiles
  parseBundleFiles_publicBundleOf pqInitInputsF pqRecvMatchingFieldsModel
  pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none preKeyOfBody?
  preKeyOfBody?_bytes_of_parsePreKey_some preKeyOfBody?_some_inv publicBundleOf_injective
  shaStateOfBytes_shaStateBytes
)
open DY.Libsignal.Composed.Refinement.Cli.SDet (
  PqPartyEquiv PqSessionEquiv initiateState_xindep inputsEquiv_pqInitInputs_pqRecvInputs_false
  inputsEquiv_pqInitInputs_pqSendInputs_false inputsEquiv_pqSendInputs_extract
  inputsEquiv_pqSendInputs_pqRecvInputs_false keysFor_eq_of_pqPartyEquiv pqInitInputs_pqInitInputsF_extract
  pqInitModel_xindep pqRecvInputs_pqInitInputsF_false pqRecvPrekeyModel_xindep
  pqSendInputs_pqInitInputsF_false recvPrekeyState_xindep
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0 (bytesToNat)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase (
  ShaAgreesOnInput pqPartyEquiv_clearSession pqPartyEquiv_of_weakWF withShaF
)

public section
set_option autoImplicit false

/-- Dummy unreached PQXDH primitives witness (all model transitions are `X`-independent). -/
@[expose] def dummyX : UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }
/-- Concrete `PEParams` for `compHooks0`. -/
@[expose] def compP0 : PEParams := ⟨compHooks0.C, compHooks0.Q⟩
/-- Concrete `PEParams` for `withRealSha256 compHooks0`. -/
@[expose] def compP0Real : PEParams := withShaF sha256Compress compP0

/-! ## Forced-`BitVec 32` SHA-256 Compression for Kernel Evaluation -/
@[expose] def withForcedNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) n (k 0) (fun m => k (Nat.add m 1))
private theorem withForcedNat_eq {α : Type} (n : Nat) (k : Nat → α) : withForcedNat n k = k n := by
  cases n <;> rfl
@[expose] def withForcedBV32 {α : Type} (x : BitVec 32) (k : BitVec 32 → α) : α :=
  withForcedNat x.toNat (fun n => k (BitVec.ofNat 32 n))
private theorem withForcedBV32_eq {α : Type} (x : BitVec 32) (k : BitVec 32 → α) :
    withForcedBV32 x k = k x := by
  unfold withForcedBV32; rw [withForcedNat_eq]
  rw [show BitVec.ofNat 32 x.toNat = x from
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])]
@[expose] def xor4Table : Nat :=
  0x123456789abcdef1032547698badcfe23016745ab89efcd32107654ba98fedc45670123cdef89ab54761032dcfe98ba67452301efcdab8976543210fedcba9889abcdef0123456798badcfe10325476ab89efcd23016745ba98fedc32107654cdef89ab45670123dcfe98ba54761032efcdab8967452301fedcba9876543210
@[expose] def and4Table : Nat :=
  0xfedcba9876543210eeccaa8866442200dcdc989854541010cccc888844440000ba98ba9832103210aa88aa88220022009898989810101010888888880000000076543210765432106644220066442200545410105454101044440000444400003210321032103210220022002200220010101010101010100000000000000000
@[expose] def xor4 (x y : Nat) : Nat := Nat.mod (Nat.div xor4Table (Nat.pow 16 (Nat.add (Nat.mul x 16) y))) 16
@[expose] def and4 (x y : Nat) : Nat := Nat.mod (Nat.div and4Table (Nat.pow 16 (Nat.add (Nat.mul x 16) y))) 16
private theorem xor4_and4_table_ok :
    ((List.range 16).all fun x => (List.range 16).all fun y =>
      decide (xor4 x y = x ^^^ y) && decide (and4 x y = x &&& y)) = true := by decide +kernel
private theorem xor4_eq {x y : Nat} (hx : x < 16) (hy : y < 16) : xor4 x y = x ^^^ y :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp xor4_and4_table_ok x (List.mem_range.mpr hx))
      y (List.mem_range.mpr hy))).1
private theorem and4_eq {x y : Nat} (hx : x < 16) (hy : y < 16) : and4 x y = x &&& y :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp xor4_and4_table_ok x (List.mem_range.mpr hx))
      y (List.mem_range.mpr hy))).2

@[expose] def nibbleCombine (op : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => Nat.add (op (Nat.mod a 16) (Nat.mod b 16))
      (Nat.mul 16 (nibbleCombine op k (Nat.div a 16) (Nat.div b 16)))

private theorem nibbleCombine_xor_eq :
    ∀ (k a b : Nat), a < 16 ^ k → b < 16 ^ k → nibbleCombine xor4 k a b = a ^^^ b
  | 0, a, b, ha, hb => by cases (show a = 0 by omega); cases (show b = 0 by omega); rfl
  | k + 1, a, b, ha, hb => by
    unfold nibbleCombine; change xor4 (a % 16) (b % 16) + 16 * nibbleCombine xor4 k (a / 16) (b / 16) = a ^^^ b
    have ha' : a / 16 < 16 ^ k := by rw [Nat.pow_succ] at ha; omega
    have hb' : b / 16 < 16 ^ k := by rw [Nat.pow_succ] at hb; omega
    rw [xor4_eq (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), nibbleCombine_xor_eq k (a / 16) (b / 16) ha' hb']
    have hlo : (a % 16) ^^^ (b % 16) = (a ^^^ b) % 16 := (Nat.xor_mod_two_pow (a := a) (b := b) (n := 4)).symm
    have hhi : (a / 16) ^^^ (b / 16) = (a ^^^ b) / 16 := by
      simpa [Nat.shiftRight_eq_div_pow] using (Nat.shiftRight_xor_distrib (a := a) (b := b) (i := 4)).symm
    omega

private theorem nibbleCombine_and_eq :
    ∀ (k a b : Nat), a < 16 ^ k → b < 16 ^ k → nibbleCombine and4 k a b = a &&& b
  | 0, a, b, ha, hb => by cases (show a = 0 by omega); cases (show b = 0 by omega); rfl
  | k + 1, a, b, ha, hb => by
    unfold nibbleCombine; change and4 (a % 16) (b % 16) + 16 * nibbleCombine and4 k (a / 16) (b / 16) = a &&& b
    have ha' : a / 16 < 16 ^ k := by rw [Nat.pow_succ] at ha; omega
    have hb' : b / 16 < 16 ^ k := by rw [Nat.pow_succ] at hb; omega
    rw [and4_eq (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), nibbleCombine_and_eq k (a / 16) (b / 16) ha' hb']
    have hlo : (a % 16) &&& (b % 16) = (a &&& b) % 16 := (Nat.and_mod_two_pow (a := a) (b := b) (n := 4)).symm
    have hhi : (a / 16) &&& (b / 16) = (a &&& b) / 16 := by
      simpa [Nat.shiftRight_eq_div_pow] using (Nat.shiftRight_and_distrib (a := a) (b := b) (i := 4)).symm
    omega

@[expose] def nibble8 (op : Nat → Nat → Nat) (a b : Nat) : Nat :=
  let a1 := Nat.div a 16; let b1 := Nat.div b 16; let a2 := Nat.div a1 16; let b2 := Nat.div b1 16
  let a3 := Nat.div a2 16; let b3 := Nat.div b2 16; let a4 := Nat.div a3 16; let b4 := Nat.div b3 16
  let a5 := Nat.div a4 16; let b5 := Nat.div b4 16; let a6 := Nat.div a5 16; let b6 := Nat.div b5 16
  let a7 := Nat.div a6 16; let b7 := Nat.div b6 16
  Nat.add (op (Nat.mod a 16) (Nat.mod b 16))
    (Nat.mul 16 (Nat.add (op (Nat.mod a1 16) (Nat.mod b1 16))
      (Nat.mul 16 (Nat.add (op (Nat.mod a2 16) (Nat.mod b2 16))
        (Nat.mul 16 (Nat.add (op (Nat.mod a3 16) (Nat.mod b3 16))
          (Nat.mul 16 (Nat.add (op (Nat.mod a4 16) (Nat.mod b4 16))
            (Nat.mul 16 (Nat.add (op (Nat.mod a5 16) (Nat.mod b5 16))
              (Nat.mul 16 (Nat.add (op (Nat.mod a6 16) (Nat.mod b6 16))
                (Nat.mul 16 (Nat.add (op (Nat.mod a7 16) (Nat.mod b7 16)) (Nat.mul 16 0)))))))))))))))
private theorem nibble8_eq (op : Nat → Nat → Nat) (a b : Nat) : nibble8 op a b = nibbleCombine op 8 a b := rfl

@[expose] def xor32Fast (x y : BitVec 32) : BitVec 32 :=
  withForcedNat x.toNat fun a => withForcedNat y.toNat fun b => BitVec.ofNat 32 (nibble8 xor4 a b)
@[expose] def and32Fast (x y : BitVec 32) : BitVec 32 :=
  withForcedNat x.toNat fun a => withForcedNat y.toNat fun b => BitVec.ofNat 32 (nibble8 and4 a b)
@[expose] def not32Fast (x : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (Nat.sub 4294967295 x.toNat)
@[expose] def shr32Fast (x : BitVec 32) (s : Nat) : BitVec 32 := BitVec.ofNat 32 (Nat.div x.toNat (Nat.pow 2 s))
@[expose] def rotr32Fast (x : BitVec 32) (s : Nat) : BitVec 32 :=
  withForcedNat x.toNat fun a => let p := Nat.pow 2 s
    BitVec.ofNat 32 (Nat.add (Nat.div a p) (Nat.mul (Nat.mod a p) (Nat.pow 2 (Nat.sub 32 s))))

private theorem xor32Fast_eq (x y : BitVec 32) : xor32Fast x y = x ^^^ y := by
  apply BitVec.eq_of_toNat_eq
  unfold xor32Fast
  rw [withForcedNat_eq, withForcedNat_eq, nibble8_eq, BitVec.toNat_ofNat,
      nibbleCombine_xor_eq 8 x.toNat y.toNat x.isLt y.isLt, BitVec.toNat_xor]
  exact Nat.mod_eq_of_lt (x ^^^ y).isLt

private theorem and32Fast_eq (x y : BitVec 32) : and32Fast x y = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  unfold and32Fast
  rw [withForcedNat_eq, withForcedNat_eq, nibble8_eq, BitVec.toNat_ofNat,
      nibbleCombine_and_eq 8 x.toNat y.toNat x.isLt y.isLt, BitVec.toNat_and]
  exact Nat.mod_eq_of_lt (x &&& y).isLt

private theorem not32Fast_eq (x : BitVec 32) : not32Fast x = ~~~x := by
  change BitVec.ofNat 32 (4294967295 - x.toNat) = ~~~x; bv_omega

private theorem shr32Fast_eq (x : BitVec 32) (s : Nat) : shr32Fast x s = x >>> s := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 32 (x.toNat / 2 ^ s)).toNat = (x >>> s).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

private theorem rotr32Fast_eq (x : BitVec 32) (s : Nat) (hs : 0 < s ∧ s < 32) :
    rotr32Fast x s = x.rotateRight s := by
  unfold rotr32Fast; rw [withForcedNat_eq]
  change BitVec.ofNat 32 (x.toNat / (2 ^ s) + (x.toNat % (2 ^ s)) * (2 ^ (32 - s))) = x.rotateRight s
  apply BitVec.eq_of_toNat_eq
  have hmod : s % 32 = s := Nat.mod_eq_of_lt hs.2
  rw [BitVec.toNat_ofNat, BitVec.toNat_rotateRight, hmod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hpow : (2 : Nat) ^ 32 = 2 ^ s * 2 ^ (32 - s) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hs.2)]
  have h1 : x.toNat / 2 ^ s < 2 ^ (32 - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), Nat.mul_comm, ← hpow]; exact x.isLt
  have hlt : x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (32 - s) < 2 ^ 32 := by
    have h2 := Nat.le_sub_one_of_lt (Nat.mod_lt x.toNat (Nat.two_pow_pos s))
    calc x.toNat / 2 ^ s + (x.toNat % 2 ^ s) * 2 ^ (32 - s)
      _ < 2 ^ (32 - s) + (2 ^ s - 1) * 2 ^ (32 - s) := Nat.add_lt_add_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
      _ = (1 + (2 ^ s - 1)) * 2 ^ (32 - s) := by rw [Nat.add_mul, Nat.one_mul]
      _ = 2 ^ s * 2 ^ (32 - s) := by rw [Nat.add_sub_cancel' (Nat.two_pow_pos s)]
      _ = 2 ^ 32 := hpow.symm
  have hm2 : (x.toNat * 2 ^ (32 - s)) % 2 ^ 32 = (x.toNat % 2 ^ s) * 2 ^ (32 - s) := by
    have hdiv : x.toNat = 2 ^ s * (x.toNat / 2 ^ s) + x.toNat % 2 ^ s := (Nat.div_add_mod _ _).symm
    conv_lhs => rw [hdiv, Nat.add_mul, Nat.mul_right_comm (2 ^ s), ← hpow, Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt)
  rw [hm2, Nat.mod_eq_of_lt hlt]
  have hdisj : (x.toNat / 2 ^ s) &&& ((x.toNat % 2 ^ s) * 2 ^ (32 - s)) = 0 := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 32 - s
    · have hlow : ((x.toNat % 2 ^ s) * 2 ^ (32 - s)).testBit i = false := by
        rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]; simp [Nat.not_le_of_lt hi]
      rw [hlow, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))), Bool.false_and]
  have ha_lt : x.toNat / 2 ^ s < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
  have hb_lt : (x.toNat % 2 ^ s) * 2 ^ (32 - s) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt
  have hand0 : (BitVec.ofNat 32 (x.toNat / 2 ^ s) &&&
      BitVec.ofNat 32 ((x.toNat % 2 ^ s) * 2 ^ (32 - s))) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt, hdisj]; rfl
  have h := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ hand0)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt, Nat.mod_eq_of_lt hlt] at h
  exact h

@[expose] def beU32Fast (bs : List (BitVec 8)) : BitVec 32 :=
  match bs with
  | [b0, b1, b2, b3] => BitVec.ofNat 32 (b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat)
  | _ => beU32OfBytes bs

private theorem beU32Fast_eq (bs : List (BitVec 8)) : beU32Fast bs = beU32OfBytes bs := by
  have step (acc : BitVec 32) (b : BitVec 8) (hacc : acc.toNat < 2 ^ 24) :
      (acc <<< 8 ||| b.zeroExtend 32).toNat = acc.toNat * 256 + b.toNat := by
    have hsh : (acc <<< 8).toNat = acc.toNat * 256 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
    have hze : (b.zeroExtend 32).toNat = b.toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
    have hand : ((acc <<< 8) &&& b.zeroExtend 32) = 0#32 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, hsh, hze]; change _ = 0
      apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]; by_cases hi : i < 8
      · have h1 : (acc.toNat * 256).testBit i = false := by
          rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]; simp [Nat.not_le_of_lt hi]
        rw [h1, Bool.false_and]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))), Bool.and_false]
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, hsh, hze]
    exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
  unfold beU32Fast; split
  · next b0 b1 b2 b3 =>
    apply BitVec.eq_of_toNat_eq; unfold beU32OfBytes; simp only [List.foldl_cons, List.foldl_nil]
    have hz : (0#32).toNat = 0 := rfl
    have s0 := step 0#32 b0 (by decide)
    have s1 := step (0#32 <<< 8 ||| b0.zeroExtend 32) b1 (by rw [s0, hz]; have := b0.isLt; omega)
    have s2 := step ((0#32 <<< 8 ||| b0.zeroExtend 32) <<< 8 ||| b1.zeroExtend 32) b2
      (by rw [s1, s0, hz]; have := b0.isLt; have := b1.isLt; omega)
    have s3 := step (((0#32 <<< 8 ||| b0.zeroExtend 32) <<< 8 ||| b1.zeroExtend 32) <<< 8 ||| b2.zeroExtend 32) b3
      (by rw [s2, s1, s0, hz]; have := b0.isLt; have := b1.isLt; have := b2.isLt; omega)
    rw [BitVec.toNat_ofNat, s3, s2, s1, s0, hz]
    have hlt : b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat < 2 ^ 32 := by
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]; omega
  · rfl
@[expose] def smallSigma0Fast (x : BitVec 32) : BitVec 32 := xor32Fast (xor32Fast (rotr32Fast x 7) (rotr32Fast x 18)) (shr32Fast x 3)
@[expose] def smallSigma1Fast (x : BitVec 32) : BitVec 32 := xor32Fast (xor32Fast (rotr32Fast x 17) (rotr32Fast x 19)) (shr32Fast x 10)
@[expose] def bigSigma0Fast (x : BitVec 32) : BitVec 32 := xor32Fast (xor32Fast (rotr32Fast x 2) (rotr32Fast x 13)) (rotr32Fast x 22)
@[expose] def bigSigma1Fast (x : BitVec 32) : BitVec 32 := xor32Fast (xor32Fast (rotr32Fast x 6) (rotr32Fast x 11)) (rotr32Fast x 25)
@[expose] def chFast (x y z : BitVec 32) : BitVec 32 := xor32Fast (and32Fast x y) (and32Fast (not32Fast x) z)
@[expose] def majFast (x y z : BitVec 32) : BitVec 32 := xor32Fast (xor32Fast (and32Fast x y) (and32Fast x z)) (and32Fast y z)
@[expose] def sha256ScheduleFast (w16 : List (BitVec 32)) : List (BitVec 32) :=
  (List.range 48).foldl (fun ws i =>
    withForcedBV32 (ws.getD i 0#32 + smallSigma0Fast (ws.getD (i + 1) 0#32) +
      ws.getD (i + 9) 0#32 + smallSigma1Fast (ws.getD (i + 14) 0#32)) fun next => ws ++ [next])
    ((w16.take 16).map fun w => withForcedBV32 w id)
@[expose] def sha256RoundFast (st : List (BitVec 32)) (k w : BitVec 32) : List (BitVec 32) :=
  match st with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := h + bigSigma1Fast e + chFast e f g + k + w; let t2 := bigSigma0Fast a + majFast a b c
    withForcedBV32 (t1 + t2) fun a' => withForcedBV32 (d + t1) fun e' => [a', a, b, c, e', e, f, g]
  | _ =>
    let a := st.getD 0 0#32; let b := st.getD 1 0#32; let c := st.getD 2 0#32; let d := st.getD 3 0#32
    let e := st.getD 4 0#32; let f := st.getD 5 0#32; let g := st.getD 6 0#32; let h := st.getD 7 0#32
    let t1 := h + bigSigma1Fast e + chFast e f g + k + w; let t2 := bigSigma0Fast a + majFast a b c
    withForcedBV32 (t1 + t2) fun a' => withForcedBV32 (d + t1) fun e' => [a', a, b, c, e', e, f, g]
@[expose] def sha256CompressBlockFast (st : List (BitVec 32)) (block : List (BitVec 8)) : List (BitVec 32) :=
  let st0 := st.map fun w => withForcedBV32 w id
  let ws := sha256ScheduleFast ((List.range 16).map fun i => beU32Fast ((block.drop (4 * i)).take 4))
  let final := (List.range 64).foldl (fun cur i => sha256RoundFast cur (sha256K.getD i 0#32) (ws.getD i 0#32)) st0
  (List.range 8).map fun i => withForcedBV32 (st0.getD i 0#32 + final.getD i 0#32) id
private theorem sha256CompressBlockFast_eq (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256CompressBlockFast st block = sha256CompressBlock st block := by
  have hs0 : smallSigma0Fast = sha256SmallSigma0 := by
    funext x; unfold smallSigma0Fast sha256SmallSigma0
    simp only [xor32Fast_eq, shr32Fast_eq, rotr32Fast_eq x 7 (by decide), rotr32Fast_eq x 18 (by decide)]
  have hs1 : smallSigma1Fast = sha256SmallSigma1 := by
    funext x; unfold smallSigma1Fast sha256SmallSigma1
    simp only [xor32Fast_eq, shr32Fast_eq, rotr32Fast_eq x 17 (by decide), rotr32Fast_eq x 19 (by decide)]
  have hb0 : bigSigma0Fast = sha256BigSigma0 := by
    funext x; unfold bigSigma0Fast sha256BigSigma0
    simp only [xor32Fast_eq, rotr32Fast_eq x 2 (by decide), rotr32Fast_eq x 13 (by decide), rotr32Fast_eq x 22 (by decide)]
  have hb1 : bigSigma1Fast = sha256BigSigma1 := by
    funext x; unfold bigSigma1Fast sha256BigSigma1
    simp only [xor32Fast_eq, rotr32Fast_eq x 6 (by decide), rotr32Fast_eq x 11 (by decide), rotr32Fast_eq x 25 (by decide)]
  have hch : chFast = sha256Ch := by funext x y z; unfold chFast sha256Ch; simp only [xor32Fast_eq, and32Fast_eq, not32Fast_eq]
  have hmaj : majFast = sha256Maj := by funext x y z; unfold majFast sha256Maj; simp only [xor32Fast_eq, and32Fast_eq]
  have hsched : ∀ w16, sha256ScheduleFast w16 = sha256Schedule w16 := by
    intro w16; unfold sha256ScheduleFast sha256Schedule; simp only [withForcedBV32_eq, List.map_id, hs0, hs1]
  have hround : sha256RoundFast = sha256Round := by
    funext cur k w; unfold sha256RoundFast sha256Round; split
    · simp only [withForcedBV32_eq, hb0, hb1, hch, hmaj]; rfl
    · simp only [withForcedBV32_eq, hb0, hb1, hch, hmaj]
  unfold sha256CompressBlockFast sha256CompressBlock
  simp only [withForcedBV32_eq, List.map_id, beU32Fast_eq, hsched, hround]; rfl

@[expose] def sha256CompressFast (st : ShaState) (block : List (BitVec 8)) : ShaState :=
  ⟨sha256CompressBlockFast st.toList block, by rw [sha256CompressBlockFast_eq]; exact sha256CompressBlock_length st.toList block⟩

private theorem sha256CompressFast_eq_spqr : sha256CompressFast = sha256Compress := by
  rw [← LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge.sha256CompressState_eq_spqrSha256Compress]
  funext st block; apply List.Vector.eq; exact sha256CompressBlockFast_eq st.toList block

/-! ## Certified Witness SHA-256 Table Cache + Fallback to `sha256CompressFast` -/

theorem leBytes_bytesToNat : ∀ bs : HwBytes, leBytes bs.length (bytesToNat bs) = bs
  | [] => rfl
  | b :: bs => by
    have h1 : BitVec.ofNat 8 (b.toNat + 256 * bytesToNat bs) = b := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    have h2 : (b.toNat + 256 * bytesToNat bs) / 256 = bytesToNat bs := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt b.isLt, Nat.zero_add]
    simp only [List.length_cons, leBytes, bytesToNat, h1, h2, leBytes_bytesToNat bs]

@[expose] def witnessSha256Rows : List (Nat × Nat × Nat) := [
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x36363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636363636, 0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c, 0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f),
  (0xf8e04e32824a932ba392418164e5750fdf1228ea90daf2a09725214ff454dead, 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e),
  (0xc87493f4418f30a35731c97400f76c573c634ddb3f392a266ef10d36f057716e, 0x6b77c765b6556603b9ce3789d8135f9f017ce167088d37af655befa4f2f390e354151271fa3dd6f78b354f259b6c06bad17e64fc6967b26f10367cff0436cdf3, 0x56c78a787c1827d8b2fcd49199c368904f7bed8a33e0a607fbb7a3bc5ef17819),
  (0x56c78a787c1827d8b2fcd49199c368904f7bed8a33e0a607fbb7a3bc5ef17819, 0x700000000000000000000000000000000000000000000000000000000008086e81a17be5801293d514fe3c93d60943e523b05dc2096ee371824900b0cace4, 0x3ad8cda4837097c45eab082fecbaf978c4b99e3cde578caafd9d2bc7ce313f93),
  (0x361d45a6deb82818753434b08e043a725dd8246737c9c5387abb6477d385480f, 0x3000000000000000000000000000000000000000000000000000000000080a4cdd83ac49770832f08ab5e78f9baec3c9eb9c4aa8c57dec72b9dfd933f31ce, 0x735919ec8086b0842db228a015f4c77c2e9b97e6f64356e90579e0b6df22c6d9),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636da2f6f45b286b0b6961e841b4af1c223d0a1ad18df6075c080d64f33eff014e9, 0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5cb045052fd8ecdadcfc74ee71209ba849bacbc772b50a1faaeabc2559859a7e83, 0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0x56d2843745597d28215dea6829baf9bb38a501fd24fabf1b79a650bb87c92bdb),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x30000000000000000000000000000000000000000000000000000000000803784d256287d594568ea5d21bbf9ba29fd01a5381bbffa24bb50a679db2bc987, 0x4c11ee612318627c98c85d1d313e499ca37c459e7faa250a3508b431c9867e50),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685761ee114c7c6218231d5dc8989c493e319e457ca30a25aa7f31b40835507e86c9, 0x7d98713ce929e25f72bc96e31ab42a99a1ac8cf4869112b28be58505465142d5),
  (0x7d98713ce929e25f72bc96e31ab42a99a1ac8cf4869112b28be58505465142d5, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0x7899a72c049d6b0338c2afc67e2b7bca9970107ace192ccf0024a198e3fe10b9),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x30000000000000000000000000000000000000000000000000000000000802ca79978036b9d04c6afc238ca7b2b7e7a107099cf2c19ce98a12400b910fee3, 0x86734de4b6588902755fbb4ee6b02413121f627d32a6ee0e2c7be763afe3ec71),
  (0x408217d3733212ba6a026aaad57ea749876bb033a693e7a0ccc3657b1ca0046f, 0x54535952435f3635322d4148535f3931353532585f7478655472657073696857e44d7386028958b64ebb5f751324b0e67d621f120eeea63263e77b2c71ece3af, 0x3eb96befd438fb5b8aaadff31754e6b48098814f723b41f0a9d81f77c7e5268e),
  (0x3eb96befd438fb5b8aaadff31754e6b48098814f723b41f0a9d81f77c7e5268e, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0xad75ae2967a3d96b2d37e2d5abad8da4e8e2f1c18d570145bbf6756c203a523b),
  (0xd5d8774008ad0a31b7e137d1d9efe989155cafe509c6c883ee9074970f284a3b, 0x300000000000000000000000000000000000000000000000000000000008029ae75ad6bd9a367d5e2372da48dadabc1f1e2e84501578d6c75f6bb3b523a20, 0xd7c7b14df20e3fcb714f4cddd439dab31730668aa0aa4292121d346c11fbe377),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636015fef64034a48334c279aa2fb44f5c8fb09b3d0cbcc4b9ed713731589745a9c, 0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c6b35850e69202259264df0c8912e9fa29163d9baa1a621f4bd79197fe31e30f6, 0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0xb6643310f5925d3b8965c44dd18d859d061dd9f6a6bccf54a3c6e2bffecd7aee),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x3000000000000000000000000000000000000000000000000000000000080103364b63b5d92f54dc465899d858dd1f6d91d0654cfbca6bfe2c6a3ee7acdfe, 0x323099ff6cd65a66ba572b696e3db41d51787234b57794be5809700574e9af1a),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x54535952435f3635322d4148535f3931353532585f7478655472657073696857ff993032665ad66c692b57ba1db43d6e34727851be9477b5057009581aafe974, 0x851f499d0d1c5be464df166df59c09963d141c457fef2d4c4aba78fcb2ea98b2),
  (0x851f499d0d1c5be464df166df59c09963d141c457fef2d4c4aba78fcb2ea98b2, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0x37eca9479e0e04ff7ea3a70658c5db4b4af8b094ba715f65abf44d6519479357),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x300000000000000000000000000000000000000000000000000000000008047a9ec37ff040e9e06a7a37e4bdbc55894b0f84a655f71ba654df4ab57934719, 0xe62fb2057b34543c308e34e80aa3f0fcad26166bf82b8053c7f73c10f6f89823),
  (0xd1e60d9c601bba16f8689a2b6dcf54459d877a5c8b603f079fd3e94740fedd2f, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685705b22fe63c54347be8348e30fcf0a30a6b1626ad53802bf8103cf7c72398f8f6, 0x11277c05183dd18a67180fdcdb4d9a2e4c0857e3ace287e3e0983c5f05ad61eb),
  (0x11277c05183dd18a67180fdcdb4d9a2e4c0857e3ace287e3e0983c5f05ad61eb, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0x27cd0f39007397f2d59bef673b9e78840192f22cc64450b60ba1563dbeb3370c),
  (0x61bf52fd96a546fe85c50e48c281b3248dc2bb536fb86a99028686d234e3893c, 0x3000000000000000000000000000000000000000000000000000000000080390fcd27f297730067ef9bd584789e3b2cf29201b65044c63d56a10b0c37b3be, 0x1b539b57e4d4e937e7bb1ba3b8a1de4abc8e5b83e711ce8ec3ed2ae8c39436e6),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x3636363636363636363636363636363636363636363636363636363636363636f4a31bef5a4b0e207afdcd9ae3faa6b6e88ed4887442368052dc11ea78b441b3, 0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe),
  (0x5be0cd191f83d9ab9b05688c510e527fa54ff53a3c6ef372bb67ae856a09e667, 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c9ec971853021644a1097a7f08990ccdc82e4bee21e285cea38b67b8012de2bd9, 0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x780300000000000000000000000000008001343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857, 0xae35e819b7d688398eef128ec5809757f4afe26c59dfe655dbdce3f868cf9d7e),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x300000000000000000000000000000000000000000000000000000000008019e835ae3988d6b78e12ef8e579780c56ce2aff455e6df59f8e3dcdb7e9dcf68, 0xa0e4b941eee905643ae23fcff4659b0c85a7f23ebde11134b8153d77b1ec4fe8),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685741b9e4a06405e9eecf3fe23a0c9b65f43ef2a7853411e1bd773d15b8e84fecb1, 0x380768761567365901d4def7c5d60f403fc045515692e406ccb67e51bde3ba00),
  (0x380768761567365901d4def7c5d60f403fc045515692e406ccb67e51bde3ba00, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008002343230312d524542594b2d534c41, 0xf2387d77269f85516af77795219a67327c8f593f4767eb234d75061da7923da2),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x3000000000000000000000000000000000000000000000000000000000080777d38f251859f269577f76a32679a213f598f7c23eb67471d06754da23d92a7, 0x3e78f157ce9e2e555a26b01e73782b6ae99ea32bb5cf09c0274cdae263992812),
  (0x75c8776b8387705fe090db00d4f446035e1bb2396602de38748a52826e189bbe, 0x54535952435f3635322d4148535f3931353532585f747865547265707369685757f1783e552e9ece1eb0265a6a2b78732ba39ee9c009cfb5e2da4c2712289963, 0x431dee2e0f8196c1eebda95bdb2d4eb9967a2b0dcabfbd19cd02ab893cac733f),
  (0x431dee2e0f8196c1eebda95bdb2d4eb9967a2b0dcabfbd19cd02ab893cac733f, 0x7804000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008003343230312d524542594b2d534c41, 0xca0e492a0ddc18dca80b50c0feabd829e2c321f23c007827c599fb2711814968),
  (0xbe66d6018666cefb7c1ac9ff82dd8841c604d4cdacca1d70fe3622903bfbecbf, 0x30000000000000000000000000000000000000000000000000000000000802a490ecadc18dc0dc0500ba829d8abfef221c3e22778003c27fb99c568498111, 0x1fbddc11374a5dbf69484c29d9e9950614e418c813211cf1c4561ef4e054cb8a)
]

private def rowCertOk (r : Nat × Nat × Nat) : Bool :=
  shaStateBytes (sha256CompressFast (shaStateOfBytes (leBytes 32 r.1)) (leBytes 64 r.2.1)) == leBytes 32 r.2.2
private theorem witnessSha256Rows_ok : witnessSha256Rows.all rowCertOk = true := by rfl_kernel

@[expose] def sha256CompressTabled (st : ShaState) (blk : List (BitVec 8)) : ShaState :=
  let stBytes := shaStateBytes st
  if stBytes.length == 32 && blk.length == 64 then
    let kSt := bytesToNat stBytes
    let kBlk := bytesToNat blk
    match witnessSha256Rows.find? (fun r => (r.1 == kSt) && (r.2.1 == kBlk)) with
    | some (_, _, outNat) => shaStateOfBytes (leBytes 32 outNat)
    | none => sha256CompressFast st blk
  else
    sha256CompressFast st blk

theorem sha256CompressTabled_eq_spqr : sha256CompressTabled = sha256Compress := by
  rw [← sha256CompressFast_eq_spqr]
  funext st blk
  unfold sha256CompressTabled
  dsimp only
  split_ifs with hlen
  · obtain ⟨hl1, hl2⟩ := (Bool.and_eq_true _ _).mp hlen
    have hst_len : (shaStateBytes st).length = 32 := beq_iff_eq.mp hl1
    have hblk_len : blk.length = 64 := beq_iff_eq.mp hl2
    cases hfind : witnessSha256Rows.find?
        (fun r => (r.1 == bytesToNat (shaStateBytes st)) && (r.2.1 == bytesToNat blk)) with
    | none => rfl
    | some r =>
      rcases r with ⟨rSt, rBlk, rOut⟩
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some hfind
      obtain ⟨he1, he2⟩ := (Bool.and_eq_true _ _).mp hpred
      have hcert := List.all_eq_true.mp witnessSha256Rows_ok (rSt, rBlk, rOut) hmem
      unfold rowCertOk at hcert
      dsimp only at he1 he2 hcert ⊢
      have hst_eq : shaStateOfBytes (leBytes 32 rSt) = st := by
        rw [beq_iff_eq.mp he1, ← hst_len, leBytes_bytesToNat, shaStateOfBytes_shaStateBytes]
      have hblk_eq : leBytes 64 rBlk = blk := by
        rw [beq_iff_eq.mp he2, ← hblk_len, leBytes_bytesToNat]
      rw [hst_eq, hblk_eq] at hcert
      have hout := congrArg shaStateOfBytes (beq_iff_eq.mp hcert)
      rw [shaStateOfBytes_shaStateBytes] at hout
      exact hout.symm
  · rfl

@[expose] def compP0RealFast : PEParams := withShaF sha256CompressTabled compP0

private theorem compP0Real_eq_fast : withShaF sha256Compress compP0 = compP0RealFast := by
  unfold compP0RealFast; rw [sha256CompressTabled_eq_spqr]

/-! ## Pure-`Bool` Equality Helpers (Avoiding `Subtype` Proof Terms in Kernel `whnf`) -/

@[expose] def listEqBool {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true | x :: xs, y :: ys => eq x y && listEqBool eq xs ys | _, _ => false
private theorem eq_of_listEqBool {α : Type} {eq : α → α → Bool} (heq : ∀ {x y}, eq x y = true → x = y) :
    ∀ {xs ys : List α}, listEqBool eq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; rw [heq h1, eq_of_listEqBool heq h2]
@[expose] def optEqBool {α : Type} (eq : α → α → Bool) : Option α → Option α → Bool
  | none, none => true | some x, some y => eq x y | _, _ => false
private theorem eq_of_optEqBool {α : Type} {eq : α → α → Bool} (heq : ∀ {x y}, eq x y = true → x = y) :
    ∀ {o1 o2 : Option α}, optEqBool eq o1 o2 = true → o1 = o2
  | none, none, _ => rfl | some _, some _, h => congrArg some (heq h)
@[expose] def prodEqBool {α β : Type} (eqA : α → α → Bool) (eqB : β → β → Bool) (p q : α × β) : Bool :=
  eqA p.1 q.1 && eqB p.2 q.2
private theorem eq_of_prodEqBool {α β : Type} {eqA : α → α → Bool} {eqB : β → β → Bool}
    (hA : ∀ {x y}, eqA x y = true → x = y) (hB : ∀ {x y}, eqB x y = true → x = y)
    {p q : α × β} (h : prodEqBool eqA eqB p q = true) : p = q := by
  rcases p with ⟨a1, b1⟩; rcases q with ⟨a2, b2⟩
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; exact Prod.ext (hA h1) (hB h2)
@[expose] def exceptEqBool {ε α : Type} (eqE : ε → ε → Bool) (eqA : α → α → Bool) : Except ε α → Except ε α → Bool
  | .error e1, .error e2 => eqE e1 e2 | .ok x1, .ok x2 => eqA x1 x2 | _, _ => false
private theorem eq_of_exceptEqBool {ε α : Type} {eqE : ε → ε → Bool} {eqA : α → α → Bool}
    (hE : ∀ {e1 e2}, eqE e1 e2 = true → e1 = e2) (hA : ∀ {x1 x2}, eqA x1 x2 = true → x1 = x2) :
    ∀ {r1 r2 : Except ε α}, exceptEqBool eqE eqA r1 r2 = true → r1 = r2
  | .error _, .error _, h => congrArg Except.error (hE h) | .ok _, .ok _, h => congrArg Except.ok (hA h)
@[expose] def pubKeyEqBool (a b : PublicKey) : Bool := a.bytes.toList == b.bytes.toList
private theorem eq_of_pubKeyEqBool {a b : PublicKey} (h : pubKeyEqBool a b = true) : a = b := by
  cases a; cases b; congr; exact List.Vector.eq _ _ (beq_iff_eq.mp h)
@[expose] def privKeyEqBool (a b : PrivateKey) : Bool := a.bytes.toList == b.bytes.toList
private theorem eq_of_privKeyEqBool {a b : PrivateKey} (h : privKeyEqBool a b = true) : a = b := by
  cases a; cases b; congr; exact List.Vector.eq _ _ (beq_iff_eq.mp h)
@[expose] def keyPairEqBool (a b : KeyPair) : Bool :=
  pubKeyEqBool a.publicKey b.publicKey && privKeyEqBool a.privateKey b.privateKey
private theorem eq_of_keyPairEqBool {a b : KeyPair} (h : keyPairEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [eq_of_pubKeyEqBool h1, eq_of_privKeyEqBool h2]
@[expose] def idKeyEqBool (a b : IdentityKey) : Bool := pubKeyEqBool a.publicKey b.publicKey
private theorem eq_of_idKeyEqBool {a b : IdentityKey} (h : idKeyEqBool a b = true) : a = b := by
  cases a; cases b; exact congrArg IdentityKey.mk (eq_of_pubKeyEqBool h)
@[expose] def chainKeyEqBool (a b : ChainKey) : Bool := (a.key == b.key) && (a.index == b.index)
private theorem eq_of_chainKeyEqBool {a b : ChainKey} (h : chainKeyEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]
@[expose] def msgKeyGenEqBool (a b : MessageKeyGenerator) : Bool := (a.seed == b.seed) && (a.counter == b.counter)
private theorem eq_of_msgKeyGenEqBool {a b : MessageKeyGenerator} (h : msgKeyGenEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]
@[expose] def senderChainEqBool (a b : SenderChain) : Bool :=
  keyPairEqBool a.ratchetKey b.ratchetKey && chainKeyEqBool a.chainKey b.chainKey
private theorem eq_of_senderChainEqBool {a b : SenderChain} (h : senderChainEqBool a b = true) : a = b := by
  cases a; cases b; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; dsimp only at h1 h2
  rw [eq_of_keyPairEqBool h1, eq_of_chainKeyEqBool h2]
@[expose] def recvChainEqBool (a b : ReceiverChain) : Bool :=
  pubKeyEqBool a.senderRatchetKey b.senderRatchetKey && optEqBool chainKeyEqBool a.chainKey b.chainKey &&
  listEqBool msgKeyGenEqBool a.messageKeys b.messageKeys
private theorem eq_of_recvChainEqBool {a b : ReceiverChain} (h : recvChainEqBool a b = true) : a = b := by
  cases a; cases b
  obtain ⟨⟨h1, h2⟩, h3⟩ := (Bool.and_eq_true _ _).mp h |>.imp_left (Bool.and_eq_true _ _).mp
  dsimp only at h1 h2 h3
  rw [eq_of_pubKeyEqBool h1, eq_of_optEqBool eq_of_chainKeyEqBool h2, eq_of_listEqBool eq_of_msgKeyGenEqBool h3]
@[expose] def sessionStateEqBool (a b : SessionState HwBytes) : Bool :=
  (a.sessionVersion == b.sessionVersion) && idKeyEqBool a.localIdentity b.localIdentity &&
  optEqBool idKeyEqBool a.remoteIdentity b.remoteIdentity && (a.rootKey == b.rootKey) &&
  (a.previousCounter == b.previousCounter) && optEqBool senderChainEqBool a.senderChain b.senderChain &&
  listEqBool recvChainEqBool a.receiverChains b.receiverChains &&
  (a.pendingPreKey == b.pendingPreKey) && (a.pqRatchetState == b.pqRatchetState)
private theorem eq_of_sessionStateEqBool {a b : SessionState HwBytes} (h : sessionStateEqBool a b = true) : a = b := by
  cases a; cases b; unfold sessionStateEqBool at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [h1, eq_of_idKeyEqBool h2, eq_of_optEqBool eq_of_idKeyEqBool h3, h4, h5,
      eq_of_optEqBool eq_of_senderChainEqBool h6, eq_of_listEqBool eq_of_recvChainEqBool h7, h8, h9]
@[expose] def signalMsgEqBool (a b : SignalMessage) : Bool :=
  (a.messageVersion == b.messageVersion) && pubKeyEqBool a.senderRatchetKey b.senderRatchetKey &&
  (a.counter == b.counter) && (a.previousCounter == b.previousCounter) && (a.ciphertext == b.ciphertext) &&
  (a.pqRatchet == b.pqRatchet) && (a.addresses == b.addresses) && (a.serialized == b.serialized)
private theorem eq_of_signalMsgEqBool {a b : SignalMessage} (h : signalMsgEqBool a b = true) : a = b := by
  cases a; cases b; unfold signalMsgEqBool at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  rw [h1, eq_of_pubKeyEqBool h2, h3, h4, h5, h6, h7, h8]
@[expose] def msgTypeEqBool : MessageType → MessageType → Bool
  | .whisper, .whisper | .preKey, .preKey => true | _, _ => false
private theorem eq_of_msgTypeEqBool : ∀ {a b}, msgTypeEqBool a b = true → a = b
  | .whisper, .whisper, _ => rfl | .preKey, .preKey, _ => rfl
@[expose] def invMsgReasonEqBool : InvalidMessageReason → InvalidMessageReason → Bool
  | .tooFarInFuture, .tooFarInFuture | .pqRatchet, .pqRatchet | .macFailed, .macFailed
  | .badCiphertext, .badCiphertext | .decryptionFailed, .decryptionFailed => true | _, _ => false
private theorem eq_of_invMsgReasonEqBool : ∀ {a b}, invMsgReasonEqBool a b = true → a = b
  | .tooFarInFuture, .tooFarInFuture, _ | .pqRatchet, .pqRatchet, _ | .macFailed, .macFailed, _
  | .badCiphertext, .badCiphertext, _ | .decryptionFailed, .decryptionFailed, _ => rfl
@[expose] def invSessReasonEqBool : InvalidSessionReason → InvalidSessionReason → Bool
  | .missingSenderChain, .missingSenderChain | .missingReceiverChainKey, .missingReceiverChainKey
  | .missingRemoteIdentity, .missingRemoteIdentity | .versionTooLarge, .versionTooLarge => true | _, _ => false
private theorem eq_of_invSessReasonEqBool : ∀ {a b}, invSessReasonEqBool a b = true → a = b
  | .missingSenderChain, .missingSenderChain, _ | .missingReceiverChainKey, .missingReceiverChainKey, _
  | .missingRemoteIdentity, .missingRemoteIdentity, _ | .versionTooLarge, .versionTooLarge, _ => rfl
@[expose] def errEqBool : SignalProtocolError → SignalProtocolError → Bool
  | .invalidSessionStructure r1, .invalidSessionStructure r2 => invSessReasonEqBool r1 r2
  | .invalidKeyAgreement, .invalidKeyAgreement | .invalidState, .invalidState
  | .invalidProtobufEncoding, .invalidProtobufEncoding | .noKeyTypeIdentifier, .noKeyTypeIdentifier
  | .panic, .panic => true
  | .duplicatedMessage c1 k1, .duplicatedMessage c2 k2 => (c1 == c2) && (k1 == k2)
  | .invalidMessage t1 r1, .invalidMessage t2 r2 => msgTypeEqBool t1 t2 && invMsgReasonEqBool r1 r2
  | .ciphertextMessageTooShort n1, .ciphertextMessageTooShort n2 => n1 == n2
  | .legacyCiphertextVersion v1, .legacyCiphertextVersion v2 => v1 == v2
  | .unrecognizedCiphertextVersion v1, .unrecognizedCiphertextVersion v2 => v1 == v2
  | .badKeyType t1, .badKeyType t2 => t1 == t2 | .badKeyLength n1, .badKeyLength n2 => n1 == n2 | _, _ => false
private theorem eq_of_errEqBool : ∀ {a b}, errEqBool a b = true → a = b
  | .invalidSessionStructure _, .invalidSessionStructure _, h =>
    congrArg SignalProtocolError.invalidSessionStructure (eq_of_invSessReasonEqBool h)
  | .invalidKeyAgreement, .invalidKeyAgreement, _ | .invalidState, .invalidState, _
  | .invalidProtobufEncoding, .invalidProtobufEncoding, _
  | .noKeyTypeIdentifier, .noKeyTypeIdentifier, _ | .panic, .panic, _ => rfl
  | .duplicatedMessage _ _, .duplicatedMessage _ _, h => by
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; rw [beq_iff_eq.mp h1, beq_iff_eq.mp h2]
  | .invalidMessage _ _, .invalidMessage _ _, h => by
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h; rw [eq_of_msgTypeEqBool h1, eq_of_invMsgReasonEqBool h2]
  | .ciphertextMessageTooShort _, .ciphertextMessageTooShort _, h =>
    congrArg SignalProtocolError.ciphertextMessageTooShort (beq_iff_eq.mp h)
  | .legacyCiphertextVersion _, .legacyCiphertextVersion _, h =>
    congrArg SignalProtocolError.legacyCiphertextVersion (beq_iff_eq.mp h)
  | .unrecognizedCiphertextVersion _, .unrecognizedCiphertextVersion _, h =>
    congrArg SignalProtocolError.unrecognizedCiphertextVersion (beq_iff_eq.mp h)
  | .badKeyType _, .badKeyType _, h => congrArg SignalProtocolError.badKeyType (beq_iff_eq.mp h)
  | .badKeyLength _, .badKeyLength _, h => congrArg SignalProtocolError.badKeyLength (beq_iff_eq.mp h)

/-! ## Kernel-Reducible UTF-8, Directory Encoding, and Model Wrappers -/

@[expose] def u8StrFast (s : String) : SignalPqxdh.Bytes := s.toList.flatMap String.utf8EncodeChar
@[expose] def textBytesFast (s : String) : HwBytes := (u8StrFast s).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_loop_eq (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop; split
  · next h =>
    have hi : i < arr.size := h; have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons his]
  · next h =>
    have hi : arr.toList.length ≤ i := by have : ¬ i < arr.size := h; simp at *; omega
    rw [List.drop_eq_nil_of_le hi, List.append_nil]
termination_by arr.size - i
decreasing_by have : i < arr.size := ‹_›; omega

private theorem u8StrFast_eq (s : String) : s.toUTF8.toList = u8StrFast s := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  unfold u8StrFast; rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode]
  have h1 : (s.toList.flatMap String.utf8EncodeChar).toByteArray =
      ⟨(s.toList.flatMap String.utf8EncodeChar).toArray⟩ := by ext1; exact List.data_toByteArray
  rw [ByteArray.toList.eq_1, h1, byteArray_loop_eq]; simp

private theorem utf8_eq_fast (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = textBytesFast s := by
  unfold CryptoVerification.LibsignalTripleRatchetRepr.utf8 textBytesFast; rw [u8StrFast_eq]
private theorem textBytes_eq_fast (s : String) : textBytes s = textBytesFast s := utf8_eq_fast s
private theorem toString_seven : toString (7 : Nat) = "7" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_seven.mpr rfl]; rfl
private theorem toString_nine : toString (9 : Nat) = "9" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_nine.mpr rfl]; rfl
@[expose] def idStrFast (i : BitVec 32) : String :=
  if i = 7#32 then "7" else if i = 9#32 then "9" else toString i.toNat
private theorem idStrFast_eq (i : BitVec 32) : toString i.toNat = idStrFast i := by
  unfold idStrFast; split
  · next h => subst h; exact toString_seven
  · split
    · next _ h => subst h; exact toString_nine
    · rfl
@[expose] def partyTextFast : CryptoGames.Party → String
  | .A => "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1" | .B => "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"
private theorem partyAddress_text_eq_fast (P : CryptoGames.Party) : (partyAddress P).text = partyTextFast P := by
  have h1 : Nat.repr 1 = "1" := by rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl
  cases P <;> simp [partyAddress, CryptoVerification.SignalSession.Address.text, partyAddressName, partyTextFast, h1]

@[expose] def encodeDirFast (W : PEParams) (st : PqParty) : List (String × HwBytes) :=
  [(addressFile, textBytesFast (partyTextFast st.party)),
   (identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, le32 st.me.regId)] ++
  (match st.peerId with | some k => [(identityFile (partyAddressName st.party.other), k.serialize)] | none => []) ++
  (match st.session with
   | some (x, g) => [("sessions/" ++ partyTextFast st.party.other, encodeRecordUnderExtras (fun _ => x) g)]
   | none => []) ++
  st.signed.map (fun (i, k) => ("signed-pre-keys/" ++ idStrFast i, signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) => ("one-time-pre-keys/" ++ idStrFast i,
    match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) => ("one-time-kyber-pre-keys/" ++ idStrFast i,
    match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [("last-resort-kyber-pre-keys/" ++ idStrFast i, kyberRecordBytes i k),
     ("last-resort-kyber-pre-keys/" ++ idStrFast i ++ ".base-keys", baseKeysBytes seen)]).flatten

theorem encodeDir_eq_fast (W : PEParams) (st : PqParty) : encodeDir W st = encodeDirFast W st := by
  have htext : textBytes (partyAddress st.party).text = textBytesFast (partyTextFast st.party) := by
    rw [partyAddress_text_eq_fast, textBytes_eq_fast]
  have hsess : sessionFile (partyAddress st.party.other) = "sessions/" ++ partyTextFast st.party.other := by
    simp [sessionFile, partyAddress_text_eq_fast]
  unfold encodeDir encodeDirFast; rw [htext, hsess]
  simp only [signedPreKeyFile, oneTimePreKeyFile, oneTimeKyberPreKeyFile,
    lastResortKyberPreKeyFile, baseKeysFile, idStrFast_eq]
  cases st.peerId <;> cases st.session <;> rfl

@[expose] def pqInitInputsFast (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Inputs :=
  { argv := ["init", partyTextFast st.party.other, bundleDir], dirs := partyDirs ++ [bundleDir],
    files := encodeDirFast W st ++ (publicBundleOf b).files bundleDir ++ [(coinsFile, t.toList)], stdin := [] }
@[expose] def pqSendInputsFast (W : PEParams) (st : PqParty) (pt : List (BitVec 8))
    (coins : List.Vector (BitVec 8) 64) : Inputs :=
  { argv := ["send", partyTextFast st.party.other], dirs := partyDirs,
    files := encodeDirFast W st ++ [(coinsFile, coins.toList)], stdin := pt }
@[expose] def pqRecvInputsFast (W : PEParams) (st : PqParty) (wire : List (BitVec 8)) (rc : BitVec 256) : Inputs :=
  { argv := ["recv", partyTextFast st.party.other], dirs := partyDirs,
    files := encodeDirFast W st ++ [(coinsFile, keyToBytes32 rc)], stdin := wire }
theorem pqInitInputs_eq_fast (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : pqInitInputs W st b t = pqInitInputsFast W st b t := by
  simp only [pqInitInputs, pqInputs, pqInitInputsFast, Cmd.argv, partyAddress_text_eq_fast, encodeDir_eq_fast]
theorem pqSendInputs_eq_fast (W : PEParams) (st : PqParty) (pt : List (BitVec 8))
    (coins : List.Vector (BitVec 8) 64) : pqSendInputs W st pt coins = pqSendInputsFast W st pt coins := by
  simp only [pqSendInputs, pqInputs, pqSendInputsFast, Cmd.argv,
    partyAddress_text_eq_fast, encodeDir_eq_fast, List.append_nil]
theorem pqRecvInputs_eq_fast (W : PEParams) (st : PqParty) (wire : List (BitVec 8))
    (rc : BitVec 256) : pqRecvInputs W st wire rc = pqRecvInputsFast W st wire rc := by
  simp only [pqRecvInputs, pqInputs, pqRecvInputsFast, Cmd.argv,
    partyAddress_text_eq_fast, encodeDir_eq_fast, List.append_nil]

@[expose] def modelPrimsFast (X : UnreachedPqxdhPrimitives) (W : PEParams) : SignalPqxdh.Primitives :=
  let B := blockLevelPrims X W
  let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
  { B1 with
    sigVerify := SignalPqxdh.xeddsaVerifyRef B1, isCanonical := SignalPqxdh.isCanonicalRef B1,
    hkdfDerive96 := fun sec => SignalPqxdh.hkdfExpand96Ref B1
      (SignalPqxdh.hkdfExtractRef B1 none sec) (u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
    rootCreateChain := SignalPqxdh.rootCreateChainRef B1, chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1,
    chainKdfNext := SignalPqxdh.chainKdfNextRef B1, deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1,
    aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1, aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 }
private theorem modelPrims_eq_fast (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CryptoVerification.E2E.modelPrims X W = modelPrimsFast X W := by
  have hkdf_eq : ∀ P : SignalPqxdh.Primitives, SignalPqxdh.hkdfDerive96Ref P = fun sec =>
      SignalPqxdh.hkdfExpand96Ref P (SignalPqxdh.hkdfExtractRef P none sec)
        (u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    intro P; funext sec; simp only [SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.INFO_PQXDH, u8StrFast_eq]
  unfold CryptoVerification.E2E.modelPrims modelPrimsFast; dsimp only; rw [hkdf_eq]
@[expose] def serviceIdParseFast (input : HwBytes) : Option (Bool × List.Vector (BitVec 8) 16) :=
  let pni : HwBytes := [0x50#8, 0x4e#8, 0x49#8, 0x3a#8]
  if pni.isPrefixOf input then
    (CryptoVerification.LibsignalTripleRatchetRepr.tryParseHyphenated
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse (input.drop pni.length)).map (true, ·)
  else (CryptoVerification.LibsignalTripleRatchetRepr.tryParseHyphenated
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse input).map (false, ·)
@[expose] def serializedPartyAddressesFast (sender recipient : CryptoGames.Party) : Option HwBytes := do
  let s ← serviceIdParseFast (textBytesFast (partyAddressName sender))
  let r ← serviceIdParseFast (textBytesFast (partyAddressName recipient))
  return CryptoVerification.LibsignalTripleRatchetRepr.addrBytes s partyDeviceId ++
    CryptoVerification.LibsignalTripleRatchetRepr.addrBytes r partyDeviceId
@[expose] def pqxdhSessionParamsFast (W : PEParams) : CryptoGames.LibsignalSession.Params HwBytes HwBytes :=
  ⟨W.C, protoSignalCodec, pqxdhSpqrSession W, partyIdentityKey .A, partyIdentityKey .B,
   serializedPartyAddressesFast .A .B, serializedPartyAddressesFast .B .A⟩
private theorem pqxdhSessionParams_eq_fast (W : PEParams) : pqxdhSessionParams W = pqxdhSessionParamsFast W := by
  have hs : ∀ input, CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse input = serviceIdParseFast input := by
    intro input; simp only [CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse, serviceIdParseFast,
      CryptoVerification.LibsignalTripleRatchetRepr.pniPrefix_word]
  have ha : ∀ p q, CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse p q = serializedPartyAddressesFast p q := by
    intro p q; simp only [CryptoVerification.E2E.serializedPartyAddresses, serializedPartyAddressesFast, utf8_eq_fast, hs]
  simp only [pqxdhSessionParams, pqxdhSessionParamsFast, ha]

@[expose] def initiateCoreFast (X : UnreachedPqxdhPrimitives) (W : PEParams) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    Option ((List UInt8 × List UInt8) × SessionState HwBytes) :=
  match SignalPqxdh.Model.initiateKeys (modelPrimsFast X W) (initiateInput W me b t) with
  | none => none
  | some (dk, hdr) =>
    let idA := keyPairOf W.C me.idPriv
    match initializeInitiatorSession W.C (pqxdhSpqrSession W) ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
        (bytesToKey32 (ofU8 dk.rootKey)) (bytesToKey32 (ofU8 dk.chainKey))
        (bytesToKey32 (ofU8 dk.pqrKey)) (bytesToKey32 ((t.toList.drop 160).take 32)) with
    | .error _ => none | .ok st => some ((hdr.ekAPk, hdr.kemCt), st)
private theorem initiateState_eq_of_coreFast (X : UnreachedPqxdhPrimitives) (W₁ W₂ : PEParams)
    (P : CryptoGames.Party) (me : LocalIdentity) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (h : initiateCoreFast X W₁ me b t = initiateCoreFast X W₂ me b t) :
    initiateState X W₁ P me b t = initiateState X W₂ P me b t := by
  have map_eq : ∀ W, initiateState X W P me b t =
      (initiateCoreFast X W me b t).map fun ((ekAPk, kemCt), st) =>
        (initiatorRecordExtras me b ⟨u8Vec 32 ekAPk⟩ (u8Vec 1568 kemCt), ⟨P, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩) := by
    intro W; unfold initiateState initiateCoreFast; dsimp only; rw [modelPrims_eq_fast]
    cases SignalPqxdh.Model.initiateKeys (modelPrimsFast X W) (initiateInput W me b t) with
    | none => rfl | some p => rcases p with ⟨dk, hdr⟩; dsimp only; cases initializeInitiatorSession W.C (pqxdhSpqrSession W) _ _ _ _ _ _ _ <;> rfl
  rw [map_eq W₁, map_eq W₂, h]

@[expose] def recvPrekeyCoreFast (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : CryptoGames.Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (HwBytes × SessionState HwBytes)) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    if (m.spkId != k.spkId) || (m.kpkId != k.kpkId) then some none
    else match SignalPqxdh.Model.acceptKeys (modelPrimsFast X W) (acceptInput W me k m) with
      | none => some none
      | some dk =>
        let st0 : SessionState HwBytes := initializeRecipientSession (pqxdhSpqrSession W)
          ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
          (bytesToKey32 (ofU8 dk.rootKey)) (bytesToKey32 (ofU8 dk.chainKey)) (bytesToKey32 (ofU8 dk.pqrKey))
        match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParamsFast W).expectedAddrs P) inner .preKey rc st0 with
        | (.ok pt, st) => some (some (pt, st)) | (.error .panic, _) => none | (.error _, _) => some none
private theorem recvPrekeyState_eq_of_coreFast (X : UnreachedPqxdhPrimitives) (W₁ W₂ : PEParams)
    (P : CryptoGames.Party) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256)
    (h : recvPrekeyCoreFast X W₁ P me k m rc = recvPrekeyCoreFast X W₂ P me k m rc) :
    recvPrekeyState X W₁ P me k m rc = recvPrekeyState X W₂ P me k m rc := by
  have map_eq : ∀ W, recvPrekeyState X W P me k m rc =
      (recvPrekeyCoreFast X W P me k m rc).map (Option.map fun (pt, st) => (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt)) := by
    intro W; unfold recvPrekeyState recvPrekeyCoreFast; dsimp only; rw [modelPrims_eq_fast, pqxdhSessionParams_eq_fast]
    cases SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => rfl
    | ok inner =>
      dsimp only; by_cases hc : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
      · have hcb : ((m.spkId != k.spkId) || (m.kpkId != k.kpkId)) = true := by simpa [Bool.or_eq_true, bne_iff_ne] using hc
        simp only [hc, hcb, ↓reduceIte]; rfl
      · have hcb : ((m.spkId != k.spkId) || (m.kpkId != k.kpkId)) = false := by
          cases hb : (m.spkId != k.spkId) || (m.kpkId != k.kpkId)
          · rfl
          · exact False.elim (hc (by simpa [Bool.or_eq_true, bne_iff_ne] using hb))
        simp only [hc, hcb, ↓reduceIte, Bool.false_eq_true]
        cases SignalPqxdh.Model.acceptKeys (modelPrimsFast X W) (acceptInput W me k m) with
        | none => rfl
        | some dk =>
          dsimp only; rcases SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParamsFast W).expectedAddrs P) inner .preKey rc _ with ⟨res, st⟩
          cases res with | ok pt => rfl | error e => cases e <;> rfl
  rw [map_eq W₁, map_eq W₂, h]

@[expose] def checkInitEqAt (W₁ W₂ : PEParams) (st₀ : PqParty) (b₀ : PreKeyBundleFields)
    (t₀ : List.Vector (BitVec 8) initiateTapeLen) : Bool :=
  optEqBool (prodEqBool (fun x y => x == y) sessionStateEqBool)
    (initiateCoreFast dummyX W₁ st₀.me b₀ t₀) (initiateCoreFast dummyX W₂ st₀.me b₀ t₀)
@[expose] def checkInitEq := checkInitEqAt compP0 compP0RealFast
theorem initiateState_eq_of_checkInitEqAt {W₁ W₂ W₂' : PEParams} (hW : W₂' = W₂)
    {st₀ : PqParty} {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    (h : checkInitEqAt W₁ W₂ st₀ b₀ t₀ = true) :
    initiateState dummyX W₁ st₀.party st₀.me b₀ t₀ = initiateState dummyX W₂' st₀.party st₀.me b₀ t₀ := by
  rw [hW]; exact initiateState_eq_of_coreFast dummyX W₁ W₂ st₀.party st₀.me b₀ t₀
    (eq_of_optEqBool (eq_of_prodEqBool beq_iff_eq.mp eq_of_sessionStateEqBool) h)

@[expose] def checkSendEqAt (W₁ W₂ : PEParams) (st₀ : PqParty) (m₀ : HwBytes) (r₀ : List.Vector (BitVec 8) 64) : Bool :=
  optEqBool (prodEqBool (exceptEqBool errEqBool signalMsgEqBool) sessionStateEqBool)
    (st₀.session.map fun p => SessionState.messageEncrypt W₁.C protoSignalCodec
      (pqxdhSpqrSession W₁) ((pqxdhSessionParamsFast W₁).sendAddrs p.2.party) m₀ r₀.toList p.2.session)
    (st₀.session.map fun p => SessionState.messageEncrypt W₂.C protoSignalCodec
      (pqxdhSpqrSession W₂) ((pqxdhSessionParamsFast W₂).sendAddrs p.2.party) m₀ r₀.toList p.2.session)
@[expose] def checkSendEq := checkSendEqAt compP0 compP0RealFast
theorem sendMap_eq_of_checkSendEqAt {W₁ W₂ W₂' : PEParams} (hW : W₂' = W₂)
    {st₀ : PqParty} {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    (h : checkSendEqAt W₁ W₂ st₀ m₀ r₀ = true) :
    st₀.session.map (fun p => SessionState.messageEncrypt W₁.C protoSignalCodec
        (pqxdhSpqrSession W₁) ((pqxdhSessionParams W₁).sendAddrs p.2.party) m₀ r₀.toList p.2.session) =
      st₀.session.map (fun p => SessionState.messageEncrypt W₂'.C protoSignalCodec
        (pqxdhSpqrSession W₂') ((pqxdhSessionParams W₂').sendAddrs p.2.party) m₀ r₀.toList p.2.session) := by
  rw [hW, pqxdhSessionParams_eq_fast W₁, pqxdhSessionParams_eq_fast W₂]
  exact eq_of_optEqBool
    (eq_of_prodEqBool (eq_of_exceptEqBool eq_of_errEqBool eq_of_signalMsgEqBool) eq_of_sessionStateEqBool) h

@[expose] def checkRecvPrekeyEqAt (W₁ W₂ : PEParams) (st₀ : PqParty)
    (m₀ : PreKeyMessageFields) (rc₀ : BitVec 256) : Bool :=
  optEqBool (optEqBool (optEqBool (prodEqBool (fun x y => x == y) sessionStateEqBool)))
    ((preKeysNamedBy st₀ m₀).map fun k => recvPrekeyCoreFast dummyX W₁ st₀.party st₀.me k m₀ rc₀)
    ((preKeysNamedBy st₀ m₀).map fun k => recvPrekeyCoreFast dummyX W₂ st₀.party st₀.me k m₀ rc₀)
@[expose] def checkRecvPrekeyEq := checkRecvPrekeyEqAt compP0 compP0RealFast
private theorem map_eq_of_optEqBool {α β₁ β₂ : Type} {f₁ f₂ : α → β₁} {g₁ g₂ : α → β₂} {eq : β₁ → β₁ → Bool}
    (hfg : ∀ k, eq (f₁ k) (f₂ k) = true → g₁ k = g₂ k) :
    ∀ (o : Option α), optEqBool eq (o.map f₁) (o.map f₂) = true → o.map g₁ = o.map g₂
  | none, _ => rfl | some k, h => congrArg some (hfg k h)
theorem recvMap_eq_of_checkRecvPrekeyEqAt {W₁ W₂ W₂' : PEParams} (hW : W₂' = W₂)
    {st₀ : PqParty} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    (P : CryptoGames.Party) (me : LocalIdentity) (hp : st₀.party = P) (hme : st₀.me = me)
    (h : checkRecvPrekeyEqAt W₁ W₂ st₀ m₀ rc₀ = true) :
    (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX W₁ P me k m₀ rc₀) =
      (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX W₂' P me k m₀ rc₀) := by
  rw [hW]; subst hp; subst hme
  exact map_eq_of_optEqBool (fun k hk => recvPrekeyState_eq_of_coreFast dummyX W₁ W₂ st₀.party st₀.me k m₀ rc₀
    (eq_of_optEqBool (eq_of_optEqBool (eq_of_prodEqBool beq_iff_eq.mp eq_of_sessionStateEqBool)) hk))
    (preKeysNamedBy st₀ m₀) h

@[expose] def checkTryDecryptEqAt (W₁ W₂ : PEParams) (g₀ : GhostState HwBytes)
    (inner : SignalMessage) (mt : MessageType) (rc₀ : BitVec 256) : Bool :=
  prodEqBool (exceptEqBool errEqBool (fun x y => x == y)) sessionStateEqBool
    (SessionState.tryDecryptFromRecord W₁.C (pqxdhSpqrSession W₁)
      ((pqxdhSessionParamsFast W₁).expectedAddrs g₀.party) inner mt rc₀ g₀.session)
    (SessionState.tryDecryptFromRecord W₂.C (pqxdhSpqrSession W₂)
      ((pqxdhSessionParamsFast W₂).expectedAddrs g₀.party) inner mt rc₀ g₀.session)
@[expose] def checkTryDecryptEq := checkTryDecryptEqAt compP0 compP0RealFast
theorem tryDecrypt_eq_of_checkTryDecryptEqAt {W₁ W₂ W₂' : PEParams} (hW : W₂' = W₂)
    {g₀ : GhostState HwBytes} {inner : SignalMessage} {mt : MessageType} {rc₀ : BitVec 256}
    (h : checkTryDecryptEqAt W₁ W₂ g₀ inner mt rc₀ = true) :
    SessionState.tryDecryptFromRecord W₁.C (pqxdhSpqrSession W₁)
        ((pqxdhSessionParams W₁).expectedAddrs g₀.party) inner mt rc₀ g₀.session =
      SessionState.tryDecryptFromRecord W₂'.C (pqxdhSpqrSession W₂')
        ((pqxdhSessionParams W₂').expectedAddrs g₀.party) inner mt rc₀ g₀.session := by
  rw [hW, pqxdhSessionParams_eq_fast W₁, pqxdhSessionParams_eq_fast W₂]
  exact eq_of_prodEqBool (eq_of_exceptEqBool eq_of_errEqBool beq_iff_eq.mp) eq_of_sessionStateEqBool h

/-- Decidable well-formedness check for a concrete reference `PqParty` `st₀`. -/
@[expose] def checkPartyWF (P : PEParams) (st₀ : PqParty) : Bool :=
  (match st₀.session with
   | none => true
   | some (x₀, g₀) =>
       decide (g₀.party = st₀.party) && decide ((encodeRecordUnderExtras (fun _ => x₀) g₀).length < 2 ^ 31)) &&
  (encodeDirFast P { st₀ with session := none }).all (fun f =>
    decide (f.2.length < 2 ^ 31) && decide (f.2.length ≤ fileCapBytes)) &&
  decide (st₀.signed.map (·.1)).Nodup && decide (st₀.oneTime.map (·.1)).Nodup &&
  decide (st₀.kyberOneTime.map (·.1)).Nodup && decide (st₀.kyberLastResort.map (·.1)).Nodup

theorem specDomain_clearSession_of_checkPartyWF {P : PEParams} {st₀ : PqParty}
    (h : checkPartyWF P st₀ = true) : PqxdhPartyInSpecDomain P { st₀ with session := none } := by
  unfold checkPartyWF at h; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, hall⟩, hnd1⟩, hnd2⟩, hnd3⟩, hnd4⟩ := h
  refine ⟨(fun _ _ hs => nomatch hs), fun f hf => ?_, hnd1, hnd2, hnd3, hnd4⟩
  rw [encodeDir_eq_fast] at hf; exact ⟨(hall f hf).1, fun _ => (hall f hf).2⟩

theorem pqPartyEquiv_of_checkPartyWF {P : PEParams} {st st₀ : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st) (hwf₀ : checkPartyWF P st₀ = true)
    (hfiles : ∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st₀) p) : PqPartyEquiv st st₀ := by
  have hwf₀N := specDomain_clearSession_of_checkPartyWF hwf₀
  unfold checkPartyWF at hwf₀; simp only [Bool.and_eq_true] at hwf₀; have hs0 := hwf₀.1.1.1.1.1
  refine pqPartyEquiv_of_weakWF hwf hwf₀N (fun x₀ g₀ hs => ?_) hfiles
  rw [hs] at hs0; simp only [Bool.and_eq_true, decide_eq_true_eq] at hs0; exact hs0

theorem inputsEquiv_symm {i i' : Inputs} (h : InputsEquiv i i') : InputsEquiv i' i :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun p => (h.2.2.2 p).symm⟩
theorem inputsEquiv_trans {i₁ i₂ i₃ : Inputs}
    (h₁ : InputsEquiv i₁ i₂) (h₂ : InputsEquiv i₂ i₃) : InputsEquiv i₁ i₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, fun p => (h₁.2.2.2 p).trans (h₂.2.2.2 p)⟩
theorem extract_pqRecvPrekey_args {P : PEParams} {st₀ st : PqParty}
    {body₀ body : HwBytes} {rc₀ rc : BitVec 256}
    (h : InputsEquiv (pqRecvInputs P st₀ (wirePrekey :: body₀) rc₀) (pqRecvInputs P st (wirePrekey :: body) rc)) :
    body₀ = body ∧ rc₀ = rc ∧ ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st) p := by
  obtain ⟨hrc, hdir⟩ := InputsInjAux.strip_coins_filesOf P st₀ st (keyToBytes32 rc₀) (keyToBytes32 rc) h.2.2.2
  exact ⟨(List.cons.inj h.2.2.1).2, CodecInjAux.keyToBytes32_inj hrc, hdir⟩

private theorem pqRecvPrekeyModel_eq_of_session_none {W₁ W₂ : PEParams} {X : UnreachedPqxdhPrimitives}
    {st st₀ : PqParty} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    (hst : PqPartyEquiv st st₀) (hs : st.session = none)
    (hEval : (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX W₁ st₀.party st₀.me k m₀ rc₀) =
      (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX W₂ st₀.party st₀.me k m₀ rc₀)) :
    pqRecvPrekeyModel X W₁ st m₀ rc₀ = pqRecvPrekeyModel X W₂ st m₀ rc₀ := by
  rw [pqRecvPrekeyModel_xindep X dummyX W₁ st m₀ rc₀, pqRecvPrekeyModel_xindep X dummyX W₂ st m₀ rc₀]
  unfold pqRecvPrekeyModel
  cases SignalMessage.tryFrom protoSignalCodec m₀.inner with
  | error _ => rfl
  | ok inner =>
    dsimp only; split_ifs
    · rfl
    · rw [hs]; dsimp only; rw [keysFor_eq_of_pqPartyEquiv hst m₀, hst.party_eq, hst.me_eq]
      cases hk : preKeysNamedBy st₀ m₀ with
      | none => rfl
      | some k => rw [hk] at hEval; simp only [Option.map_some, Option.some.injEq] at hEval; dsimp only; rw [hEval]

theorem modelAgreesOnInput_of_pqInitInputsAt {P P₀ : PEParams}
    {i : Inputs} {st₀ : PqParty} {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    (hwf₀ : checkPartyWF P st₀ = true) (heq₀ : InputsEquiv i (pqInitInputs P st₀ b₀ t₀))
    (hEval : initiateState dummyX P st₀.party st₀.me b₀ t₀ =
      initiateState dummyX P₀ st₀.party st₀.me b₀ t₀) :
    DY.Libsignal.Composed.Refinement.Cli.ElfGuard.ModelAgreesOnInput P P₀ i := by
  refine ⟨?_, fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqInitInputs_pqSendInputs_false
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqInitInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ _ _ _ heq => False.elim (inputsEquiv_pqInitInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ _ _ _ _ _ _ heq => False.elim (inputsEquiv_pqInitInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq))⟩
  intro X st files b t hwf _ hbun heq
  have ⟨hflat, hpbf⟩ : DY.Libsignal.Composed.Refinement.Cli.BundleFilesFlat files ∧
      parseBundleFiles (filesOf files) = some (publicBundleOf b) := by
    rcases hbun with rfl | hb
    · exact ⟨bundleFilesFlat_publicBundleOf b, parseBundleFiles_publicBundleOf b⟩
    · exact hb
  obtain ⟨hpbf₀, ht, hfiles⟩ := pqInitInputs_pqInitInputsF_extract hflat (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
  cases publicBundleOf_injective (Option.some.inj (hpbf₀.symm.trans hpbf)); subst ht
  have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)
  rw [pqInitModel_xindep X dummyX P st b₀ t₀, pqInitModel_xindep X dummyX P₀ st b₀ t₀]
  unfold pqInitModel; rw [hst.party_eq, hst.me_eq, hEval]

/-- Proves `Sha256AgreesOnInput compHooks0 i` for an `init` call matching `(st₀, b₀, t₀)`. -/
theorem sha256AgreesOnInput_of_pqInitInputs {i : Inputs} {st₀ : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (_hsess₀ : st₀.session = none)
    (heq₀ : InputsEquiv i (pqInitInputs compP0 st₀ b₀ t₀))
    (hEvalBool : checkInitEq st₀ b₀ t₀ = true) : Sha256AgreesOnInput compHooks0 i :=
  modelAgreesOnInput_of_pqInitInputsAt hwf₀ heq₀ (initiateState_eq_of_checkInitEqAt compP0Real_eq_fast hEvalBool)

theorem modelAgreesOnInput_of_pqSendInputsAt {P P₀ : PEParams}
    {i : Inputs} {st₀ : PqParty} {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    (hwf₀ : checkPartyWF P st₀ = true) (hsess₀ : st₀.session.isSome = true) (heq₀ : InputsEquiv i (pqSendInputs P st₀ m₀ r₀))
    (hEval : st₀.session.map (fun p => SessionState.messageEncrypt P.C protoSignalCodec
        (pqxdhSpqrSession P) ((pqxdhSessionParams P).sendAddrs p.2.party) m₀ r₀.toList p.2.session) =
      st₀.session.map (fun p => SessionState.messageEncrypt P₀.C protoSignalCodec
        (pqxdhSpqrSession P₀) ((pqxdhSessionParams P₀).sendAddrs p.2.party)
        m₀ r₀.toList p.2.session)) :
    DY.Libsignal.Composed.Refinement.Cli.ElfGuard.ModelAgreesOnInput P P₀ i := by
  cases hs₀ : st₀.session with
  | none => rw [hs₀] at hsess₀; cases hsess₀
  | some xg₀ =>
    rcases xg₀ with ⟨x₀, g₀⟩; rw [hs₀] at hEval; simp only [Option.map_some, Option.some.injEq] at hEval
    refine ⟨fun _ _ _ _ _ _ _ _ heq => False.elim (pqSendInputs_pqInitInputsF_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)), ?_,
      fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
      fun _ _ _ _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
      fun _ _ _ _ _ _ _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false (inputsEquiv_trans (inputsEquiv_symm heq₀) heq))⟩
    intro st m coins hwf _ heq
    obtain ⟨rfl, rfl, hfiles⟩ := inputsEquiv_pqSendInputs_extract (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)
    unfold pqSendModel; cases hs : st.session with
    | none => rfl
    | some xg =>
      rcases xg with ⟨x, g⟩; have hrel := hst.session_rel; rw [hs, hs₀] at hrel
      cases hrel with | some hse => dsimp only at hse ⊢; rw [hse.party_eq, hse.session_eq, hEval]

/-- Proves `Sha256AgreesOnInput compHooks0 i` for a `send` call matching `(st₀, m₀, r₀)`. -/
theorem sha256AgreesOnInput_of_pqSendInputs {i : Inputs} {st₀ : PqParty}
    {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session.isSome = true)
    (heq₀ : InputsEquiv i (pqSendInputs compP0 st₀ m₀ r₀))
    (hEvalBool : checkSendEq st₀ m₀ r₀ = true) : Sha256AgreesOnInput compHooks0 i :=
  modelAgreesOnInput_of_pqSendInputsAt hwf₀ hsess₀ heq₀ (sendMap_eq_of_checkSendEqAt compP0Real_eq_fast hEvalBool)

theorem modelAgreesOnInput_of_pqRecvPrekey_noneAt {P P₀ : PEParams}
    {i : Inputs} {st₀ : PqParty} {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF P st₀ = true) (hsess₀ : st₀.session = none)
    (heq₀ : InputsEquiv i (pqRecvInputs P st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : preKeyOfBody? body₀ = some m₀)
    (hEval : (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX P st₀.party st₀.me k m₀ rc₀) =
      (preKeysNamedBy st₀ m₀).map (fun k => recvPrekeyState dummyX P₀ st₀.party st₀.me k m₀ rc₀)) :
    DY.Libsignal.Composed.Refinement.Cli.ElfGuard.ModelAgreesOnInput P P₀ i := by
  refine ⟨fun _ _ _ _ _ _ _ _ heq => False.elim (pqRecvInputs_pqInitInputsF_false
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false
      (inputsEquiv_trans (inputsEquiv_symm heq) heq₀)),
    fun _ _ _ _ _ heq => absurd
      (List.cons.inj (inputsEquiv_trans (inputsEquiv_symm heq₀) heq).2.2.1).1 (by decide),
    ?_, ?_⟩
  · intro X st body m rc hwf hmlen hbody heq
    obtain ⟨rfl, rfl, hfiles⟩ := extract_pqRecvPrekey_args
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)
    have hs_none : st.session = none := by
      have hrel := hst.session_rel; rw [hsess₀] at hrel
      cases hs : st.session with | none => rfl | some _ => rw [hs] at hrel; cases hrel
    have hmain : ∀ st' : PqParty, PqPartyEquiv st' st₀ → st'.session = none →
        pqRecvPrekeyModel X P st' m rc₀ = pqRecvPrekeyModel X P₀ st' m rc₀ := by
      intro st' hst' hs'
      rcases hbody with hbytes | ⟨_, hm⟩
      · cases hp : parsePreKey m.bytes with
        | none =>
          rw [pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P st' m rc₀ hmlen hp,
              pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P₀ st' m rc₀ hmlen hp]
        | some _ =>
          have hm' : preKeyOfBody? body₀ = some m :=
            hbytes ▸ preKeyOfBody?_bytes_of_parsePreKey_some hmlen hp
          cases hm'.symm.trans hm₀; exact pqRecvPrekeyModel_eq_of_session_none hst' hs' hEval
      · cases hm.symm.trans hm₀; exact pqRecvPrekeyModel_eq_of_session_none hst' hs' hEval
    exact ⟨fun _ => hmain st hst hs_none, fun _ _ hs => nomatch (hs_none.symm.trans hs)⟩
  · intro st x g body q rc hwf hs _ _ _ heq
    obtain ⟨_, _, hfiles⟩ := extract_pqRecvPrekey_args
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    have hrel := (pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)).session_rel
    rw [hs, hsess₀] at hrel; cases hrel

/-- Proves `Sha256AgreesOnInput compHooks0 i` for a pre-key `recv` call when `st₀.session = none`. -/
theorem sha256AgreesOnInput_of_pqRecvPrekey_none {i : Inputs} {st₀ : PqParty}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = none)
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : DY.Libsignal.Composed.Refinement.Cli.ElfGuard.preKeyOfBody? body₀ = some m₀)
    (hEvalBool : checkRecvPrekeyEq st₀ m₀ rc₀ = true) : Sha256AgreesOnInput compHooks0 i :=
  modelAgreesOnInput_of_pqRecvPrekey_noneAt hwf₀ hsess₀ heq₀ hm₀
    (recvMap_eq_of_checkRecvPrekeyEqAt compP0Real_eq_fast st₀.party st₀.me rfl rfl hEvalBool)

theorem modelAgreesOnInput_of_pqRecvPrekey_someAt {P P₀ : PEParams}
    {i : Inputs} {st₀ : PqParty} {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {q₀ : PreKeyFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF P st₀ = true) (hsess₀ : st₀.session = some (x₀, g₀))
    (heq₀ : InputsEquiv i (pqRecvInputs P st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : preKeyOfBody? body₀ = some m₀) (hq₀ : parsePreKey body₀ = some q₀)
    (hEvalDec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g₀.party) q₀.inner .preKey rc₀ g₀.session =
      SessionState.tryDecryptFromRecord P₀.C (pqxdhSpqrSession P₀)
        ((pqxdhSessionParams P₀).expectedAddrs g₀.party) q₀.inner .preKey rc₀ g₀.session)
    (hEvalNew : (preKeysNamedBy { st₀ with session := none } m₀).map
        (fun k => recvPrekeyState dummyX P st₀.party st₀.me k m₀ rc₀) =
      (preKeysNamedBy { st₀ with session := none } m₀).map
        (fun k => recvPrekeyState dummyX P₀ st₀.party st₀.me k m₀ rc₀)) :
    DY.Libsignal.Composed.Refinement.Cli.ElfGuard.ModelAgreesOnInput P P₀ i := by
  refine ⟨fun _ _ _ _ _ _ _ _ heq => False.elim (pqRecvInputs_pqInitInputsF_false
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false
      (inputsEquiv_trans (inputsEquiv_symm heq) heq₀)),
    fun _ _ _ _ _ heq => absurd
      (List.cons.inj (inputsEquiv_trans (inputsEquiv_symm heq₀) heq).2.2.1).1 (by decide),
    ?_, ?_⟩
  · intro X st body m rc hwf hmlen hbody heq
    obtain ⟨rfl, rfl, hfiles⟩ := extract_pqRecvPrekey_args
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)
    have htry₀ : SignalMessage.tryFrom protoSignalCodec m₀.inner = .ok q₀.inner := by
      obtain ⟨q', hq', _, _, _, _, htry⟩ := preKeyOfBody?_some_inv hm₀
      cases hq₀.symm.trans hq'; exact htry
    have hsome_eq : m = m₀ → pqRecvPrekeyModel X P st m rc₀ = pqRecvPrekeyModel X P₀ st m rc₀ := by
      rintro rfl; unfold pqRecvPrekeyModel; rw [htry₀]; dsimp only; split_ifs
      · rfl
      · cases hs : st.session with
        | none => have hrel := hst.session_rel; rw [hs, hsess₀] at hrel; cases hrel
        | some xg =>
          rcases xg with ⟨x, g⟩; have hrel := hst.session_rel; rw [hs, hsess₀] at hrel
          cases hrel with
          | some hse =>
            dsimp only at hse ⊢; split_ifs
            · rfl
            · rw [hse.party_eq, hse.session_eq, hEvalDec]
            · rfl
    have hnone_eq : m = m₀ →
        pqRecvPrekeyModel X P { st with session := none } m rc₀ =
          pqRecvPrekeyModel X P₀ { st with session := none } m rc₀ := by
      rintro rfl; exact pqRecvPrekeyModel_eq_of_session_none (pqPartyEquiv_clearSession hst) rfl hEvalNew
    rcases hbody with hbytes | ⟨_, hm⟩
    · cases hp : parsePreKey m.bytes with
      | none =>
        exact ⟨fun _ => by
            rw [pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P st m rc₀ hmlen hp,
                pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P₀ st m rc₀ hmlen hp],
          fun _ _ _ _ => by
            rw [pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P _ m rc₀ hmlen hp,
                pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P₀ _ m rc₀ hmlen hp]⟩
      | some _ =>
        have hm_eq := Option.some.inj ((hbytes ▸ preKeyOfBody?_bytes_of_parsePreKey_some hmlen hp).symm.trans hm₀)
        exact ⟨fun _ => hsome_eq hm_eq, fun _ _ _ _ => hnone_eq hm_eq⟩
    · have hm_eq := Option.some.inj (hm.symm.trans hm₀)
      exact ⟨fun _ => hsome_eq hm_eq, fun _ _ _ _ => hnone_eq hm_eq⟩
  · intro st x g body q rc hwf hs _ hq _ heq
    obtain ⟨rfl, rfl, hfiles⟩ := extract_pqRecvPrekey_args (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    cases hq.symm.trans hq₀
    have hrel := (pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)).session_rel
    rw [hs, hsess₀] at hrel
    cases hrel with
    | some hse =>
      unfold DY.Libsignal.Composed.Refinement.Cli.ElfGuard.pqRecvMatchingFieldsModel
      dsimp only; split_ifs
      · rfl
      · rfl
      · rw [hse.party_eq, hse.session_eq, hEvalDec]
/-- Proves `Sha256AgreesOnInput compHooks0 i` for a pre-key `recv` call when
`st₀.session = some (x₀, g₀)` and `preKeyOfBody? body₀ = some m₀`. -/
theorem sha256AgreesOnInput_of_pqRecvPrekey_some {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {q₀ : PreKeyFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = some (x₀, g₀))
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : DY.Libsignal.Composed.Refinement.Cli.ElfGuard.preKeyOfBody? body₀ = some m₀)
    (hq₀ : parsePreKey body₀ = some q₀)
    (hEvalDecBool : checkTryDecryptEq g₀ q₀.inner .preKey rc₀ = true)
    (hEvalNewBool : checkRecvPrekeyEq { st₀ with session := none } m₀ rc₀ = true) :
    Sha256AgreesOnInput compHooks0 i :=
  modelAgreesOnInput_of_pqRecvPrekey_someAt hwf₀ hsess₀ heq₀ hm₀ hq₀
    (tryDecrypt_eq_of_checkTryDecryptEqAt compP0Real_eq_fast hEvalDecBool)
    (recvMap_eq_of_checkRecvPrekeyEqAt compP0Real_eq_fast st₀.party st₀.me rfl rfl hEvalNewBool)

theorem modelAgreesOnInput_of_pqRecvPrekey_noMatchAt {P P₀ : PEParams}
    {i : Inputs} {st₀ : PqParty} {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {q₀ : PreKeyFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF P st₀ = true) (hsess₀ : st₀.session = some (x₀, g₀))
    (heq₀ : InputsEquiv i (pqRecvInputs P st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : preKeyOfBody? body₀ = some m₀) (hq₀ : parsePreKey body₀ = some q₀)
    (hNoMatch : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqSessionMatches x g m₀)
    (hNoFields : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqFieldsMatch x g q₀)
    (hEvalNew : (preKeysNamedBy { st₀ with session := none } m₀).map
        (fun k => recvPrekeyState dummyX P st₀.party st₀.me k m₀ rc₀) =
      (preKeysNamedBy { st₀ with session := none } m₀).map
        (fun k => recvPrekeyState dummyX P₀ st₀.party st₀.me k m₀ rc₀)) :
    DY.Libsignal.Composed.Refinement.Cli.ElfGuard.ModelAgreesOnInput P P₀ i := by
  refine ⟨fun _ _ _ _ _ _ _ _ heq => False.elim (pqRecvInputs_pqInitInputsF_false
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)),
    fun _ _ _ _ _ heq => False.elim (inputsEquiv_pqSendInputs_pqRecvInputs_false
      (inputsEquiv_trans (inputsEquiv_symm heq) heq₀)),
    fun _ _ _ _ _ heq => absurd
      (List.cons.inj (inputsEquiv_trans (inputsEquiv_symm heq₀) heq).2.2.1).1 (by decide),
    ?_, ?_⟩
  · intro X st body m rc hwf hmlen hbody heq
    obtain ⟨rfl, rfl, hfiles⟩ := extract_pqRecvPrekey_args
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)
    have hnot_match : m = m₀ → ¬ (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) := by
      rintro rfl hcond
      cases hs : st.session with
      | none => have hrel := hst.session_rel; rw [hs, hsess₀] at hrel; cases hrel
      | some xg =>
        rcases xg with ⟨x, g⟩
        have hrel := hst.session_rel; rw [hs, hsess₀] at hrel
        cases hrel with | some hse => exact hNoMatch x g hse (hcond x g hs)
    have hnone_eq : m = m₀ →
        pqRecvPrekeyModel X P { st with session := none } m rc₀ =
          pqRecvPrekeyModel X P₀ { st with session := none } m rc₀ := by
      rintro rfl
      exact pqRecvPrekeyModel_eq_of_session_none (pqPartyEquiv_clearSession hst) rfl hEvalNew
    rcases hbody with hbytes | ⟨_, hm⟩
    · cases hp : parsePreKey m.bytes with
      | none =>
        exact ⟨fun _ => by
            rw [pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P st m rc₀ hmlen hp,
                pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P₀ st m rc₀ hmlen hp],
          fun _ _ _ _ => by
            rw [pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P _ m rc₀ hmlen hp,
                pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none X P₀ _ m rc₀ hmlen hp]⟩
      | some _ =>
        have hm' : preKeyOfBody? body₀ = some m :=
          hbytes ▸ preKeyOfBody?_bytes_of_parsePreKey_some hmlen hp
        have hm_eq : m = m₀ := Option.some.inj (hm'.symm.trans hm₀)
        exact ⟨fun hcond => False.elim (hnot_match hm_eq hcond), fun _ _ _ _ => hnone_eq hm_eq⟩
    · have hm_eq : m = m₀ := Option.some.inj (hm.symm.trans hm₀)
      exact ⟨fun hcond => False.elim (hnot_match hm_eq hcond), fun _ _ _ _ => hnone_eq hm_eq⟩
  · intro st x g body q rc hwf hs _ hq hfm heq
    obtain ⟨rfl, rfl, hfiles⟩ := extract_pqRecvPrekey_args
      (inputsEquiv_trans (inputsEquiv_symm heq₀) heq)
    cases hq.symm.trans hq₀
    have hrel := (pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hfiles p).symm)).session_rel
    rw [hs, hsess₀] at hrel
    cases hrel with | some hse => exact False.elim (hNoFields x g hse hfm)

/-- Proves `Sha256AgreesOnInput compHooks0 i` for a pre-key `recv` call when
`st₀.session = some (x₀, g₀)` does not match the incoming pre-key message `m₀` / `q₀`. -/
theorem sha256AgreesOnInput_of_pqRecvPrekey_noMatch {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {q₀ : PreKeyFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = some (x₀, g₀))
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : DY.Libsignal.Composed.Refinement.Cli.ElfGuard.preKeyOfBody? body₀ = some m₀)
    (hq₀ : parsePreKey body₀ = some q₀)
    (hNoMatch : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqSessionMatches x g m₀)
    (hNoFields : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqFieldsMatch x g q₀)
    (hEvalNewBool : checkRecvPrekeyEq { st₀ with session := none } m₀ rc₀ = true) :
    Sha256AgreesOnInput compHooks0 i :=
  modelAgreesOnInput_of_pqRecvPrekey_noMatchAt hwf₀ hsess₀ heq₀ hm₀ hq₀ hNoMatch hNoFields
    (recvMap_eq_of_checkRecvPrekeyEqAt compP0Real_eq_fast st₀.party st₀.me rfl rfl hEvalNewBool)

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
