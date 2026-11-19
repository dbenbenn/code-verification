/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.NonVacuity -- proof-setup: allow-public-import
public import Symbolic.Specifications.Concrete.MachineEvents
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards

/-!
# Concrete SPQR-ON Non-Vacuity Base Helpers

Mock cryptographic primitives, initial Alice/Bob states, algebraic hash/HMAC/HKDF/signature
short-circuits, opaque ML-KEM vector wrappers, and `Mut.exec` / `SignalMessage` codec lemmas
for the concrete SPQR-ON roundtrip witness.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession

@[expose] def nvMlKem : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
    List.Vector.replicate 32 1#8)
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 1#8
  validPk := fun _ _ => true

@[expose] def nvPubKeyA : List.Vector (BitVec 8) 32 :=
  ⟨9#8 :: List.replicate 31 0#8, rfl⟩

@[expose] def nvPubKeyB : List.Vector (BitVec 8) 32 :=
  ⟨[0xab#8, 0xbb#8, 0x90#8, 0x4f#8, 0x2c#8, 0x8f#8, 0x86#8, 0xf7#8,
    0x13#8, 0x32#8, 0xb8#8, 0x05#8, 0x93#8, 0x13#8, 0xb1#8, 0xa1#8,
    0xcb#8, 0xad#8, 0x7b#8, 0x33#8, 0x2d#8, 0x85#8, 0x92#8, 0x7b#8,
    0x48#8, 0x5e#8, 0x5b#8, 0x0e#8, 0x10#8, 0x49#8, 0xc3#8, 0x4d#8], rfl⟩

@[expose] def nvSigZero64 : List.Vector (BitVec 8) 64 :=
  ⟨1#8 :: List.replicate 63 0#8, rfl⟩

@[expose] def nvCrypto : Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ _ => List.Vector.replicate 32 1#8
  pubKey := fun sk => if sk.get 1 == 2#8 then nvPubKeyA else nvPubKeyB

@[expose] def nvW : PEParams where
  C := nvCrypto
  Q := {
    F512 := fun _ _ => List.Vector.replicate 8 0#64
    encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 1#8)
    decaps := fun _ _ => List.Vector.replicate 32 1#8
    K := nvMlKem
  }

@[expose] def nvX : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => List.replicate 32 0
  sigSign := fun _ _ _ => List.replicate 64 0
  scalarMul := fun _ _ => List.replicate 32 0
  scalarAdd := fun _ _ => List.replicate 32 0
  kemKeyGen := fun _ => (List.replicate 1568 0, List.replicate 3168 0)
  pow8 := fun x => x
  isValidDhTriple := fun _ _ _ => true

@[expose] def nvKeysB : ResponderPreKeySecrets where
  spkId := 1#32
  spkPriv := List.Vector.replicate 32 2#8
  kpkId := 2#32
  kpkPub := List.Vector.replicate 1568 0#8
  kpkSec := List.Vector.replicate 3168 0#8
  opk := none

@[expose] def nvStA0 : PqParty :=
  { emptyParty with party := .A, me := ⟨List.Vector.replicate 32 3#8, 10#32⟩ }

@[expose] def nvStB0 : PqParty :=
  { party := .B
    me := ⟨List.Vector.replicate 32 4#8, 20#32⟩
    peerId := none
    session := none
    signed := [(1#32, ⟨List.Vector.replicate 32 2#8, nvSigZero64, 0#64⟩)]
    oneTime := []
    kyberOneTime := [(2#32, some ⟨List.Vector.replicate 1568 0#8, List.Vector.replicate 3168 0#8,
      nvSigZero64, 0#64⟩)]
    kyberLastResort := [] }

@[expose] def nvBundleB : PreKeyBundleFields :=
  honestBundle nvW.C nvStB0.me nvKeysB nvSigZero64 nvSigZero64

@[expose] def nvTapeA : List.Vector (BitVec 8) initiateTapeLen :=
  List.Vector.replicate initiateTapeLen 5#8
@[expose] def nvCoins64A : HwBytes := List.replicate 64 6#8
@[expose] def nvCoins64B : HwBytes := List.replicate 64 7#8
@[expose] def nvPt1 : HwBytes := [0x48#8, 0x69#8]
@[expose] def nvPt2 : HwBytes := [0x4F#8, 0x4B#8]

/-! ## Algebraic Short-Circuit Helpers for `nvW` and `nvX` -/

set_option maxRecDepth 8192

theorem ofU8_toU8 : ∀ (bs : List (BitVec 8)), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (ofU8_toU8 xs)

theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq
  rcases v with ⟨l, hl⟩
  dsimp only [u8Vec, vecU8]
  rw [ofU8_toU8]
  simp [fitVec, List.Vector.toList, hl]

theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) : (vecU8 v).length = n := by
  rcases v with ⟨l, hl⟩
  simpa [vecU8, toU8] using hl

abbrev nvB1 : SignalPqxdh.Primitives :=
  { blockLevelPrims nvX nvW with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims nvX nvW) }

theorem sha256Step_nvB1 (blk : List UInt8) :
    SignalPqxdh.sha256Step nvB1 SignalPqxdh.sha256InitState blk =
      SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.sha256Step, nvB1, blockLevelPrims, nvW]
  rfl

theorem foldl_sha256Step_nvB1 (blocks : List (List UInt8)) :
    blocks.foldl (SignalPqxdh.sha256Step nvB1) SignalPqxdh.sha256InitState =
      SignalPqxdh.sha256InitState := by
  induction blocks with
  | nil => rfl
  | cons blk tl ih =>
    simp only [List.foldl_cons, sha256Step_nvB1]
    exact ih

theorem sha256Ref_nvB1 (msg : List UInt8) :
    SignalPqxdh.sha256Ref nvB1 msg = SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.sha256Ref]
  rw [foldl_sha256Step_nvB1]
  rfl

theorem hmacSha256Ref_nvB1 (k msg : List UInt8) :
    SignalPqxdh.hmacSha256Ref nvB1 k msg = SignalPqxdh.sha256InitState := by
  dsimp only [SignalPqxdh.hmacSha256Ref]
  simp only [sha256Ref_nvB1]

@[expose] def nvDk : SignalPqxdh.DRKey :=
  { rootKey := SignalPqxdh.sha256InitState
    chainKey := SignalPqxdh.sha256InitState
    pqrKey := SignalPqxdh.sha256InitState }

theorem hkdfDerive96_nv (secrets : List UInt8) :
    (modelPrims nvX nvW).hkdfDerive96 secrets = nvDk := by
  dsimp only [modelPrims, SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExtractRef,
    SignalPqxdh.hkdfExpand96Ref]
  simp only [hmacSha256Ref_nvB1]
  rfl

section NvCurveHelpers

open VerifiedLibraries.Common (
  edOrderL fpInv recoverXEven leBytesToNat
  EdPoint edZero edBasepoint edOnCurve edAdd edNeg edSub edSmul encodeEd
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (
  montLiftEd signalMontLiftEd_eq montLiftEd_some_onCurve
  isCanonicalRef_blockLevelPrims_eq xeddsaVerifyRef_blockLevelPrims_eq
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4SymbolicBridge (
  signalMontLiftEd_u9_torsionFree signalMontLiftEd_ekAPub_torsionFree
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  edOnCurve_edZero edOnCurve_edBasepoint edAdd_edZero edNeg_edZero edSmul_eq_edNatSmul
)

attribute [local irreducible] fpInv recoverXEven montLiftEd montToEdwards edSmul

private def nvSigZeroEd64 : List UInt8 := (1 : UInt8) :: List.replicate 63 0

private theorem nv_ite_true {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

private theorem nv_pubKey_cases (sk : List.Vector (BitVec 8) 32) :
    nvW.C.pubKey sk = nvPubKeyA ∨ nvW.C.pubKey sk = nvPubKeyB := by
  dsimp only [nvW, nvCrypto]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem nv_pubKey_montLiftEd (v : List.Vector (BitVec 8) 32)
    (hv : v = nvPubKeyA ∨ v = nvPubKeyB) :
    ∃ P : EdPoint, montLiftEd v 0#8 = some P ∧ (edSmul edOrderL P == edZero) = true := by
  rcases hv with rfl | rfl
  · rcases signalMontLiftEd_u9_torsionFree (b := nvPubKeyA.toList) nvPubKeyA.toList_length
      (by decide) with ⟨P, hP, htf⟩
    rw [signalMontLiftEd_eq] at hP
    exact ⟨P, hP, htf⟩
  · rcases signalMontLiftEd_ekAPub_torsionFree (b := nvPubKeyB.toList) nvPubKeyB.toList_length
      (by decide) with ⟨P, hP, htf⟩
    rw [signalMontLiftEd_eq] at hP
    exact ⟨P, hP, htf⟩

private theorem nv_pubKey_guard (v : List.Vector (BitVec 8) 32)
    (hv : v = nvPubKeyA ∨ v = nvPubKeyB) :
    ((vecU8 v).length == 32 && (((vecU8 v).getD 31 0 &&& 0x80) == 0) &&
      SignalPqxdh.scalarIsInRange (vecU8 v)) = true := by
  rcases hv with rfl | rfl <;> decide

private theorem nv_upd9_isCanonical (B1 : SignalPqxdh.Primitives)
    (sv h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    ({ B1 with
        sigVerify := sv
        isCanonical := SignalPqxdh.isCanonicalRef B1
        hkdfDerive96 := h96
        rootCreateChain := rcc
        chainKdfSeed := cks
        chainKdfNext := ckn
        deriveMsgKeys := dmk
        aeadEnc := ae
        aeadDec := ad } : SignalPqxdh.Primitives).isCanonical pk =
      SignalPqxdh.isCanonicalRef B1 pk := rfl

private theorem nv_upd1_isCanonicalRef (B : SignalPqxdh.Primitives) (s512) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s512 } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl

private theorem nv_modelPrims_isCanonical_eq (pk : List UInt8) :
    (modelPrims nvX nvW).isCanonical pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims nvX nvW) pk :=
  (nv_upd9_isCanonical _ _ _ _ _ _ _ _ _ pk).trans (nv_upd1_isCanonicalRef _ _ pk)

private theorem nv_block_eq_upd :
    blockLevelPrims nvX nvW =
      { blockLevelPrims nvX nvW with isTorsionFree := fun P => edSmul edOrderL P == edZero } := rfl

private theorem nv_upd_isTorsionFree (B : SignalPqxdh.Primitives) (f : EdPoint → Bool) (P : EdPoint) :
    ({ B with isTorsionFree := f } : SignalPqxdh.Primitives).isTorsionFree P = f P := rfl

private theorem nv_block_isTorsionFree (P : EdPoint) :
    (blockLevelPrims nvX nvW).isTorsionFree P = (edSmul edOrderL P == edZero) :=
  (congrArg (fun B : SignalPqxdh.Primitives => B.isTorsionFree P) nv_block_eq_upd).trans
    (nv_upd_isTorsionFree _ _ P)

private theorem nv_block_montToEd_zero (pk : List UInt8) :
    (blockLevelPrims nvX nvW).montToEd pk 0 = montLiftEd (u8Vec 32 pk) 0#8 := by
  change SignalPqxdh.montLiftEd (u8Vec 32 pk).toList (0 : UInt8).toBitVec = _
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl,
    LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge.signalMontLiftEd_eq]

private theorem nv_isCanonicalRef_of_some (B : SignalPqxdh.Primitives) (pk : List UInt8) (P : EdPoint)
    (hg : (pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange pk) = true)
    (hm : B.montToEd pk 0 = some P) :
    SignalPqxdh.isCanonicalRef B pk = B.isTorsionFree P := by
  rw [SignalPqxdh.isCanonicalRef.eq_def, nv_ite_true hg]
  split
  · rename_i Q hQ; exact congrArg B.isTorsionFree (Option.some.inj (hQ.symm.trans hm))
  · rename_i hQ; exact absurd (hQ.symm.trans hm) nofun

theorem isCanonical_nv_pubKey (sk : List.Vector (BitVec 8) 32) :
    (modelPrims nvX nvW).isCanonical (vecU8 (nvW.C.pubKey sk)) = true := by
  have hv := nv_pubKey_cases sk
  rcases nv_pubKey_montLiftEd _ hv with ⟨P, hP, htf⟩
  have hm : (blockLevelPrims nvX nvW).montToEd (vecU8 (nvW.C.pubKey sk)) 0 = some P := by
    rw [nv_block_montToEd_zero, u8Vec_vecU8]
    exact hP
  exact (nv_modelPrims_isCanonical_eq _).trans
    ((nv_isCanonicalRef_of_some _ _ P (nv_pubKey_guard _ hv) hm).trans
      ((nv_block_isTorsionFree P).trans htf))

private theorem nv_sha512Pad_len_ge_128 (msg : List UInt8) :
    128 ≤ (SignalPqxdh.sha512Pad msg).length := by
  unfold SignalPqxdh.sha512Pad SignalPqxdh.encodeBitLen128BE SignalPqxdh.encodeBitLen64BE
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  set rem := (msg.length + 17) % 128
  have hrem_lt : rem < 128 := Nat.mod_lt _ (by decide)
  by_cases h0 : rem == 0
  · have hr0 : rem = 0 := beq_iff_eq.mp h0
    simp only [h0, ↓reduceIte]; omega
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]; omega

private theorem nv_foldl_const_aux {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β), l.foldl f z = z
  | [] => rfl
  | _ :: rest => by simp only [List.foldl_cons, hf]; exact nv_foldl_const_aux f z hf rest

private theorem nv_foldl_const {α β : Type} (f : α → β → α) (z : α)
    (hf : ∀ s x, f s x = z) :
    ∀ (l : List β) (init : α), l ≠ [] → l.foldl f init = z
  | [], _, hne => absurd rfl hne
  | _ :: rest, _, _ => by
    simp only [List.foldl_cons, hf]
    exact nv_foldl_const_aux f z hf rest

private theorem nv_sha512_zero (msg : List UInt8) :
    SignalPqxdh.sha512Ref (blockLevelPrims nvX nvW) msg = List.replicate 64 0 := by
  unfold SignalPqxdh.sha512Ref SignalPqxdh.chunkBlocks
  dsimp only []
  have hdiv : 1 ≤ (SignalPqxdh.sha512Pad msg).length / 128 :=
    Nat.div_pos (nv_sha512Pad_len_ge_128 msg) (by decide)
  have hne : ((List.range ((SignalPqxdh.sha512Pad msg).length / 128)).map
      (fun i => ((SignalPqxdh.sha512Pad msg).drop (i * 128)).take 128)) ≠ [] := by
    intro heq
    have hl := congrArg List.length heq
    simp at hl
    omega
  have hstep : ∀ s b, SignalPqxdh.sha512Step (blockLevelPrims nvX nvW) s b = List.replicate 64 0 := by
    intro s b
    unfold SignalPqxdh.sha512Step
    dsimp only [blockLevelPrims, nvW]
    decide
  rw [nv_foldl_const _ (List.replicate 64 0) hstep _ _ hne]
  decide

theorem sigVerify_nv_sigZero64 (sk : List.Vector (BitVec 8) 32) (msg : List UInt8) :
    (modelPrims nvX nvW).sigVerify (vecU8 (nvW.C.pubKey sk)) msg (vecU8 nvSigZero64) = true := by
  have hsig : vecU8 nvSigZero64 = nvSigZeroEd64 := by decide
  rw [hsig]
  have hv := nv_pubKey_cases sk
  rcases nv_pubKey_montLiftEd _ hv with ⟨P, hmont, _⟩
  have hP_on : edOnCurve P = true := montLiftEd_some_onCurve hmont
  change SignalPqxdh.xeddsaVerifyRef
    ({ blockLevelPrims nvX nvW with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims nvX nvW) })
    (vecU8 (nvW.C.pubKey sk)) msg nvSigZeroEd64 = true
  rw [xeddsaVerifyRef_blockLevelPrims_eq]
  have hcond : ((vecU8 (nvW.C.pubKey sk)).length == 32 &&
      nvSigZeroEd64.length == 64 &&
      ((nvSigZeroEd64.getD 63 0 &&& 0x60) == 0)) = true := by
    rw [vecU8_length]; decide
  rw [nv_ite_true hcond]
  dsimp only
  have hs0 : ((nvSigZeroEd64.getD 63 0 &&& 0x80) >>> 7).toBitVec = 0#8 := by decide
  rw [hs0, u8Vec_vecU8, hmont]
  dsimp only
  rw [nv_sha512_zero]
  have hh0 : leBytesToNat (u8Vec 64 (List.replicate 64 (0 : UInt8))).toList % edOrderL = 0 := by
    decide
  have hsNat0 : leBytesToNat (u8Vec 32
      ((nvSigZeroEd64.drop 32).take 31 ++ [(nvSigZeroEd64.drop 32).getD 31 0 &&& 0x7F])).toList %
      edOrderL = 0 := by decide
  rw [hh0, hsNat0,
    edSmul_eq_edNatSmul (by decide) edOnCurve_edBasepoint,
    edSmul_eq_edNatSmul (by decide) hP_on]
  change (toU8 (encodeEd (edSub edZero edZero)) == nvSigZeroEd64.take 32) = true
  have hsub0 : edSub edZero edZero = edZero := by
    change edAdd edZero (edNeg edZero) = edZero
    rw [edNeg_edZero, edAdd_edZero edOnCurve_edZero]
  rw [hsub0]
  decide

end NvCurveHelpers

theorem sha256With_nvCrypto (m : HwBytes) :
    CryptoGames.HMAC.sha256With nvCrypto.F m =
      CryptoGames.HMAC.sha256IV.toList.flatMap (CryptoGames.HMAC.toBEBytes 4) := by
  unfold CryptoGames.HMAC.sha256With
  have hfold : ∀ (blks : List HwBytes),
      blks.foldl nvCrypto.F CryptoGames.HMAC.sha256IV = CryptoGames.HMAC.sha256IV := by
    intro blks
    induction blks with
    | nil => rfl
    | cons _ tl ih => exact ih
  rw [hfold]

theorem computeMac_nvCrypto_len (sId rId : IdentityKey) (macKey : BitVec 256)
    (content : HwBytes) :
    (computeMac nvCrypto.F sId rId macKey content).length = macLength := by
  unfold computeMac CryptoGames.HMAC.hmacSha256Trunc8 CryptoGames.HMAC.hmacWith
  simp only [sha256With_nvCrypto]
  rfl

theorem publicKey_deserialize_serialize (rk : PublicKey) :
    PublicKey.deserialize rk.serialize = .ok rk := by
  rcases rk with ⟨⟨l, hl⟩⟩
  unfold PublicKey.deserialize PublicKey.serialize
  dsimp only [List.head?, List.tail, List.Vector.toList]
  have hlen : 32 ≤ l.length := Nat.le_of_eq hl.symm
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hlen, ↓reduceDIte]
  apply congrArg Except.ok
  apply congrArg PublicKey.mk
  apply Subtype.ext
  exact List.take_of_length_le (Nat.le_of_eq hl)

theorem tryFrom_protoSignalCodec_new_nv
    (macKey : BitVec 256) (addrs : Option HwBytes) (rk : PublicKey)
    (ctr prev : BitVec 32) (ct : HwBytes) (sId rId : IdentityKey) (pq : HwBytes)
    (hct : ct.length < 2 ^ 64) (hpq : pq.length < 2 ^ 64)
    (haddrs : ∀ a, addrs = some a → a.length < 2 ^ 64) :
    SignalMessage.tryFrom protoSignalCodec
      (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
        sId rId pq).serialized =
    .ok (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
        sId rId pq) := by
  let pm : ProtoSignalMessage :=
    { ratchetKey := some rk.serialize
      counter := some ctr
      previousCounter := some prev
      ciphertext := some ct
      pqRatchet := if pq.isEmpty then none else some pq
      addresses := addrs }
  let body := protoSignalCodec.encode pm
  let content := versionByte currentVersion :: body
  let mac := computeMac nvCrypto.F sId rId macKey content
  have hmacLen : mac.length = macLength := computeMac_nvCrypto_len sId rId macKey content
  have hser : (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).serialized = content ++ mac := rfl
  have hlen : ¬ ((content ++ mac).length < macLength + 1) := by
    simp only [List.length_append, content, List.length_cons, hmacLen, macLength]
    omega
  have htake : (content ++ mac).take ((content ++ mac).length - macLength) = content := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.take_left
  have hfit : CryptoVerification.LibsignalProtoCodec.LengthsFit pm := by
    intro v hv
    rcases hv with hrk | hct' | hpq' | haddr'
    · cases hrk
      rcases rk with ⟨⟨l, hl⟩⟩
      simp [PublicKey.serialize, hl]
    · cases hct'; exact hct
    · by_cases he : pq.isEmpty
      · simp [pm, he] at hpq'
      · simp [pm, he] at hpq'; subst hpq'; exact hpq
    · exact haddrs v haddr'
  have hdec : protoSignalCodec.decode body = some pm :=
    CryptoVerification.LibsignalProtoCodec.protoSignalCodec_roundTrip pm hfit
  have hpqGet : (if pq.isEmpty then none else some pq).getD [] = pq := by
    cases pq <;> rfl
  have hhead : (content ++ mac).headD 0 = versionByte currentVersion := by
    simp [content]
  have hdrop1 : content.drop 1 = body := rfl
  unfold SignalMessage.tryFrom
  rw [hser]
  dsimp only
  simp only [hlen, ↓reduceIte, htake, hdrop1, hhead,
    show versionByte currentVersion >>> 4 = currentVersion from rfl,
    show ¬ (currentVersion < preKyberVersion) by simp [currentVersion, preKyberVersion],
    show ¬ (currentVersion < currentVersion) by simp,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [hdec]
  dsimp only [pm]
  rw [publicKey_deserialize_serialize, hpqGet]
  rfl

/-! ## Opaque Large-Vector Wrappers -/

@[irreducible] def nvVec1568 : List.Vector (BitVec 8) 1568 :=
  List.Vector.replicate 1568 0#8

theorem nvVec1568_eq : List.Vector.replicate 1568 0#8 = nvVec1568 := by
  unfold nvVec1568; rfl

@[irreducible] def nvVec3168 : List.Vector (BitVec 8) 3168 :=
  List.Vector.replicate 3168 0#8

theorem nvVec3168_eq : List.Vector.replicate 3168 0#8 = nvVec3168 := by
  unfold nvVec3168; rfl

theorem nvCoins64A_len : nvCoins64A.length = 64 := rfl

@[expose] def nvSeedA : List.Vector (BitVec 8) 64 := ⟨nvCoins64A, nvCoins64A_len⟩

theorem nvMlKem_fromSeed_hdr (s : List.Vector (BitVec 8) 64) :
    (nvMlKem.fromSeed s).1.toList = List.replicate 64 0#8 := by
  rw [CryptoVerification.LibsignalSpqrV1.MlKem.fromSeed_hdr]
  simp [nvMlKem, CryptoVerification.LibsignalSpqrV1.pk1Off]

@[expose, irreducible] def nvEk1152 : HwBytes :=
  (nvMlKem.fromSeed nvSeedA).2.1.toList

@[expose, irreducible] def nvDk2400 : HwBytes :=
  (nvMlKem.fromSeed nvSeedA).2.2.toList

theorem nvEk1152_def :
    (nvMlKem.fromSeed nvSeedA).2.1.toList = nvEk1152 := by
  unfold nvEk1152; rfl

theorem nvDk2400_def :
    (nvMlKem.fromSeed nvSeedA).2.2.toList = nvDk2400 := by
  unfold nvDk2400; rfl

theorem nvEk1152_len : nvEk1152.length = 1152 := by
  unfold nvEk1152; exact List.Vector.toList_length _

theorem nvDk2400_len : nvDk2400.length = 2400 := by
  unfold nvDk2400; exact List.Vector.toList_length _

theorem isEmpty_false_of_pos_len {bs : HwBytes} (h : 0 < bs.length) :
    bs.isEmpty = false := by
  cases bs with
  | nil => simp at h
  | cons _ _ => rfl

theorem nvEk1152_isEmpty : nvEk1152.isEmpty = false :=
  isEmpty_false_of_pos_len (by rw [nvEk1152_len]; omega)

theorem nvDk2400_isEmpty : nvDk2400.isEmpty = false :=
  isEmpty_false_of_pos_len (by rw [nvDk2400_len]; omega)

theorem nvVec1568_beq_self : (nvVec1568 == nvVec1568) = true := beq_self_eq_true _

theorem nvVec3168_beq_self : (nvVec3168 == nvVec3168) = true := beq_self_eq_true _

theorem nvEk1152_beq_self : (nvEk1152 == nvEk1152) = true := beq_self_eq_true _

theorem nvDk2400_beq_self : (nvDk2400 == nvDk2400) = true := beq_self_eq_true _

theorem nvEk1152_ne_nvDk2400 : nvEk1152 ≠ nvDk2400 := by
  intro h
  have hl := congrArg List.length h
  rw [nvEk1152_len, nvDk2400_len] at hl
  omega

theorem nvEk1152_beq_nvDk2400 : (nvEk1152 == nvDk2400) = false :=
  beq_eq_false_iff_ne.mpr nvEk1152_ne_nvDk2400

theorem nvDk2400_beq_nvEk1152 : (nvDk2400 == nvEk1152) = false :=
  beq_eq_false_iff_ne.mpr nvEk1152_ne_nvDk2400.symm

theorem nvEk1152_ne_nil : nvEk1152 ≠ [] := by
  intro h
  have hl := nvEk1152_len
  rw [h] at hl
  simp at hl

theorem nvDk2400_ne_nil : nvDk2400 ≠ [] := by
  intro h
  have hl := nvDk2400_len
  rw [h] at hl
  simp at hl

theorem decide_nvVec1568_self : decide (nvVec1568 = nvVec1568) = true :=
  decide_eq_true rfl

theorem decide_nvVec3168_self : decide (nvVec3168 = nvVec3168) = true :=
  decide_eq_true rfl

theorem decide_nvEk1152_self : decide (nvEk1152 = nvEk1152) = true :=
  decide_eq_true rfl

theorem decide_nvDk2400_self : decide (nvDk2400 = nvDk2400) = true :=
  decide_eq_true rfl

theorem decide_nvEk1152_nvDk2400 : decide (nvEk1152 = nvDk2400) = false :=
  decide_eq_false nvEk1152_ne_nvDk2400

theorem decide_nvDk2400_nvEk1152 : decide (nvDk2400 = nvEk1152) = false :=
  decide_eq_false nvEk1152_ne_nvDk2400.symm

/-! ## `SignalMessage` MAC and `Mut.exec` Decryption Combinators -/

theorem addrsE_len_lt (u : CryptoVerification.LibsignalTripleRatchetRepr.UuidParser)
    (p1 p2 : Party) (a : HwBytes)
    (h : serializedPartyAddresses u p1 p2 = some a) : a.length < 2 ^ 64 := by
  unfold serializedPartyAddresses at h
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure] at h
  cases hs : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse u
      (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName p1)) with
  | none => simp [hs] at h
  | some s =>
    cases hr : CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse u
        (CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName p2)) with
    | none => simp [hs, hr] at h
    | some r =>
      simp only [hs, hr, Option.some.injEq] at h
      subst h
      simp only [CryptoVerification.LibsignalTripleRatchetRepr.addrBytes,
        List.length_append, List.length_cons, List.length_nil, List.Vector.toList_length]
      omega

theorem verifyMacWithAddresses_new_nv
    (macKey : BitVec 256) (addrs expected : Option HwBytes) (rk : PublicKey)
    (ctr prev : BitVec 32) (ct : HwBytes) (sId rId : IdentityKey) (pq : HwBytes)
    (had : LibsignalAead.addressCheckPasses addrs expected = true) :
    (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr prev ct
      sId rId pq).verifyMacWithAddresses nvCrypto.F expected sId rId macKey = true := by
  unfold SignalMessage.verifyMacWithAddresses SignalMessage.verifyMac
  let content := serializeContent protoSignalCodec currentVersion rk ctr prev ct pq addrs
  let mac := computeMac nvCrypto.F sId rId macKey content
  have hmacLen : mac.length = macLength := computeMac_nvCrypto_len sId rId macKey content
  have hser : (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).serialized = content ++ mac := rfl
  have hadEq : (SignalMessage.new nvCrypto.F protoSignalCodec currentVersion macKey addrs rk ctr
      prev ct sId rId pq).addresses = addrs := rfl
  rw [hser, hadEq]
  have htake : (content ++ mac).take ((content ++ mac).length - macLength) = content := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.take_left
  have hdrop : (content ++ mac).drop ((content ++ mac).length - macLength) = mac := by
    rw [List.length_append, hmacLen, Nat.add_sub_cancel]
    exact List.drop_left
  rw [htake, hdrop]
  simp only [mac, beq_self_eq_true, had, Bool.and_self]

theorem mut_exec_bind {S α β : Type} (m : Mut S α) (f : α → Mut S β) (s : S) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  rcases hm : Mut.exec m s with ⟨_ | _, s'⟩
  · change (match m s with | (a, s1) => (ExceptT.bindCont f a) s1) = _
    change m s = _ at hm
    rw [hm]; rfl
  · change (match m s with | (a, s1) => (ExceptT.bindCont f a) s1) = _
    change m s = _ at hm
    rw [hm]; rfl

theorem mut_exec_get {S : Type} (s : S) :
    Mut.exec (get : Mut S S) s = (.ok s, s) := rfl

theorem mut_exec_pure {S α : Type} (x : α) (s : S) :
    Mut.exec (pure x : Mut S α) s = (.ok x, s) := rfl

theorem mut_exec_set {S : Type} (s' s : S) :
    Mut.exec (set s' : Mut S Unit) s = (.ok (), s') := rfl

theorem mut_exec_modify {S : Type} (f : S → S) (s : S) :
    Mut.exec (modify f : Mut S Unit) s = (.ok (), f s) := rfl

theorem mut_exec_liftE {S α : Type} (x : Except SignalProtocolError α) (s : S) :
    Mut.exec (liftE x : Mut S α) s = (x, s) := by
  cases x <;> rfl

theorem mut_exec_onRatchet {PQ α : Type} (m : Mut RatchetState α) (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      match Mut.exec m t.ratchet with
      | (.ok a, r') => (.ok a, { t with ratchet := r' })
      | (.error e, r') => (.error e, { t with ratchet := r' }) := by
  unfold TripleRatchet.onRatchet zoom
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  rcases hm : Mut.exec m t.ratchet with ⟨_ | _, r'⟩ <;>
    (rw [mut_exec_bind, mut_exec_set]; dsimp only; rw [mut_exec_liftE])

theorem mut_exec_decrypt_ok {PQ PQC : Type}
    (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option HwBytes) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256)
    (r0 r1 r2 : RatchetState) (pq0 pq1 : PQ) (locId remId : IdentityKey)
    (ck : ChainKey) (mkGen : MessageKeyGenerator) (salt : Option (List.Vector (BitVec 8) 32))
    (mk : MessageKeys) (ptext : HwBytes)
    (hens : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins) r0 =
      (.ok ck, r1))
    (hcons : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType)
      r1 = (.ok mkGen, r2))
    (hpan : spqr.recvPanics pq0 msg.pqRatchet = false)
    (hspqr : spqr.recv pq0 msg.pqRatchet = .ok (pq1, salt))
    (hgen : mkGen.generateKeys C.F salt = mk)
    (hmac : msg.verifyMacWithAddresses C.F expected remId locId mk.macKey = true)
    (hcbc : aesCbcDecrypt C.D mk.cipherKey mk.iv msg.ciphertext = some ptext) :
    Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins)
      ⟨r0, pq0, locId, remId⟩ =
      (.ok ptext, ⟨r2, pq1, locId, remId⟩) := by
  unfold TripleRatchet.decrypt
  rw [mut_exec_bind, mut_exec_onRatchet]
  dsimp only
  rw [hens]
  dsimp only
  rw [mut_exec_bind, mut_exec_onRatchet]
  dsimp only
  rw [hcons]
  dsimp only
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  rw [hpan]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hspqr]
  dsimp only
  rw [mut_exec_bind, mut_exec_pure]
  dsimp only
  rw [hgen, hmac]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hcbc]
  dsimp only
  rw [mut_exec_bind, mut_exec_modify]
  dsimp only
  rw [mut_exec_pure]

theorem mut_exec_tryDecryptWithState_ok {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option HwBytes) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256)
    (s0 sTaken : SessionState PQ) (tr0 tr1 : TripleRatchet PQ) (ptext : HwBytes)
    (htake : Mut.exec TripleRatchet.fromSessionState s0 = (.ok tr0, sTaken))
    (hdec : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr0 =
      (.ok ptext, tr1)) :
    Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) s0 =
      (.ok ptext, (tr1.applyToSessionState sTaken).clearUnacknowledgedPreKeyMessage) := by
  unfold SessionState.tryDecryptWithState
  rw [mut_exec_bind, htake]
  dsimp only
  rw [hdec]
  dsimp only
  rw [mut_exec_bind, mut_exec_liftE]
  dsimp only
  rw [mut_exec_bind, mut_exec_modify]
  dsimp only
  rw [mut_exec_pure]

end Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
