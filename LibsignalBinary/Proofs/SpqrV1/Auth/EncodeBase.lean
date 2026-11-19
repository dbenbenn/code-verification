/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Specifications and Step Lemmas for `encode<Authenticator>` (`[local#1, 2]`)

Provides instruction decode tables (`0x372d4..0x37520` and `0x522c0..0x52544`), pure
Protobuf equivalence lemmas (`encodeAuthMsg`), specifications (`authEncodePinnedSpec`,
`authEncodeSpec`), callee wrappers, and shared basic-block step lemmas for both
monomorphizations of `prost::encoding::message::encode::<Authenticator, Vec<u8>>`.
-/

public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Instruction Decode Tables and Symbols -/

abbrev authEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#1]"

abbrev authEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]"

/-- Stack budget `64 + (0x30 + resStack)` for `encode<Authenticator>` (`64` B frame plus `encode_varint`). -/
abbrev authEncodeStackOf (resStack : Nat) : Nat := 64 + (0x30 + resStack)

abbrev authEncodeStack : Nat := authEncodeStackOf doReserveStack

abbrev authEncodeStackX : Nat := authEncodeStackOf doReserveStackX

/-! ## Pure Model Equivalence and Decomposition Lemmas -/

/-- Length-delimited Protobuf bytes (`tag = 2`) appended by `encode<Authenticator>`. -/
abbrev encodeAuthMsg (auth : AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth

private theorem or_80_truncate8_and_7f (a : BitVec 64) :
    (a.truncate 8 ||| 0x80#8) = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

private theorem protoEncodeVarintAux_eq_codec_of_lt (fuel : Nat) (a : BitVec 64)
    (hbound : a >>> (7 * fuel) < 0x80#64) :
    Proto.encodeVarintAux (fuel + 1) a =
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux (fuel + 1) a := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero] at hbound
    have h' : a.toNat < 0x80 := BitVec.lt_def.mp hbound
    simp only [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux,
      hbound, h', ↓reduceIte]
  | succ fuel ih =>
    rw [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      have hb' : (a >>> 7) >>> (7 * fuel) < 0x80#64 := by
        have hsh : (a >>> 7) >>> (7 * fuel) = a >>> (7 * (fuel + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
            ← Nat.pow_add]
          congr 2; omega
        rw [hsh]; exact hbound
      simp only [h, h', ↓reduceIte, or_80_truncate8_and_7f a, ih (a >>> 7) hb']
      rfl

theorem protoEncodeVarint_eq_codec (a : BitVec 64) :
    Proto.encodeVarint a = CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  refine protoEncodeVarintAux_eq_codec_of_lt 9 a ?_
  change a >>> 63 < 0x80#64
  bv_bits

theorem protoEncodeKey_1_lengthDelimited :
    Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl

theorem protoEncodeKey_2_lengthDelimited :
    Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl

theorem protoEncodeBytesField_nil (tag : BitVec 32) :
    Proto.encodeBytesField tag [] = [] := rfl

theorem protoEncodeBytesField_1_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 1#32 bs =
      [0x0a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_2_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 2#32 bs =
      [0x12#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_2_lengthDelimited, protoEncodeVarint_eq_codec]

theorem encodeAuthMsg_eq_parts (auth : AuthenticatorPB) :
    encodeAuthMsg auth =
      [0x12#8] ++
        CryptoVerification.LibsignalProtoCodec.encodeVarint
          (BitVec.ofNat 64 (authenticatorPBEncodedLen auth)) ++
        Proto.encodeBytesField 1#32 auth.rootKey ++
        Proto.encodeBytesField 2#32 auth.macKey := by
  have hlen : (ProtoAuthenticator.encodeRaw auth).length = authenticatorPBEncodedLen auth :=
    authenticatorPBEncodedLen_eq_proto auth
  dsimp only [encodeAuthMsg, Proto.encodeMessage]
  rw [hlen, protoEncodeKey_2_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [ProtoAuthenticator.encodeRaw, List.append_assoc]

theorem encodeAuthMsg_length (auth : AuthenticatorPB) :
    (encodeAuthMsg auth).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint
            (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length +
        (Proto.encodeBytesField 1#32 auth.rootKey).length +
        (Proto.encodeBytesField 2#32 auth.macKey).length := by
  rw [encodeAuthMsg_eq_parts]
  simp only [List.length_append, List.length_singleton, Nat.add_assoc]

theorem bytesField_1_length_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.encodeBytesField 1#32 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  rw [protoEncodeBytesField_1_of_ne_nil hne]
  simp only [List.length_append, List.length_singleton]

theorem bytesField_2_length_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.encodeBytesField 2#32 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  rw [protoEncodeBytesField_2_of_ne_nil hne]
  simp only [List.length_append, List.length_singleton]

theorem authenticatorPBEncodedLen_eq_fields_len (auth : AuthenticatorPB) :
    authenticatorPBEncodedLen auth =
      (Proto.encodeBytesField 1#32 auth.rootKey).length +
        (Proto.encodeBytesField 2#32 auth.macKey).length := by
  have h : (ProtoAuthenticator.encodeRaw auth).length = authenticatorPBEncodedLen auth :=
    authenticatorPBEncodedLen_eq_proto auth
  rw [← h]
  simp only [ProtoAuthenticator.encodeRaw, List.length_append]

/-! ## Specifications of `encode<Authenticator> [local#1, 2]` -/

/-- Pinned ghost arguments `(authA, g, auth, v, cap, ptr, bs)` for
`prost::encoding::message::encode::<Authenticator, Vec<u8>>`. -/
structure AuthEncodePinnedGhost where
  authA : BitVec 64
  g : AuthenticatorPBGhost
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments for `encode<Authenticator>`. -/
structure AuthEncodeGhost where
  authA : BitVec 64
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `encode<Authenticator>` parameterized by `resStack`. -/
@[expose] def authEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) : Spec AuthEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62)⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `encode<Authenticator>` parameterized by `resStack`. -/
@[expose] def authEncodeSpecOf (resStack : Nat) (A : RustAlloc) : Spec AuthEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62)⌝ ∗
      authenticatorPBAt A x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBAt A x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev authEncodePinnedSpec (A : RustAlloc) : Spec AuthEncodePinnedGhost :=
  authEncodePinnedSpecOf doReserveStack A

abbrev authEncodePinnedSpecX (A : RustAlloc) : Spec AuthEncodePinnedGhost :=
  authEncodePinnedSpecOf doReserveStackX A

abbrev authEncodeSpec (A : RustAlloc) : Spec AuthEncodeGhost :=
  authEncodeSpecOf doReserveStack A

abbrev authEncodeSpecX (A : RustAlloc) : Spec AuthEncodeGhost :=
  authEncodeSpecOf doReserveStackX A

theorem stackAt_authEncode {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (authEncodeStackOf resStack) =
      stackAt (sp - 64#64) (0x30 + resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (0x30 + resStack) 8 (by omega)
  have heq : 0x30 + resStack + 8 * 8 = authEncodeStackOf resStack := by
    dsimp [authEncodeStackOf]; omega
  rw [heq] at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_encodeVarint_eq_doReserve64 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (0x30 + resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ stackAt sp1 resStack := by
  have h := ProofLib.stackAt_split_bottom sp1 resStack 48 (by omega)
  have heq : resStack + 48 = 0x30 + resStack := by omega
  simpa only [heq] using h

theorem sp_sub_64_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 64#64) &&& 15#64 = 0#64 := by
  bv_bits

/-- Pointer and length fields of `AuthenticatorPB` read by `encode<Authenticator>`. -/
@[expose] def authPBElemsAt (authA rkPtr mkPtr : BitVec 64) (auth : AuthenticatorPB) : SepProp :=
  ((authA + 8#64) ↦₆₄ rkPtr) ∗
  ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
  (rkPtr ↦ₛ auth.rootKey) ∗
  ((authA + 32#64) ↦₆₄ mkPtr) ∗
  ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
  (mkPtr ↦ₛ auth.macKey)

/-- Frame remainder of `authenticatorPBPinnedAt` after extracting `authPBElemsAt`. -/
@[expose] def authPBRestAt (A : RustAlloc) (g : AuthenticatorPBGhost) (authA : BitVec 64)
    (auth : AuthenticatorPB) : SepProp :=
  vecU8ElemRestAt A authA g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
  vecU8ElemRestAt A (authA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey

theorem authenticatorPBPinnedAt_eq_elems (A : RustAlloc) (g : AuthenticatorPBGhost)
    (authA : BitVec 64) (auth : AuthenticatorPB)
    (hrk : g.rootKey.cap = 0 → auth.rootKey = [])
    (hmk : g.macKey.cap = 0 → auth.macKey = []) :
    authenticatorPBPinnedAt A g authA auth =
      authPBElemsAt authA g.rootKey.ptr g.macKey.ptr auth ∗
      authPBRestAt A g authA auth := by
  unfold authenticatorPBPinnedAt authPBElemsAt authPBRestAt
  rw [vecU8At_eq_repeatedBytesElemAt A authA g.rootKey.cap g.rootKey.ptr auth.rootKey hrk,
    vecU8At_eq_repeatedBytesElemAt A (authA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey hmk]
  unfold repeatedBytesElemAt
  have h32 : authA + 24#64 + 8#64 = authA + 32#64 := by bv_omega
  have h40 : authA + 24#64 + 16#64 = authA + 40#64 := by bv_omega
  rw [h32, h40]
  ac_rfl

theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    rw [hP, vecU8At_eq_header_sep_buf] at hm
    convert hm using 1; ac_rfl
  unfold vecU8Buf at hhm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

theorem vecU8At_open_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A v cap ptr bs =
      ∃∗ y : BitVec 8,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader, vecU8Buf_eq_open_one A cap ptr bs hlt]
  simp only [sepExists_sepConj_right]
  congr 1; funext y; ac_rfl

theorem vecU8At_close_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs) =
    vecU8At A v cap ptr (bs ++ [byte]) := by
  rw [bv_len_add_one bs byte, vecU8At_eq_header_sep_buf, vecHeader,
    ← vecU8Buf_snoc_eq A cap ptr bs byte hlt]
  ac_rfl

/-- Preservation of callee-saved registers `x25..x28` and `StepInv s0 s`. -/
@[expose] def AuthEncodeCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem AuthEncodeCalleeSaved.refl (s0 : State) : AuthEncodeCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem AuthEncodeCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSaved s0 s1) (h12 : AuthEncodeCalleeSaved s1 s2) :
    AuthEncodeCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h01.2.2.2.2.2.trans h12.2.2.2.2.2⟩

theorem AuthEncodeCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : AuthEncodeCalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem AuthEncodeCalleeSaved.step {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSaved s0 s1)
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    AuthEncodeCalleeSaved s0 s2 :=
  h01.trans ⟨hx25, hx26, hx27, hx28, hvregs, hinv⟩

@[expose] def withAuthEncodeCS {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜AuthEncodeCalleeSaved s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withAuthEncodeCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withAuthEncodeCS s0 spec) := by
  refine subroutine_ok_mono h (fun x R s hpre => ?_) (fun _ _ _ _ hpost => hpost)
  rw [withAuthEncodeCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

end CryptoVerification.SpqrV1.Auth
