/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<Authenticator, Vec<u8>> [local#1]`

Defines pure byte-slice helpers for `encodeAuthMsg` and verifies
`encode<Authenticator> [local#1]` (`0x372d4`, calling `encode_varint [local#2]` and
`do_reserve_and_handle [local#2]`) on `tripleRatchetProgAtExt`.
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
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
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

/-! ## Pure and Memory Helpers for `encode<Authenticator>` -/

/-- Header bytes (`0x12` tag plus varint-encoded payload length) of `encodeAuthMsg auth`. -/
@[expose] def authHeaderBytes (auth : AuthenticatorPB) : List (BitVec 8) :=
  [0x12#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
    (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))

/-- Field 1 (`root_key`) bytes of `encodeAuthMsg auth`. -/
@[expose] def authRootKeyBytes (auth : AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeBytesField 1#32 auth.rootKey

/-- Field 2 (`mac_key`) bytes of `encodeAuthMsg auth`. -/
@[expose] def authMacKeyBytes (auth : AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeBytesField 2#32 auth.macKey

theorem bs0_append_authHeaderBytes (bs0 : List (BitVec 8)) (auth : AuthenticatorPB) :
    (bs0 ++ [0x12#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 (authenticatorPBEncodedLen auth)) = bs0 ++ authHeaderBytes auth := by
  simp only [authHeaderBytes, List.append_assoc]

theorem bs_append_authRootKeyBytes_of_ne_empty (bs1 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hrk : auth.rootKey.isEmpty = false) :
    ((bs1 ++ [0x0a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 auth.rootKey.length)) ++ auth.rootKey = bs1 ++ authRootKeyBytes auth := by
  rw [authRootKeyBytes, protoEncodeBytesField_1_of_ne_nil (List.isEmpty_eq_false_iff.mp hrk)]
  simp only [List.append_assoc]

theorem bs_append_authRootKeyBytes_of_empty (bs1 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hrk : auth.rootKey.isEmpty = true) : bs1 ++ authRootKeyBytes auth = bs1 := by
  simp only [authRootKeyBytes, List.isEmpty_iff.mp hrk, protoEncodeBytesField_nil, List.append_nil]

theorem bs_append_authMacKeyBytes_of_ne_empty (bs2 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hmk : auth.macKey.isEmpty = false) :
    ((bs2 ++ [0x12#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 auth.macKey.length)) ++ auth.macKey = bs2 ++ authMacKeyBytes auth := by
  rw [authMacKeyBytes, protoEncodeBytesField_2_of_ne_nil (List.isEmpty_eq_false_iff.mp hmk)]
  simp only [List.append_assoc]

theorem bs_append_authMacKeyBytes_of_empty (bs2 : List (BitVec 8)) (auth : AuthenticatorPB)
    (hmk : auth.macKey.isEmpty = true) : bs2 ++ authMacKeyBytes auth = bs2 := by
  simp only [authMacKeyBytes, List.isEmpty_iff.mp hmk, protoEncodeBytesField_nil, List.append_nil]

theorem bs0_append_encodeAuthMsg (bs0 : List (BitVec 8)) (auth : AuthenticatorPB) :
    ((bs0 ++ authHeaderBytes auth) ++ authRootKeyBytes auth) ++ authMacKeyBytes auth =
      bs0 ++ encodeAuthMsg auth := by
  rw [encodeAuthMsg_eq_parts, authHeaderBytes, authRootKeyBytes, authMacKeyBytes]
  simp only [List.append_assoc]

theorem encodeAuthMsg_len_split (auth : AuthenticatorPB) :
    (encodeAuthMsg auth).length =
      (authHeaderBytes auth).length + (authRootKeyBytes auth).length + (authMacKeyBytes auth).length := by
  simpa only [List.nil_append, List.length_append, Nat.add_assoc] using
    (congrArg List.length (bs0_append_encodeAuthMsg [] auth)).symm

theorem authHeaderBytes_len_bounds (auth : AuthenticatorPB) :
    2 ≤ (authHeaderBytes auth).length ∧ (authHeaderBytes auth).length ≤ 11 := by
  have hb := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))
  simp only [authHeaderBytes, List.length_append, List.length_singleton]; omega

theorem authRootKeyBytes_len_of_ne_empty (auth : AuthenticatorPB) (hrk : auth.rootKey.isEmpty = false) :
    (authRootKeyBytes auth).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.rootKey.length)).length +
        auth.rootKey.length :=
  bytesField_1_length_of_ne_nil (List.isEmpty_eq_false_iff.mp hrk)

theorem authMacKeyBytes_len_of_ne_empty (auth : AuthenticatorPB) (hmk : auth.macKey.isEmpty = false) :
    (authMacKeyBytes auth).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 auth.macKey.length)).length +
        auth.macKey.length :=
  bytesField_2_length_of_ne_nil (List.isEmpty_eq_false_iff.mp hmk)

theorem cap_toNat_eq_of_beq {cap : BitVec 64} {n : Nat}
    (h : (cap == BitVec.ofNat 64 n) = true) (hlt : n < 2 ^ 64) : cap.toNat = n := by
  rw [beq_iff_eq.mp h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem lt_cap_toNat_of_beq_false {cap : BitVec 64} {n : Nat}
    (h : (cap == BitVec.ofNat 64 n) = false) (hle : n ≤ cap.toNat) (hlt : n < 2 ^ 64) :
    n < cap.toNat := by
  have hne : cap.toNat ≠ n := fun heq => beq_eq_false_iff_ne.mp h <|
    BitVec.eq_of_toNat_eq (by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt])
  omega

theorem reserveCap_one_bounds {cap len : Nat} (heq : cap = len) (hfit : len + 5 < 2 ^ 62) :
    reserveCap cap len 1 + 1 ≤ 2 ^ 63 ∧
    len < (BitVec.ofNat 64 (reserveCap cap len 1)).toNat ∧
    cap ≤ (BitVec.ofNat 64 (reserveCap cap len 1)).toNat := by
  have hb : len + 1 ≤ reserveCap cap len 1 ∧ reserveCap cap len 1 ≤ 2 * len + 8 := by
    unfold reserveCap; omega
  have htoNat : (BitVec.ofNat 64 (reserveCap cap len 1)).toNat = reserveCap cap len 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [htoNat]; exact ⟨by omega, by omega, by omega⟩

theorem vecU8At_bounds_of_satisfies {m : Memory} {A : RustAlloc}
    {v cap ptr : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} (h : m ⊨ vecU8At A v cap ptr bs ∗ F) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
  have h' : m ⊨ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F) := by
    rw [vecU8At] at h; convert h using 1; ac_rfl
  rw [satisfies_pure_sepConj] at h'; exact h'.1

theorem authenticatorPBPinnedAt_bounds_of_satisfies {m : Memory} {A : RustAlloc}
    {g : AuthenticatorGhost} {authA : BitVec 64} {auth : AuthenticatorPB} {F : SepProp}
    (h : m ⊨ authenticatorPBPinnedAt A g authA auth ∗ F) :
    auth.rootKey.length < 2 ^ 63 ∧ auth.macKey.length < 2 ^ 63 ∧
    (g.rootKey.cap = 0 → auth.rootKey = []) ∧
    (g.macKey.cap = 0 → auth.macKey = []) := by
  rw [authenticatorPBPinnedAt] at h
  have hrk := vecU8At_bounds_of_satisfies (A := A) (v := authA)
    (cap := g.rootKey.cap) (ptr := g.rootKey.ptr) (bs := auth.rootKey)
    (F := vecU8At A (authA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey ∗ F)
    (by convert h using 1; ac_rfl)
  have hmk := vecU8At_bounds_of_satisfies (A := A) (v := authA + 24#64)
    (cap := g.macKey.cap) (ptr := g.macKey.ptr) (bs := auth.macKey)
    (F := vecU8At A authA g.rootKey.cap g.rootKey.ptr auth.rootKey ∗ F)
    (by convert h using 1; ac_rfl)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h0; apply List.eq_nil_iff_length_eq_zero.mpr; have hle := hrk.1; rw [h0] at hle; exact Nat.eq_zero_of_le_zero hle
  · intro h0; apply List.eq_nil_iff_length_eq_zero.mpr; have hle := hmk.1; rw [h0] at hle; exact Nat.eq_zero_of_le_zero hle

theorem authEncode_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : AuthEncodeGhost} {g : AuthenticatorPBGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (authEncodePinnedSpecOf resStack A).post
      ⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (authEncodeSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [authEncodePinnedSpecOf] at hq; dsimp only [authEncodeSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
    A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ authenticatorPBPinnedAt A g x.authA x.auth ∗ Rest := by convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ authenticatorPBAt A x.authA x.auth ∗ Rest := by
    rw [authenticatorPBAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]; exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

/-- Lifts a pinned `authEncodePinnedSpecOf` proof to `authEncodeSpecOf`. -/
theorem authEncode_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (authEncodePinnedSpecOf resStack A)) :
    subroutine_ok prog entry (authEncodeSpecOf resStack A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [authEncodeSpecOf] at hpre; rw [authenticatorPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · exact Or.inl ⟨hret, hcc, authEncode_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.Auth
