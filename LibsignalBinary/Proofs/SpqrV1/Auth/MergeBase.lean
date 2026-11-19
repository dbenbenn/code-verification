/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Base Definitions and Step Lemmas for `Authenticator::merge`

Defines the decode table (`authMergeBin`), capacity-bounded `authenticatorPBCapAt` predicate,
`authMergeSpec` contract, pure `ProtoAuthenticator.mergeField` lemmas, and per-branch
step/exit lemmas for `prost::encoding::message::merge::<Authenticator, &mut &[u8]>` (`0x4df38`).
-/

public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

theorem Entails.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ a, P a ⊢ Q) : (∃∗ a, P a) ⊢ Q :=
  Arm64.Entails.sepExists_elim h

theorem SepWPp.pure_elim {prog : Program} {ret_pc : BitVec 64} {s : State} {φ : Prop} {P : SepProp}
    {post panic : State → SepProp → Prop} (h : φ → SepWPp prog ret_pc s P post panic) :
    SepWPp prog ret_pc s (⌜φ⌝ ∗ P) post panic := by
  intro F hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 F hm.2 hL

theorem SepWPp.pure_elim2 {prog : Program} {ret_pc : BitVec 64} {s : State} {φ : Prop} {P Q : SepProp}
    {post panic : State → SepProp → Prop} (h : φ → SepWPp prog ret_pc s (P ∗ Q) post panic) :
    SepWPp prog ret_pc s (P ∗ ⌜φ⌝ ∗ Q) post panic := by
  apply SepWPp.weaken_pre (P' := ⌜φ⌝ ∗ (P ∗ Q)) (Entails.of_eq (by ac_rfl))
  exact SepWPp.pure_elim h

/-! ## Decode Table and Offset Lemmas -/

theorem skipBelow3_97_eq_stackAt_96 (sp : BitVec 64) :
    skipBelow3 sp 97 = stackAt (sp - 96#64) (skipField3Stack 96) :=
  congrArg (stackAt (sp - 96#64)) (rfl : 97 * 0x60 + decodeVarint2Stack = skipField3Stack 96)

theorem memRegion_48_split_96 (sp : BitVec 64) :
    memRegion (sp - 96#64) 48 =
      (∃∗ v : BitVec 64, (sp - 96#64) ↦₆₄ v) ∗ memRegion (sp - 88#64) 40 := by
  rw [memRegion_48_split (sp - 96#64), bv_sub_add_lit sp 96 8]

theorem memRegion8_memRegion40_entails_48 (sp : BitVec 64) :
    memRegion (sp - 96#64) 8 ∗ memRegion (sp - 88#64) 40 ⊢
      memRegion (sp - 96#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 96 8] at s1
  exact Entails.of_eq s1.symm

/-! ## Capacity-Bounded `AuthenticatorPB` Predicate and Specification -/

/-- `ProtoAuthenticator` at `a` (48 bytes) with `BytesMergeCapOk cap bsLen` on both
`root_key` (`a`) and `mac_key` (`a + 0x18`). -/
@[expose] def authenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr auth.rootKey) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr auth.macKey)

theorem vecU8CapAt_mono (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr bs) ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap m⌝ ∗ vecU8At A a cap ptr bs) := by
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun hok => ?_
  refine Entails.trans (Entails.pure_right (bytesMergeCapOk_mono hok hle) (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem authenticatorPBCapAt_mono (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator)
    {m n : Nat} (hle : m ≤ n) :
    authenticatorPBCapAt A a n auth ⊢ authenticatorPBCapAt A a m auth :=
  sepConj_mono (vecU8CapAt_mono A a auth.rootKey hle)
    (vecU8CapAt_mono A (a + 0x18#64) auth.macKey hle)

theorem vecU8CapAt_entails_vecU8 (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr bs) ⊢
      rustBytesVecAt A a bs := by
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem authenticatorPBCapAt_entails_authenticatorPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBCapAt A a n auth ⊢ authenticatorPBAt A a auth :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n auth.rootKey)
    (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n auth.macKey)

theorem authenticatorPBAt_entails_exists (A : RustAlloc) (a : BitVec 64) (m : ProtoAuthenticator) :
    authenticatorPBAt A a m ⊢ ∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m' :=
  Entails.sepExists_intro m

theorem authenticatorPBCapAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : ProtoAuthenticator) :
    authenticatorPBCapAt A a n m ⊢ ∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m' :=
  Entails.trans (authenticatorPBCapAt_entails_authenticatorPBAt A a n m)
    (authenticatorPBAt_entails_exists A a m)

theorem authenticatorPBPinnedAt_zero_entails_cap (A : RustAlloc) (p1 p2 a : BitVec 64)
    (n : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ⟨⟨0#64, p1⟩, ⟨0#64, p2⟩⟩ a auth ⊢
      authenticatorPBCapAt A a n auth := by
  unfold authenticatorPBPinnedAt authenticatorPBCapAt
  refine sepConj_mono ?_ ?_
  · refine Entails.trans (Entails.pure_right (bytesMergeCapOk_zero (n := n)) (Entails.refl _)) ?_
    exact Entails.sepExists_right 0#64 (Entails.sepExists_right p1 (Entails.refl _))
  · refine Entails.trans (Entails.pure_right (bytesMergeCapOk_zero (n := n)) (Entails.refl _)) ?_
    exact Entails.sepExists_right 0#64 (Entails.sepExists_right p2 (Entails.refl _))

theorem authenticatorPBAt_entails_cap_of_lt32 (A : RustAlloc) (a : BitVec 64)
    {n : Nat} (hn : n < 2 ^ 32) (auth : ProtoAuthenticator) :
    authenticatorPBAt A a auth ⊢ authenticatorPBCapAt A a n auth := by
  unfold authenticatorPBAt authenticatorPBCapAt rustBytesVecAt vecU8
  refine sepConj_mono ?_ ?_
  · refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans (Entails.pure_right (bytesMergeCapOk_of_len_lt32 (cap := cap) hn) (Entails.refl _)) ?_
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
  · refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans (Entails.pure_right (bytesMergeCapOk_of_len_lt32 (cap := cap) hn) (Entails.refl _)) ?_
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- Stack budget `skipField3Stack 97` (`96 + skipField3Stack 96`) for `Authenticator::merge`. -/
abbrev authMergeStack : Nat := skipField3Stack 97

/-- Ghost arguments for `Authenticator::merge` (`0x4df38`). -/
structure AuthMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : ProtoAuthenticator
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Specification of `prost::encoding::message::merge::<Authenticator, &mut &[u8]>` (`0x4df38`). -/
@[expose] def authMergeSpec (A : RustAlloc) : Spec AuthMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      authenticatorPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp authMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp authMergeStack ∗
      match (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ authenticatorPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ProtoAuthenticator, authenticatorPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Pure `mergeField` and `mergeBytes` Lemmas -/

theorem mergeBytes_length {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    rest.length < bs.length := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · rcases hdv : decodeVarint bs with _ | ⟨len, r0⟩
    · rw [hdv] at h; contradiction
    · rw [hdv] at h; dsimp only at h
      split at h
      · contradiction
      · injection h with hpair; injection hpair with _ hr; subst hr
        have hlt := decodeVarint_length hdv
        rw [List.length_drop]
        omega

theorem mergeBytes_suffix {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    IsDropSuffix bs rest := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · rcases hdv : decodeVarint bs with _ | ⟨len, r0⟩
    · rw [hdv] at h; contradiction
    · rw [hdv] at h; dsimp only at h
      split at h
      · contradiction
      · rename_i hge
        injection h with hpair; injection hpair with _ hr; subst hr
        have hsuf0 := decodeVarint_suffix hdv
        have hlt0 := decodeVarint_length hdv
        have hle_drop : (r0.drop len.toNat).length ≤ r0.length := by
          rw [List.length_drop]; omega
        have hsuf_drop : IsDropSuffix r0 (r0.drop len.toNat) := by
          unfold IsDropSuffix
          rw [List.length_drop, Nat.sub_sub_self (by omega)]
        exact suffix_trans (Nat.le_of_lt hlt0) hsuf0 hle_drop hsuf_drop

theorem protoAuthenticator_mergeField_tag1 (m : ProtoAuthenticator) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with rootKey := v }, rest')) := by
  unfold ProtoAuthenticator.mergeField
  simp only [beq_self_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl

theorem protoAuthenticator_mergeField_tag2 (m : ProtoAuthenticator) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with macKey := v }, rest')) := by
  unfold ProtoAuthenticator.mergeField
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl

theorem protoAuthenticator_mergeField_other (m : ProtoAuthenticator) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold ProtoAuthenticator.mergeField
  simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']
    rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']
    rfl

theorem setWidth8_ofNat64_wt (iwt : WireType) :
    (BitVec.ofNat 64 iwt.toNat).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

/-! ## Loop Invariant and Per-Branch Step Lemmas -/

abbrev authLoopPre (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ProtoAuthenticator) (bs cur : List (BitVec 8)) : SepProp :=
  authenticatorPBCapAt A msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp 97

abbrev authErrFrame (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ProtoAuthenticator) (bs : List (BitVec 8)) : SepProp :=
  authenticatorPBAt A msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗
    (ptr ↦ₛ bs) ∗
    A.pool ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

abbrev WppPost {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev WppPanic (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R

end CryptoVerification.SpqrV1.Auth
