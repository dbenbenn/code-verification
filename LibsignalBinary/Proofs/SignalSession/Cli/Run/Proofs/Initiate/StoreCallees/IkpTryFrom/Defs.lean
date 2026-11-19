/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Stack Layout, Invariants, and Cleanup Tails

Callee wrappers, `224`-byte stack frame layout (`ikpCalleeSavedAt`), protobuf decode invariants,
return-buffer decompositions (`identityKeyPairResultAt`), and shared epilogue/deallocation tails.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Relative-offset callee `subroutine_ok` wrappers -/

abbrev ikpSubStack : Nat := smallRootStack - 224

theorem spAligned_sub224 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

/-- Saved callee-saved registers and FP/LR in `[sp' + 144 .. sp' + 168)` and `[sp' + 176 .. sp' + 224)`. -/
@[expose] def ikpCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 144#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp' + 152#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp' + 160#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp' + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp' + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp' + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp' + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp' + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp' + 216#64) ↦₆₄ s0.readReg64 .x19)

theorem ikpRootStack_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      memRegion (sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64) 144 ∗
      memRegion (sp - 224#64 + 144#64) 80 := by
  have h1 := stackAt_sub_split sp 224 smallRootStack (by decide) (by decide)
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) ikpSubStack =
      stackAt (sp - 224#64) ikpSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 224#64 - BitVec.ofNat 64 ikpSubStack := by
      change sp - 65536#64 = sp - 224#64 - 65312#64
      bv_omega
    rw [ha]
  have h2b := stackAt_sub_split (sp - 224#64) (skipFieldStackX 100) ikpSubStack
    (by decide) (by decide)
  have h3 : stackAt sp 224 =
      memRegion (sp - 224#64) 144 ∗ memRegion (sp - 224#64 + 144#64) 80 := by
    unfold stackAt
    exact Prost.memRegion_split (sp - 224#64) 144 80 (by decide)
  rw [h1, h2, h2b, h3]
  ac_rfl

theorem ikpMem80_cells (sp' : BitVec 64) :
    memRegion (sp' + 144#64) 80 ⊢
      ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
      ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ wbuf : BitVec 64,
      ∃∗ w25 : BitVec 64, ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
        ((sp' + 144#64) ↦₆₄ w29) ∗ ((sp' + 152#64) ↦₆₄ w30) ∗
        ((sp' + 160#64) ↦₆₄ w25) ∗ ((sp' + 168#64) ↦₆₄ wbuf) ∗
        ((sp' + 176#64) ↦₆₄ w24) ∗ ((sp' + 184#64) ↦₆₄ w23) ∗
        ((sp' + 192#64) ↦₆₄ w22) ∗ ((sp' + 200#64) ↦₆₄ w21) ∗
        ((sp' + 208#64) ↦₆₄ w20) ∗ ((sp' + 216#64) ↦₆₄ w19) := by
  rw [show (80 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))) by decide,
    Prost.memRegion_split (sp' + 144#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpCalleeSaved_unsplit (sp : BitVec 64) (s0 : State) (wbuf : BitVec 64) :
    memRegion (sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64) 144 ∗
      (((sp - 224#64 + 168#64) ↦₆₄ wbuf) ∗ ikpCalleeSavedAt (sp - 224#64) s0) ⊢
      stackAt sp smallRootStack := by
  rw [ikpRootStack_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  set sp' := sp - 224#64
  unfold ikpCalleeSavedAt
  rw [show (80 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))) by decide,
    Prost.memRegion_split (sp' + 144#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 144#64) (s0.readReg64 .x29))
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 152#64) (s0.readReg64 .x30))
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 160#64) (s0.readReg64 .x25))
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 168#64) wbuf)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 176#64) (s0.readReg64 .x24))
              (sepConj_mono (pointsTo64_entails_memRegion (sp' + 184#64) (s0.readReg64 .x23))
                (sepConj_mono (pointsTo64_entails_memRegion (sp' + 192#64) (s0.readReg64 .x22))
                  (sepConj_mono (pointsTo64_entails_memRegion (sp' + 200#64) (s0.readReg64 .x21))
                    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 208#64) (s0.readReg64 .x20))
                      (pointsTo64_entails_memRegion (sp' + 216#64) (s0.readReg64 .x19)))))))))))
  apply entails_of_eq; ac_rfl

/-! ## State & memory invariants for `IdentityKeyPair::try_from` -/

@[expose] def ikpStructAt (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (m : IdentityKeyPairStructure) : SepProp :=
  vecU8At A a pk.cap pk.ptr m.publicKey ∗
  vecU8At A (a + 24#64) sk.cap sk.ptr m.privateKey

@[expose] def ikpStructOf (A : RustAlloc) (a : BitVec 64) (m : IdentityKeyPairStructure) : SepProp :=
  ∃∗ pk : VecPin, ∃∗ sk : VecPin, ikpStructAt A pk sk a m

@[expose] def ikpStructLoopOf (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (m : IdentityKeyPairStructure) : SepProp :=
  ∃∗ pk : VecPin, ∃∗ sk : VecPin,
    ⌜BytesMergeCapOk pk.cap n ∧ BytesMergeCapOk sk.cap n⌝ ∗ ikpStructAt A pk sk a m

theorem ikpStructAt_entails_loopOf (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (n : Nat) (m : IdentityKeyPairStructure)
    (hpk : BytesMergeCapOk pk.cap n) (hsk : BytesMergeCapOk sk.cap n) :
    ikpStructAt A pk sk a m ⊢ ikpStructLoopOf A a n m := by
  unfold ikpStructLoopOf
  refine Entails.trans ?_ (sepExists_intro _ pk)
  refine Entails.trans ?_ (sepExists_intro _ sk)
  rw [pure_true_emp ⟨hpk, hsk⟩, emp_sepConj]
  exact Entails.refl _

theorem ikpStructLoopOf_mono (A : RustAlloc) (a : BitVec 64) {m n : Nat}
    (msg : IdentityKeyPairStructure) (hle : m ≤ n) :
    ikpStructLoopOf A a n msg ⊢ ikpStructLoopOf A a m msg :=
  Entails.sepExists_elim fun pk => Entails.sepExists_elim fun sk =>
    Entails.pure_left fun ⟨hpk, hsk⟩ =>
      ikpStructAt_entails_loopOf A pk sk a m msg
        (bytesMergeCapOk_mono hpk hle) (bytesMergeCapOk_mono hsk hle)

theorem ikpStructLoopOf_entails_of (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (m : IdentityKeyPairStructure) :
    ikpStructLoopOf A a n m ⊢ ikpStructOf A a m :=
  Entails.sepExists_elim fun pk => Entails.sepExists_elim fun sk =>
    Entails.pure_left fun _ =>
      Entails.trans (sepExists_intro (fun sk' => ikpStructAt A pk sk' a m) sk)
        (sepExists_intro (fun pk' => ∃∗ sk', ikpStructAt A pk' sk' a m) pk)

/-! ## Pure field-length and suffix lemmas for `IdentityKeyPairStructure` -/

theorem ikp_mergeField_suffix {m m' : IdentityKeyPairStructure} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)}
    (h : IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold IdentityKeyPairStructure.mergeField at h
  rcases tag with _ | _ | _ | tag3 <;>
    simp only [skipUnknown, Option.map_eq_some_iff] at h
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩
    obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩
    obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs

@[expose] def IkpFieldsLe (N : Nat) (m : IdentityKeyPairStructure) : Prop :=
  m.publicKey.length ≤ N ∧ m.privateKey.length ≤ N

theorem ikp_mergeField_fields_le {N : Nat} {m m' : IdentityKeyPairStructure} {tag : Nat}
    {wt : WireType} {bs rest : List (BitVec 8)}
    (hm : IkpFieldsLe N m) (hbs : bs.length ≤ N)
    (h : IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest)) :
    IkpFieldsLe N m' := by
  rcases hm with ⟨h1, h2⟩
  unfold IdentityKeyPairStructure.mergeField at h
  split at h <;> simp only [skipUnknown, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨Nat.le_trans (mergeBytes_len_le hv) hbs, h2⟩
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨h1, Nat.le_trans (mergeBytes_len_le hv) hbs⟩
  · rcases h with ⟨r, _, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2⟩

theorem ikp_decodeLoop_fields_le :
    ∀ (fuel N : Nat) (m m' : IdentityKeyPairStructure) (bs : List (BitVec 8)),
      IkpFieldsLe N m → bs.length ≤ N →
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs = some m' →
      IkpFieldsLe N m'
  | 0, _, _, _, [], hm, _, h => by
    simp only [decodeFieldsLoop, Option.some.injEq] at h; subst h; exact hm
  | 0, _, _, _, _ :: _, _, _, h => by simp [decodeFieldsLoop] at h
  | fuel + 1, _, m, m', [], hm, _, h => by
    simp only [decodeFieldsLoop, Option.some.injEq] at h; subst h; exact hm
  | fuel + 1, N, m, m', b :: rest, hm, hbs, h => by
    simp only [decodeFieldsLoop] at h
    split at h
    · contradiction
    · rename_i tag wt rest1 hk
      split at h
      · contradiction
      · rename_i m1 rest2 hmr
        rcases decodeKey_suffix hk with ⟨k1, _, hk1_le, rfl, _, _⟩
        have hbs1 : ((b :: rest).drop k1).length ≤ N := by
          simp only [List.length_drop]; omega
        have hm1 := ikp_mergeField_fields_le hm hbs1 hmr
        rcases ikp_mergeField_suffix hmr with ⟨k2, hk2_le, rfl⟩
        have hbs2 : (((b :: rest).drop k1).drop k2).length ≤ N := by
          simp only [List.length_drop] at hbs1 ⊢; omega
        exact ikp_decodeLoop_fields_le fuel N m1 m' (((b :: rest).drop k1).drop k2) hm1 hbs2 h

theorem ikp_decode_field_lengths {bs : List (BitVec 8)} {m' : IdentityKeyPairStructure}
    (h : IdentityKeyPairStructure.decode bs = some m') :
    IkpFieldsLe bs.length m' :=
  ikp_decodeLoop_fields_le bs.length bs.length IdentityKeyPairStructure.empty m' bs
    ⟨Nat.zero_le _, Nat.zero_le _⟩ (Nat.le_refl _) h

/-! ## Return buffer splitting and `identityKeyPairResultAt` intro lemmas -/

theorem memRegion72_split_err (r : BitVec 64) :
    memRegion r 72 ⊢
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ b0 : BitVec 8,
        (r ↦₈ b0) ∗ memRegion (r + 1#64) 7 ∗
        ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
        memRegion (r + 24#64) 48 := by
  rw [show (72 : Nat) = 1 + (7 + (8 + (8 + 48))) by decide,
    Prost.memRegion_split r 1 71 (by decide),
    Prost.memRegion_split (r + 1#64) 7 64 (by decide),
    Prost.memRegion_split (r + 1#64 + 7#64) 8 56 (by decide),
    Prost.memRegion_split (r + 1#64 + 7#64 + 8#64) 8 48 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpResult_err_spe2 (A : RustAlloc) (r w2 : BitVec 64)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error .invalidProtobufEncoding) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 2) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have h40 : ((r + 16#64) ↦₆₄ w2) ∗ memRegion (r + 24#64) 32 ⊢
      memRegion (r + 16#64) 40 := by
    rw [Prost.memRegion_split (r + 16#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (r + 16#64) w2)
  rw [ha16, h48]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right h40))))
  apply entails_of_eq; ac_rfl

theorem ikpResult_err_spe7 (A : RustAlloc) (r w2 : BitVec 64)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error .noKeyTypeIdentifier) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 7) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have h40 : ((r + 16#64) ↦₆₄ w2) ∗ memRegion (r + 24#64) 32 ⊢
      memRegion (r + 16#64) 40 := by
    rw [Prost.memRegion_split (r + 16#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (r + 16#64) w2)
  rw [ha16, h48]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right h40))))
  apply entails_of_eq; ac_rfl

theorem ikpResult_err_spe8 (A : RustAlloc) (r : BitVec 64) (t : BitVec 8)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error (.badKeyType t)) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₆₄ t.zeroExtend 64) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have ha17 : r + 8#64 + 9#64 = r + 17#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have hw8 : ((r + 16#64) ↦₆₄ t.zeroExtend 64) ⊢
      ((r + 16#64) ↦₈ t) ∗ memRegion (r + 17#64) 7 := by
    have hz : ∀ u : BitVec 8, u.zeroExtend 64 =
        0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ u := by decide
    rw [hz t, ← pointsToBytes8_eq_pointsTo64, pointsToBytes_cons]
    have hm7 : ((r + 16#64 + 1#64) ↦ₛ [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]) ⊢
        memRegion (r + 17#64) 7 := by
      simpa [BitVec.add_assoc] using
        pointsToBytes_entails_memRegion (r + 16#64 + 1#64) [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
    exact sepConj_mono_right hm7
  have h39 : memRegion (r + 17#64) 7 ∗ memRegion (r + 24#64) 32 =
      memRegion (r + 17#64) 39 := by
    have hs := (Prost.memRegion_split (r + 17#64) 7 32 (by decide)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  rw [ha16, ha17, h48]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw8)))) ?_
  have hrew :
      (r ↦₈ 1#8) ∗ (memRegion (r + 1#64) 7 ∗
        (((r + 8#64) ↦₆₄ speWord 8) ∗
          ((((r + 16#64) ↦₈ t) ∗ memRegion (r + 17#64) 7) ∗
            (memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16)))) =
      (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
        (((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₈ t) ∗
          (memRegion (r + 17#64) 7 ∗ memRegion (r + 24#64) 32)) ∗
        memRegion (r + 0x38#64) 16 := by ac_rfl
  rw [hrew, h39]
  exact Entails.refl _

theorem ikpResult_err_spe9 (A : RustAlloc) (r : BitVec 64) (n : Nat)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error (.badKeyLength n)) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 9) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have ha24 : r + 8#64 + 16#64 = r + 24#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  rw [ha16, ha24, h48]
  apply entails_of_eq; ac_rfl

/-! ## Shared epilogue (`+812 .. +836`) and Vec dealloc tails (`+772 .. +808`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
