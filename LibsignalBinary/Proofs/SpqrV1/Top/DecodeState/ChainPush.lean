/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpoch
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainPB` `links.push` & Tag 3 (`0x536ec..0x53770`)

**Checked by Lean.** Verifies strict length decrease of `.lengthDelimited` `Proto.mergeMessage`,
the 112-byte Q-register copy (`0x5371c`), `Vec<ChainEpochPB>::push` with `grow_one` (`0x5370c`),
and `ChainPB` tag 3 (`links`, `0x536ec`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bv_ofNat_mul_112 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 112#64 = ptr + BitVec.ofNat 64 (n * 112) := by
  rw [← BitVec.ofNat_mul]

theorem bv_ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

attribute [local simp, local arm64_norm] bv_ofNat_mul_112 bv_ofNat_add_one

/-! ## Pure & Spatial Helpers for `Vec<ChainEpochPB>::push` -/

theorem proto_mergeMessage_length_lt {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {m m' : M} {bs rest : List (BitVec 8)} {depth' : Nat}
    (h : (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = some (m', rest)) :
    rest.length < bs.length := by
  have hchk : Proto.checkWireType .lengthDelimited .lengthDelimited = .ok () := rfl
  simp only [Proto.mergeMessage, hchk, Bind.bind, Except.bind, takeExact_eq_take_drop] at h
  rcases hdv : Proto.decodeVarint bs with e | ⟨len64, restMid⟩
  · rw [hdv] at h; cases h
  · have hdv_opt : decodeVarint bs = some (len64, restMid) := by
      rw [← proto_decodeVarint_toOption, hdv]; rfl
    have hlt_mid : restMid.length < bs.length := decodeVarint_length hdv_opt
    rw [hdv] at h; dsimp only at h
    by_cases hle : len64.toNat ≤ restMid.length
    · rw [ite_eq_left_iff.mpr fun hnot => absurd hle hnot] at h; dsimp only at h
      rcases hloop : Proto.mergeFieldsLoop mergeField (restMid.take len64.toNat).length m
          (restMid.take len64.toNat) depth' with e | m''
      · rw [hloop] at h; cases h
      · rw [hloop] at h
        simp only [Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        rw [List.length_drop]
        omega
    · rw [ite_eq_right_iff.mpr fun hyes => absurd hyes hle] at h; cases h

theorem arrayAt_append_singleton {α : Type} (elemAt : α → BitVec 64 → SepProp) (stride : Nat)
    (ptr : BitVec 64) (xs : List α) (x : α) :
    arrayAt elemAt stride ptr xs ∗ elemAt x (ptr + BitVec.ofNat 64 (xs.length * stride)) =
      arrayAt elemAt stride ptr (xs ++ [x]) := by
  induction xs generalizing ptr with
  | nil =>
    simp only [arrayAt, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.nil_append, emp_sepConj, sepConj_emp]
  | cons y ys ih =>
    simp only [arrayAt, List.cons_append, List.length_cons]
    have hadd :
        ptr + BitVec.ofNat 64 ((ys.length + 1) * stride) =
          (ptr + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (ys.length * stride) := by
      have hm : (ys.length + 1) * stride = stride + ys.length * stride := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hadd, sepConj_assoc, ih (ptr + BitVec.ofNat 64 stride)]

theorem max_double_four_bound {cap : Nat} (hcap : cap ≤ 2 ^ 54) :
    max (2 * cap) 4 * 112 + 8 ≤ 2 ^ 63 ∧ max (2 * cap) 4 * 112 < 2 ^ 63 ∧
      cap < max (2 * cap) 4 ∧ max (2 * cap) 4 < 2 ^ 64 := by
  omega

theorem vecBuf_chainEpochPB_expose_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.refl _

theorem vecBuf_chainEpochPB_of_lt (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hlt : xs.length < cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((cap.toNat - xs.length) * 112) := by
  unfold vecBuf
  apply Entails.pure_left; intro _
  have hcap0 : cap ≠ 0 := by intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  exact Entails.refl _

theorem vecBuf_chainEpochPB_to_growOne_pre (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hfull : xs.length = cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = cap.toNat * 112 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        (relocArrayAtChainEpochPB A xs).1 bs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨_, _, hptr⟩
  by_cases hcap0 : cap = 0
  · subst hcap0
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero hfull
    subst hxs
    simp only [↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mul, relocArrayAtChainEpochPB]
    refine Entails.sepExists_right [] ?_
    apply Entails.pure_right ⟨rfl, hptr⟩
    simp only [sepConj_emp]
    exact Entails.refl _
  · have hcap0' : cap ≠ 0#64 := hcap0
    simp only [hcap0, hcap0', ↓reduceIte, hfull, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
    have hto := (relocArrayAtChainEpochPB A xs).2.to_bytes ptr
    refine Entails.trans (sepConj_mono_right hto) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    have hpull :
        A.live ptr (cap.toNat * 112) 8 ∗
          (⌜bs.length = xs.length * 112⌝ ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) =
        ⌜bs.length = xs.length * 112⌝ ∗
          A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hbs
    have hbs' : bs.length = cap.toNat * 112 := by rw [hbs, hfull]
    apply Entails.pure_right ⟨hbs', hptr⟩
    rw [hbs']
    exact Entails.of_eq (by ac_rfl)

theorem growOne_post_to_arrayAt_chainEpochPB (A : RustAlloc) (cap p' : BitVec 64)
    (xs : List ChainEpochPB) (bs : List (BitVec 8))
    (hfull : xs.length = cap.toNat) (hbs : bs.length = cap.toNat * 112)
    (hnew_toNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4) :
    A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
      (relocArrayAtChainEpochPB A xs).1 bs ⊢
    A.live p' ((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 p' xs ∗
      memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
        (((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat - xs.length) * 112) := by
  rw [hnew_toNat]
  have hlen_xs : bs.length = xs.length * 112 := by rw [hbs, hfull]
  have hof := (relocArrayAtChainEpochPB A xs).2.of_bytes p' bs hlen_xs
  have hsub : max (2 * cap.toNat) 4 - cap.toNat = max (2 * cap.toNat) 4 - xs.length := by
    rw [hfull]
  rw [hlen_xs, hsub]
  have hgroup :
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) ∗
        (relocArrayAtChainEpochPB A xs).1 bs =
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
        ((p' ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono_left hof)

/-! ## 112-Byte Q-Register Copy & `arrayAt` Snoc Helpers (`0x5371c..0x53770`) -/

theorem quads14At_sp_688_restore (sp : BitVec 64) (q : Quads14) :
    quads14At (sp - 688#64) q ∗ memRegion (sp - 576#64) 240 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 := by
  unfold quads14At Quads14.head
  have h1 := quads7_entails_head_and_memRegion_48 (sp - 688#64) q.1
  have h2 := quads7At_entails_memRegion_56 (sp - 632#64) q.2
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 688#64 + 56#64 = sp - 632#64 := by bv_omega
  rw [ha1] at h1; rw [ha2]
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) (Entails.refl _)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
      (b' := sp - 632#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240)
      (b' := sp - 576#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_rem_split_112 (ptr : BitVec 64) (len cap : Nat)
    (hlt : len < cap) (hcap63 : cap * 112 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (len * 112)) ((cap - len) * 112) ⊢
      (∃∗ q_dst : Quads14, quads14At (ptr + BitVec.ofNat 64 (len * 112)) q_dst) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len + 1) * 112)) ((cap - (len + 1)) * 112) := by
  have hsplit : (cap - len) * 112 = 112 + (cap - (len + 1)) * 112 := by
    have hsub : cap - len = 1 + (cap - (len + 1)) := by omega
    rw [hsub, Nat.add_mul, Nat.one_mul]
  have haddr : ptr + BitVec.ofNat 64 ((len + 1) * 112) =
      (ptr + BitVec.ofNat 64 (len * 112)) + 112#64 := by
    have hm : (len + 1) * 112 = len * 112 + 112 := by rw [Nat.add_mul, Nat.one_mul]
    rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 (len * 112))
      (n := 112) (k := (cap - (len + 1)) * 112)
      (b' := ptr + BitVec.ofNat 64 ((len + 1) * 112)) hsplit haddr (by omega),
    memRegion_112_eq_quads14At (ptr + BitVec.ofNat 64 (len * 112))]
  exact Entails.refl _

theorem vecOf_chainEpochPB_snoc_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (ep' : ChainEpochPB) (q : Quads14)
    (hlt : xs.length < cap.toNat) (hcap63 : cap.toNat * 112 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
      chainEpochPBHeap A q ep' ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
        ((cap.toNat - (xs.length + 1)) * 112) ⊢
    chainLinksVecAt A a (xs ++ [ep']) := by
  have hcap0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlen_app : (xs ++ [ep']).length = xs.length + 1 := by simp
  have hep_at := quads14_entails_chainEpochPBAt A (ptr + BitVec.ofNat 64 (xs.length * 112)) q ep'
  have harr := arrayAt_append_singleton (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ep'
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simp only [hlen_app, hcap0, ↓reduceIte]
  have hgroup :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
        quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
        chainEpochPBHeap A q ep' ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
          (quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
            chainEpochPBHeap A q ep')) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right hep_at)))) ?_
  rw [harr]
  have hpure :
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) =
      ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
          A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) := by ac_rfl
  rw [hpure]
  apply Entails.pure_right ⟨by omega, hcap63, hptr⟩
  exact Entails.of_eq (by ac_rfl)

theorem fold_protoPqRatchetStateCapOkAt_snoc (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (ep' : ChainEpochPB) (inner : Option PqRatchetState.Inner)
    (hlinks_next : (ch.links ++ [ep']).length + remLen ≤ 2 ^ 54) :
    optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
      vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
      ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (sp - 928#64) ch.params ∗
      ((sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner ⊢
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen
      ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq H_inner A sp remLen optVn
    { ch with links := ch.links ++ [ep'] } inner]
  dsimp only
  have hpure :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by ac_rfl
  rw [hpure]
  apply Entails.pure_right hlinks_next
  exact Entails.of_eq (by ac_rfl)

/-! ## `decodeState_chain_push_copy_5371c` (`0x5371c..0x53770`, `+640..+724`) -/

theorem bv_len_beq_cap_false {len : Nat} {cap : BitVec 64}
    (hlt : len < cap.toNat) :
    (BitVec.ofNat 64 len == cap) = false ∧ (BitVec.ofNat 64 len != cap) = true := by
  have hlt64 : len < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  have hne : BitVec.ofNat 64 len ≠ cap := by
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at hto
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

theorem bv_len_beq_cap_true {len : Nat} {cap : BitVec 64}
    (heq : len = cap.toNat) :
    (BitVec.ofNat 64 len == cap) = true ∧ (BitVec.ofNat 64 len != cap) = false := by
  have hbv : BitVec.ofNat 64 len = cap := by
    rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨beq_iff_eq.mpr hbv, bne_eq_false_iff_eq.mpr hbv⟩

theorem protoPqRatchetStateCapOkAt_expose_ch_links (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ ⊢
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq]
  have h1 :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          (chainLinksVecAt A (sp - 992#64) ch.links ∗
            vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
            ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
            ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
            optChainParamsPBAt (sp - 928#64) ch.params ∗
            ((sp - 916#64) ↦₃₂ ch.direction)) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.of_eq (by ac_rfl)

theorem wt_ne_two_of_ne_lengthDelimited {iwt : WireType} (hwt : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> first | exact (hwt rfl).elim | decide

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

end CryptoVerification.SpqrV1.Top.DecodeState
