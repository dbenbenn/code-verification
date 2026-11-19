/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Callees -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Shared `.rodata`, Cell Wrappers, and `RelocatableBlock` Helpers for Store Polls

Symbolic `.rodata` string witnesses (`ls_xref%`), 72-byte and 14-byte cell decompositions,
cell-oriented `Dir::get` / `dealloc` / `IdentityKeyPair::try_from` wrappers, and `RelocatableBlock`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

open Arm64 ProofLib ProofLib.ProgramReflection open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

/-! ## Symbolic `.rodata` Addresses and Loading Witnesses -/

theorem utf8_idKp_length : (utf8 "identity-key-pair").length = 17 := by decide +kernel
theorem utf8_regId_length : (utf8 "registration-id").length = 15 := by decide +kernel

theorem cap_reconstruct_u32_pair (cap : BitVec 64) :
    ((cap.truncate 32).zeroExtend 64 |||
      (((cap >>> 32).truncate 32).zeroExtend 64 <<< 32)) = cap := by
  bv_bits

theorem cap_split_lo_hi_pointsTo64 (a : BitVec 64) (cap : BitVec 64) :
    (a ↦₆₄ cap) =
      ((a ↦₃₂ cap.truncate 32) ∗ ((a + 4#64) ↦₃₂ (cap >>> 32).truncate 32)) := by
  rw [pointsTo64_split32']
  have hhi : cap.extractLsb' 32 32 = (cap >>> 32).truncate 32 := by bv_bits
  rw [hhi]

theorem u64_pack_u32_pair (lo hi : BitVec 32) :
    ((lo.zeroExtend 64) ||| ((hi.zeroExtend 64) <<< 32)) = hi ++ lo := by
  bv_bits

abbrev DirGetRoCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def dirGetRoCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec DirGetRoCellsGhost where
  pre := fun (ret, self, dir, nameA, name, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name)⌝ ∗
      dirAt A self dir ∗ (nameA ↦ᵣ name) ∗ memRegion ret 48 ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nameA, name, fsp) s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace⌝ ∗
        getResultAt A ret r) ∗
      dirAt A self dir ∗ (nameA ↦ᵣ name) ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem exists_pointsTo128_of_length_16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ q : BitVec 128, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₁₂₈ q) := by
  obtain ⟨w0, w1, _, hp⟩ := exists_unpack64_of_length_16 h
  refine ⟨w1 ++ w0, fun a => ?_⟩
  rw [hp]
  unfold Arm64.pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_bits
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_bits
  rw [h0, h1]

theorem pointsToBytes72_split_qwords {bs : List (BitVec 8)}
    (hlen : bs.length = 72) :
    ∃ (q3 q0 q1 q2 : BitVec 128) (w8 : BitVec 64),
      (∀ p : BitVec 64,
        (p ↦ₛ bs) =
          (p ↦₁₂₈ q3) ∗ ((p + 16#64) ↦₁₂₈ q0) ∗ ((p + 32#64) ↦₁₂₈ q1) ∗
          ((p + 48#64) ↦₁₂₈ q2) ∗ ((p + 64#64) ↦₆₄ w8)) := by
  have h1 : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm
  have h2 : bs.drop 16 = (bs.drop 16).take 16 ++ bs.drop 32 := by
    simpa [List.drop_drop] using (List.take_append_drop 16 (bs.drop 16)).symm
  have h3 : bs.drop 32 = (bs.drop 32).take 16 ++ bs.drop 48 := by
    simpa [List.drop_drop] using (List.take_append_drop 16 (bs.drop 32)).symm
  have h4 : bs.drop 48 = (bs.drop 48).take 16 ++ bs.drop 64 := by
    simpa [List.drop_drop] using (List.take_append_drop 16 (bs.drop 48)).symm
  have htake : bs =
      (bs.take 16) ++ (((bs.drop 16).take 16) ++ (((bs.drop 32).take 16) ++
        (((bs.drop 48).take 16) ++ (bs.drop 64)))) :=
    Eq.trans h1 (congrArg (bs.take 16 ++ ·)
      (Eq.trans h2 (congrArg ((bs.drop 16).take 16 ++ ·)
        (Eq.trans h3 (congrArg ((bs.drop 32).take 16 ++ ·) h4)))))
  have l0 : (bs.take 16).length = 16 := by simp [hlen]
  have l1 : ((bs.drop 16).take 16).length = 16 := by simp [hlen]
  have l2 : ((bs.drop 32).take 16).length = 16 := by simp [hlen]
  have l3 : ((bs.drop 48).take 16).length = 16 := by simp [hlen]
  have l4 : (bs.drop 64).length = 8 := by simp [hlen]
  obtain ⟨q3, hq3⟩ := exists_pointsTo128_of_length_16 l0
  obtain ⟨q0, hq0⟩ := exists_pointsTo128_of_length_16 l1
  obtain ⟨q1, hq1⟩ := exists_pointsTo128_of_length_16 l2
  obtain ⟨q2, hq2⟩ := exists_pointsTo128_of_length_16 l3
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 l4
  refine ⟨q3, q0, q1, q2, w8, fun p => ?_⟩
  conv_lhs => rw [htake]
  rw [pointsToBytes_append, l0,
      pointsToBytes_append, l1,
      pointsToBytes_append, l2,
      pointsToBytes_append, l3,
      hq3, hq0, hq1, hq2, hw8, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_72_eq_qwords (p : BitVec 64) :
    memRegion p 72 =
      ∃∗ w8 : BitVec 64, ∃∗ q2 : BitVec 128, ∃∗ q1 : BitVec 128,
      ∃∗ q0 : BitVec 128, ∃∗ q3 : BitVec 128,
        (p ↦₁₂₈ q3) ∗ ((p + 16#64) ↦₁₂₈ q0) ∗ ((p + 32#64) ↦₁₂₈ q1) ∗
        ((p + 48#64) ↦₁₂₈ q2) ∗ ((p + 64#64) ↦₆₄ w8) := by
  rw [memRegion_split p 16 56 (by decide),
      memRegion_split (p + 16#64) 16 40 (by decide),
      memRegion_split (p + 16#64 + 16#64) 16 24 (by decide),
      memRegion_split (p + 16#64 + 16#64 + 16#64) 16 8 (by decide),
      memRegion_sixteen, memRegion_sixteen, memRegion_sixteen, memRegion_sixteen,
      ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-! ## 14-Byte Overlapping Store Decomposition -/

theorem memRegion_14_split_8_6 (buf : BitVec 64) :
    memRegion buf 14 =
      ∃∗ b0 : BitVec 64, (buf ↦₆₄ b0) ∗ memRegion (buf + 8#64) 6 := by
  rw [memRegion_split buf 8 6 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left]

theorem write_14_overlap_mid (buf w0 : BitVec 64) :
    (buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 6 ⊢
      (buf ↦ₛ (unpack64 w0).take 6) ∗ (∃∗ bt : BitVec 64, (buf + 6#64) ↦₆₄ bt) := by
  have h0 : (unpack64 w0).length = 8 := unpack64_length w0
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [h0]
  have h2 : ((unpack64 w0).drop 6).length = 2 := by simp [h0]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 6 (unpack64 w0),
      pointsToBytes_append, h6]
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [← ProofLib.memRegion_eight (buf + 6#64),
      memRegion_split (buf + 6#64) 2 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono
    (by have := pointsToBytes_entails_memRegion (buf + 6#64) ((unpack64 w0).drop 6)
        rwa [h2] at this)
    (Entails.refl _)

theorem write_14_overlap_done (buf w0 wTail : BitVec 64) :
    (buf ↦ₛ (unpack64 w0).take 6) ∗ ((buf + 6#64) ↦₆₄ wTail) ⊢
      (buf ↦ₛ ((unpack64 w0).take 6 ++ unpack64 wTail)) := by
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [unpack64_length]
  rw [pointsToBytes_append, h6, ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem write_14_overlap_length (w0 wTail : BitVec 64) :
    ((unpack64 w0).take 6 ++ unpack64 wTail).length = 14 := by
  have h0 := unpack64_length w0
  have h1 := unpack64_length wTail
  simp [h0, h1]

/-! ## Deallocation and `IdentityKeyPair::try_from` Cell Wrappers -/

abbrev IkpTryFromCellsGhost := BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64

/-- A separation-logic predicate `F : BitVec 64 → SepProp` is a position-independent `n`-byte block
if `F p` decomposes into `n` contiguous bytes at `p` plus a `p`-independent resource `B bs`. -/
@[expose] def RelocatableBlock (n : Nat) (F : BitVec 64 → SepProp) : Prop :=
  ∃ B : List (BitVec 8) → SepProp,
    ∀ p : BitVec 64, F p = ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (p ↦ₛ bs) ∗ B bs

theorem reloc_pointsToBytes (bs₀ : List (BitVec 8)) :
    RelocatableBlock bs₀.length (fun p => p ↦ₛ bs₀) := by
  refine ⟨fun bs => ⌜bs = bs₀⌝, fun p => ?_⟩
  dsimp only
  apply Entails.antisymm
  · refine Entails.sepExists_right bs₀ ?_
    refine Entails.pure_right rfl ?_
    rw [sepConj_comm]
    exact Entails.pure_right rfl (Entails.refl _)
  · refine Entails.sepExists_elim fun bs => ?_
    apply Entails.pure_left; intro _
    rw [sepConj_comm]
    apply Entails.pure_left; rintro rfl
    exact Entails.refl _

theorem reloc_pointsTo8 (b : BitVec 8) :
    RelocatableBlock 1 (fun p => p ↦₈ b) := by
  have h := reloc_pointsToBytes [b]
  simpa only [List.length_singleton, pointsToBytes_singleton] using h

theorem reloc_pointsTo32 (w : BitVec 32) :
    RelocatableBlock 4 (fun p => p ↦₃₂ w) := by
  have h := reloc_pointsToBytes (unpack32 w)
  simpa only [unpack32_length, ← pointsTo32_eq_pointsToBytes] using h

theorem reloc_pointsTo64 (w : BitVec 64) :
    RelocatableBlock 8 (fun p => p ↦₆₄ w) := by
  have h := reloc_pointsToBytes (unpack64 w)
  simpa only [unpack64_length, ← pointsTo64_eq_pointsToBytes] using h

theorem reloc_memRegion (n : Nat) (hn : n ≤ 2 ^ 64) :
    RelocatableBlock n (fun p => memRegion p n) := by
  refine ⟨fun _ => emp, fun p => ?_⟩
  dsimp only
  rw [memRegion_eq_exists_bytes p n hn]
  exact sepExists_congr fun _ => by simp only [sepConj_emp]

theorem reloc_false (n : Nat) :
    RelocatableBlock n (fun _ => (⌜False⌝ : SepProp)) := by
  refine ⟨fun _ => ⌜False⌝, fun p => ?_⟩
  dsimp only
  apply Entails.antisymm
  · rw [← sepConj_emp (⌜False⌝ : SepProp)]
    apply Entails.pure_left; exact False.elim
  · refine Entails.sepExists_elim fun bs => ?_
    rw [show (⌜bs.length = n⌝ ∗ (p ↦ₛ bs) ∗ (⌜False⌝ : SepProp)) =
          ⌜False⌝ ∗ (⌜bs.length = n⌝ ∗ (p ↦ₛ bs)) by ac_rfl]
    apply Entails.pure_left; exact False.elim

theorem reloc_frame_right {n : Nat} {F : BitVec 64 → SepProp} (H : SepProp)
    (hF : RelocatableBlock n F) :
    RelocatableBlock n (fun p => F p ∗ H) := by
  rcases hF with ⟨B, hB⟩
  refine ⟨fun bs => B bs ∗ H, fun p => ?_⟩
  dsimp only
  rw [hB p, sepExists_sepConj_left]
  exact sepExists_congr fun _ => by simp only [sepConj_assoc]

theorem reloc_sepConj {n₁ n₂ : Nat} {F₁ F₂ : BitVec 64 → SepProp}
    (h₁ : RelocatableBlock n₁ F₁) (h₂ : RelocatableBlock n₂ F₂) :
    RelocatableBlock (n₁ + n₂) (fun p => F₁ p ∗ F₂ (p + BitVec.ofNat 64 n₁)) := by
  rcases h₁ with ⟨B₁, hB₁⟩
  rcases h₂ with ⟨B₂, hB₂⟩
  refine ⟨fun bs => B₁ (bs.take n₁) ∗ B₂ (bs.drop n₁), fun p => ?_⟩
  dsimp only
  rw [hB₁ p, hB₂ (p + BitVec.ofNat 64 n₁)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.antisymm
  · refine Entails.sepExists_elim fun bs₂ => Entails.sepExists_elim fun bs₁ => ?_
    rw [show (⌜bs₁.length = n₁⌝ ∗ (p ↦ₛ bs₁) ∗ B₁ bs₁) ∗
          ⌜bs₂.length = n₂⌝ ∗ ((p + BitVec.ofNat 64 n₁) ↦ₛ bs₂) ∗ B₂ bs₂ =
        ⌜bs₁.length = n₁⌝ ∗ ⌜bs₂.length = n₂⌝ ∗
          ((p ↦ₛ bs₁) ∗ ((p + BitVec.ofNat 64 n₁) ↦ₛ bs₂)) ∗ B₁ bs₁ ∗ B₂ bs₂ by ac_rfl]
    apply Entails.pure_left; intro hl₁
    apply Entails.pure_left; intro hl₂
    refine Entails.sepExists_right (bs₁ ++ bs₂) ?_
    refine Entails.pure_right (by simp [hl₁, hl₂]) ?_
    have ht : (bs₁ ++ bs₂).take n₁ = bs₁ := by simp [hl₁]
    have hd : (bs₁ ++ bs₂).drop n₁ = bs₂ := by simp [hl₁]
    rw [ht, hd, pointsToBytes_append, hl₁]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun bs => ?_
    apply Entails.pure_left; intro hl
    refine Entails.sepExists_right (bs.drop n₁) (Entails.sepExists_right (bs.take n₁) ?_)
    have hl₁ : (bs.take n₁).length = n₁ := by simp [hl]
    have hl₂ : (bs.drop n₁).length = n₂ := by simp [hl]
    have hbs : bs = bs.take n₁ ++ bs.drop n₁ := (List.take_append_drop n₁ bs).symm
    conv_lhs => arg 1; rw [hbs, pointsToBytes_append, hl₁]
    rw [show (⌜(bs.take n₁).length = n₁⌝ ∗ (p ↦ₛ bs.take n₁) ∗ B₁ (bs.take n₁)) ∗
          ⌜(bs.drop n₁).length = n₂⌝ ∗ ((p + BitVec.ofNat 64 n₁) ↦ₛ bs.drop n₁) ∗ B₂ (bs.drop n₁) =
        ⌜(bs.take n₁).length = n₁⌝ ∗ ⌜(bs.drop n₁).length = n₂⌝ ∗
          ((p ↦ₛ bs.take n₁) ∗ ((p + BitVec.ofNat 64 n₁) ↦ₛ bs.drop n₁)) ∗
          B₁ (bs.take n₁) ∗ B₂ (bs.drop n₁) by ac_rfl]
    refine Entails.pure_right hl₁ (Entails.pure_right hl₂ ?_)
    exact Entails.of_eq (by ac_rfl)

theorem reloc_sepConj_off {n₁ n₂ : Nat} {off : BitVec 64} {F₁ F₂ : BitVec 64 → SepProp}
    (hoff : BitVec.ofNat 64 n₁ = off)
    (h₁ : RelocatableBlock n₁ F₁) (h₂ : RelocatableBlock n₂ F₂) :
    RelocatableBlock (n₁ + n₂) (fun p => F₁ p ∗ F₂ (p + off)) := by
  subst hoff
  exact reloc_sepConj h₁ h₂

theorem reloc_sepExists {α : Type} {n : Nat} {F : α → BitVec 64 → SepProp}
    (hF : ∀ x : α, RelocatableBlock n (F x)) :
    RelocatableBlock n (fun p => ∃∗ x : α, F x p) := by
  refine ⟨fun bs => ∃∗ x : α, Classical.choose (hF x) bs, fun p => ?_⟩
  dsimp only
  apply Entails.antisymm
  · refine Entails.sepExists_elim fun x => ?_
    rw [Classical.choose_spec (hF x) p]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    exact sepConj_mono_right (sepConj_mono_right
      (Entails.sepExists_intro (P := fun y => Classical.choose (hF y) bs) x))
  · refine Entails.sepExists_elim fun bs => ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun x => Entails.sepExists_right x ?_
    rw [Classical.choose_spec (hF x) p]
    exact Entails.sepExists_right bs (Entails.refl _)

theorem reloc_congr {n : Nat} {F G : BitVec 64 → SepProp}
    (hFG : ∀ p, F p = G p) (hF : RelocatableBlock n F) :
    RelocatableBlock n G := by
  rcases hF with ⟨B, hB⟩
  exact ⟨B, fun p => (hFG p).symm.trans (hB p)⟩

theorem reloc_vecU8 (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocatableBlock 24 (fun p => vecU8 A p bs) := by
  refine reloc_sepExists fun cap => reloc_sepExists fun ptr => ?_
  refine reloc_congr (fun p => ?_)
    (reloc_frame_right (SpqrV1.Alloc.vecU8Buf A cap ptr bs)
      (reloc_sepConj_off (n₁ := 8) (n₂ := 16) rfl (reloc_pointsTo64 cap)
        (reloc_sepConj_off (n₁ := 8) (n₂ := 8) rfl (reloc_pointsTo64 ptr)
          (reloc_pointsTo64 (BitVec.ofNat 64 bs.length)))))
  simp only [SpqrV1.Alloc.vecU8At_eq_header_sep_buf, vecHeader,
    SpqrV1.Alloc.vecU8Buf, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem reloc_strRefAt (fnName : List (BitVec 8)) :
    RelocatableBlock 16 (fun p => strRefAt p fnName) := by
  refine reloc_sepExists fun ptr => ?_
  refine reloc_congr (fun p => by simp only [sepConj_assoc])
    (reloc_frame_right (ptr ↦ᵣ fnName)
      (reloc_sepConj_off (n₁ := 8) (n₂ := 8) rfl (reloc_pointsTo64 ptr)
        (reloc_pointsTo64 (BitVec.ofNat 64 fnName.length))))

theorem reloc_invalidMessageStrAt (A : RustAlloc) (r : InvalidMessageReason) :
    RelocatableBlock 24 (fun p => invalidMessageStrAt A p r) := by
  cases r with
  | tooFarInFuture => exact reloc_vecU8 A _
  | macFailed => exact reloc_vecU8 A _
  | pqRatchet => exact reloc_sepExists fun bs => reloc_vecU8 A bs
  | badCiphertext => exact reloc_sepExists fun bs => reloc_vecU8 A bs
  | decryptionFailed => exact reloc_false 24

theorem reloc_speAt (A : RustAlloc) (fnName : List (BitVec 8)) (e : SignalProtocolError) :
    RelocatableBlock 48 (fun p => speAt A fnName p e) := by
  cases e with
  | invalidState =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 1))
        (reloc_sepConj_off (n₁ := 24) (n₂ := 16) rfl
          (reloc_sepExists fun bs => reloc_vecU8 A bs) (reloc_strRefAt fnName)))
  | ciphertextMessageTooShort n =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 3))
        (reloc_sepConj_off (n₁ := 8) (n₂ := 32) rfl (reloc_pointsTo64 (BitVec.ofNat 64 n))
          (reloc_memRegion 32 (by decide))))
  | legacyCiphertextVersion v =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 4))
        (reloc_sepConj_off (n₁ := 1) (n₂ := 39) rfl (reloc_pointsTo8 v)
          (reloc_memRegion 39 (by decide))))
  | unrecognizedCiphertextVersion v =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 5))
        (reloc_sepConj_off (n₁ := 1) (n₂ := 39) rfl (reloc_pointsTo8 v)
          (reloc_memRegion 39 (by decide))))
  | invalidProtobufEncoding =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 2))
      (reloc_memRegion 40 (by decide))
  | noKeyTypeIdentifier =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 7))
      (reloc_memRegion 40 (by decide))
  | badKeyType t =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 8))
        (reloc_sepConj_off (n₁ := 1) (n₂ := 39) rfl (reloc_pointsTo8 t)
          (reloc_memRegion 39 (by decide))))
  | badKeyLength n =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 9))
        (reloc_sepConj_off (n₁ := 8) (n₂ := 32) rfl (reloc_pointsTo64 (BitVec.ofNat 64 n))
          (reloc_memRegion 32 (by decide))))
  | invalidKeyAgreement =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 10))
      (reloc_memRegion 40 (by decide))
  | invalidSessionStructure r =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 20))
        (reloc_sepConj_off (n₁ := 16) (n₂ := 24) rfl (reloc_strRefAt (invalidSessionStructureStr r))
          (reloc_memRegion 24 (by decide))))
  | duplicatedMessage i c =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 23))
        (reloc_sepConj_off (n₁ := 4) (n₂ := 36) rfl (reloc_pointsTo32 i)
          (reloc_sepConj_off (n₁ := 4) (n₂ := 32) rfl (reloc_pointsTo32 c)
            (reloc_memRegion 32 (by decide)))))
  | invalidMessage t r =>
    refine reloc_congr (fun p => by
        dsimp only [speAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 24))
        (reloc_sepConj_off (n₁ := 24) (n₂ := 16) rfl (reloc_invalidMessageStrAt A r)
          (reloc_sepConj_off (n₁ := 1) (n₂ := 15) rfl (reloc_pointsTo8 (msgTypeByte t))
            (reloc_memRegion 15 (by decide)))))
  | panic => exact reloc_false 48

theorem reloc_speOwnedAt (A : RustAlloc) (k : RunDrop.SpeOwned) :
    RelocatableBlock 48 (fun p => RunDrop.speOwnedAt A p k) := by
  cases k with
  | proto fnName e => exact reloc_speAt A fnName e
  | sessionNotFound addr op =>
    refine reloc_congr (fun p => by
        dsimp only [RunDrop.speOwnedAt, LibsignalPublicApiRepr.apiErrAt,
          LibsignalPublicApiRepr.addrCloneAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])
      (reloc_sepConj_off (n₁ := 24) (n₂ := 24) rfl (reloc_vecU8 A addr.name)
        (reloc_sepConj_off (n₁ := 1) (n₂ := 23) rfl (reloc_pointsTo8 addr.device)
          (reloc_sepConj_off (n₁ := 7) (n₂ := 16) rfl (reloc_memRegion 7 (by decide))
            (reloc_strRefAt (LibsignalTripleRatchetRepr.utf8 op)))))
  | untrustedIdentity addr =>
    refine reloc_congr (fun p => by
        dsimp only [RunDrop.speOwnedAt, LibsignalPublicApiRepr.apiErrAt,
          LibsignalPublicApiRepr.addrCloneAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl
        (reloc_pointsTo64 (speWord LibsignalPublicApiRepr.speUntrustedIdentity))
        (reloc_sepConj_off (n₁ := 24) (n₂ := 16) rfl (reloc_vecU8 A addr.name)
          (reloc_sepConj_off (n₁ := 1) (n₂ := 15) rfl (reloc_pointsTo8 addr.device)
            (reloc_sepConj_off (n₁ := 7) (n₂ := 8) rfl (reloc_memRegion 7 (by decide))
              (reloc_memRegion 8 (by decide))))))
  | badKemKeyType =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 31))
      (reloc_memRegion 40 (by decide))
  | badKemKeyLength =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord 33))
      (reloc_memRegion 40 (by decide))
  | plain i _ =>
    exact reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord i))
      (reloc_memRegion 40 (by decide))
  | withString i _ =>
    refine reloc_congr (fun p => by
        dsimp only [RunDrop.speOwnedAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 8) (n₂ := 40) rfl (reloc_pointsTo64 (speWord i))
        (reloc_sepConj_off (n₁ := 24) (n₂ := 16) rfl
          (reloc_sepExists fun bs => reloc_vecU8 A bs) (reloc_memRegion 16 (by decide))))

theorem reloc_idKeyPairOutAt (A : RustAlloc)
    (ans : Except Unit RecordCodecs.IdentityKeyPair) :
    RelocatableBlock 72 (fun p => idKeyPairOutAt A p ans) := by
  cases ans with
  | ok kp =>
    have hpk : RelocatableBlock 32 (fun p => p ↦ₛ kp.identityKey.publicKey.bytes.toList) := by
      have h := reloc_pointsToBytes kp.identityKey.publicKey.bytes.toList
      simpa only [kp.identityKey.publicKey.bytes.toList_length] using h
    have hsk : RelocatableBlock 32 (fun p => p ↦ₛ kp.privateKey.bytes.toList) := by
      have h := reloc_pointsToBytes kp.privateKey.bytes.toList
      simpa only [kp.privateKey.bytes.toList_length] using h
    refine reloc_congr (fun p => by
        dsimp only [idKeyPairOutAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 1) (n₂ := 71) rfl (reloc_pointsTo8 0#8)
        (reloc_sepConj_off (n₁ := 32) (n₂ := 39) rfl hpk
          (reloc_sepConj_off (n₁ := 32) (n₂ := 7) rfl hsk
            (reloc_memRegion 7 (by decide)))))
  | error u =>
    cases u
    refine reloc_congr (fun p => by
        dsimp only [idKeyPairOutAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd])
      (reloc_sepConj_off (n₁ := 1) (n₂ := 71) rfl (reloc_pointsTo8 1#8)
        (reloc_sepConj_off (n₁ := 7) (n₂ := 64) rfl (reloc_memRegion 7 (by decide))
          (reloc_sepConj_off (n₁ := 48) (n₂ := 16) rfl
            (reloc_sepExists fun k => reloc_speOwnedAt A k)
            (reloc_memRegion 16 (by decide)))))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

