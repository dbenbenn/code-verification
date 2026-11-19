/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Shared OOM Stubs and Error Cleanup Chain for Arm `R1b` (`R+0x2a60 .. R+0x2c7c`, `R+0x2d44 .. R+0x2d7c`)

Reusable `SepWPp` continuations for the OOM panic stubs (`alloc::raw_vec::handle_error`) and
error/reject cleanup tail of `run_hop_init2_ok` (Arm `R1b`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_fsp_align {s0 s : State} (hsp : s.sp = runFsp s0) (hsp0 : s0.spAligned = true) :
    runFsp s0 &&& 15#64 = 0#64 :=
  hsp ▸ eq_of_beq (r1b_spAligned_of_fsp hsp hsp0)

theorem r1b_allocFailedIn_mono {s0 s1 s2 : State}
    (ha : allocFailedIn s0 s1) (hp : s1.trace <+: s2.trace) :
    allocFailedIn s0 s2 := by
  unfold allocFailedIn at ha ⊢
  rcases hp with ⟨extTr, htr2⟩
  rw [← htr2, List.drop_append]
  exact List.mem_append_left _ ha

/-! ## `ownedBytes` / `vecU8` Bridges, `memRegion` Packing, and `r1b_SpePayload` -/

theorem r1b_ownedBytes_to_vecU8 (A : RustAlloc) (v cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len) ∗
      ownedBytes A cap ptr len bs) ⊢
      vecU8 A v bs := by
  dsimp only [vecU8, vecU8At, vecHeader, ownedBytes]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  conv => lhs; rw [sepConj_comm ((v + 16#64) ↦₆₄ len), sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨rfl, hle, hlt, hne⟩
  conv => rhs; rw [sepConj_comm ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length), sepConj_assoc]
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)

theorem r1b_cell64_cons {a : BitVec 64} (v : BitVec 64) {n : Nat} (hn : n < 2 ^ 64 - 8) :
    ((a ↦₆₄ v) ∗ memRegion (a + 8#64) n) ⊢ memRegion a (n + 8) :=
  ProofLib.memRegion_cons a v (n := n + 8) (by omega) (by omega)

theorem r1b_cells2_to_region16 (a : BitVec 64) (v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 :=
  Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _))
    (r1b_cell64_cons v0 (by decide))

theorem r1b_cells2_region8_to_24 (a : BitVec 64) (v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  have h16 : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
  refine Entails.trans (sepConj_mono_right (by rw [h16]; exact r1b_cell64_cons v1 (by decide))) ?_
  exact r1b_cell64_cons v0 (by decide)

theorem r1b_cell8_to_region (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 := by
  rw [ProofLib.memRegion_one a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem r1b_cell32_to_region (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 := by
  rw [ProofLib.memRegion_four a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem r1b_region16_to_cells (a : BitVec 64) :
    memRegion a 16 = ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
      (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, ProofLib.memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_left]
  congr 1; funext v0
  rw [sepExists_sepConj_right]

theorem r1b_region48_to_cells (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
  have h32 : memRegion (a + 32#64) 16 = ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
    have ha : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
    simpa [ha] using r1b_region16_to_cells (a + 32#64)
  have h16 : memRegion (a + 16#64) 16 = ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) := by
    have ha : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
    simpa [ha] using r1b_region16_to_cells (a + 16#64)
  have hsplit32 : memRegion (a + 16#64) 32 =
      memRegion (a + 16#64) 16 ∗ memRegion (a + 32#64) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, ProofLib.memRegion_split (a + 16#64) 16 16 (by decide),
      show a + 16#64 + 16#64 = a + 32#64 from by bv_omega]
  rw [show (48 : Nat) = 16 + 32 from rfl, ProofLib.memRegion_split a 16 32 (by decide),
    hsplit32, r1b_region16_to_cells a, h16, h32]
  simp only [sepExists_sepConj_left]
  congr 1; funext v0
  simp only [sepExists_sepConj_right]
  congr 1; funext v1
  congr 1; funext v2; congr 1; funext v3; congr 1; funext v4; congr 1; funext v5
  ac_rfl

@[expose] def r1b_SpeRegs (cap ptr len r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) : Prop :=
  (r9 &&& 0xffffffff#64) = (cap &&& 0xffffffff#64) ∧
  (r23 <<< 32) = (cap &&& 0xffffffff00000000#64) ∧
  (r27 &&& 0x00ffffffffffffff#64) = (ptr &&& 0x00ffffffffffffff#64) ∧
  ((r16 &&& 0xff#64) <<< 56) = (ptr &&& 0xff00000000000000#64) ∧
  ((r14 &&& 16777215#64) <<< 32) = (len &&& 0x00ffffff00000000#64) ∧
  ((r15 <<< 8) &&& 0xffffff00#64) = (len &&& 0x00000000ffffff00#64) ∧
  (r28 <<< 56) = (len &&& 0xff00000000000000#64) ∧
  (r22 &&& 0xff#64) = (len &&& 0xff#64)

theorem r1b_SpeRegs.of_zext_r9_r22 {cap ptr len r10 r23 r27 r16 r14 r15 r28 r2 : BitVec 64}
    (h : r1b_SpeRegs cap ptr len r10 r23 r27 r16 r14 r15 r28 r2) :
    r1b_SpeRegs cap ptr len
      ((r10.truncate 32).zeroExtend 64) r23 r27 r16 r14 r15 r28
      ((r2.truncate 32).zeroExtend 64) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨by bv_bits, h2, h3, h4, h5, h6, h7, by bv_bits⟩

theorem r1b_SpeRegs.repack {cap ptr len r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64}
    (h : r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22) :
    (((r9 &&& 0xffffffff#64) ||| (r23 <<< 32)) = cap) ∧
    (((r27 &&& 0x00ffffffffffffff#64) ||| ((r16 &&& 0xff#64) <<< 56)) = ptr) ∧
    (((((r14 &&& 16777215#64) <<< 32) ||| (r28 <<< 56)) |||
      (((r15 <<< 8) &&& 0xffffff00#64) ||| (r22 &&& 0xff#64))) = len) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨by bv_bits, by bv_bits, by bv_bits⟩

@[expose] def r1b_SpePayload (A : RustAlloc)
    (tag r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) : SepProp :=
  ∃∗ isPlain : Bool,
    if isPlain then
      ∃∗ i : Nat, ⌜RunDrop.PlainSpeTag i ∧ tag = speWord i⌝
    else
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64, ∃∗ bs : List (BitVec 8),
        ⌜tag = speWord 1 ∧ r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22⌝ ∗
          ownedBytes A cap ptr len bs

theorem r1b_SpePayload_plain (A : RustAlloc) {i : Nat} (hi : RunDrop.PlainSpeTag i)
    (r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64) :
    emp ⊢ r1b_SpePayload A (speWord i) r9 r23 r27 r16 r14 r15 r28 r22 := by
  refine Entails.sepExists_right true (Entails.sepExists_right i ?_)
  rw [← sepConj_emp ⌜RunDrop.PlainSpeTag i ∧ speWord i = speWord i⌝]
  exact Entails.pure_right ⟨hi, rfl⟩ (Entails.refl _)

theorem r1b_SpePayload_str (A : RustAlloc) {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    {r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64}
    (hregs : r1b_SpeRegs cap ptr len r9 r23 r27 r16 r14 r15 r28 r22) :
    ownedBytes A cap ptr len bs ⊢
      r1b_SpePayload A (speWord 1) r9 r23 r27 r16 r14 r15 r28 r22 := by
  refine Entails.sepExists_right false
    (Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right len (Entails.sepExists_right bs ?_))))
  exact Entails.pure_right ⟨rfl, hregs⟩ (Entails.refl _)

theorem r1b_SpePayload_zext_r9_r22 {A : RustAlloc}
    {tag r10 r23 r27 r16 r14 r15 r28 r2 : BitVec 64} :
    r1b_SpePayload A tag r10 r23 r27 r16 r14 r15 r28 r2 ⊢
      r1b_SpePayload A tag
        ((r10.truncate 32).zeroExtend 64) r23 r27 r16 r14 r15 r28
        ((r2.truncate 32).zeroExtend 64) := by
  dsimp only [r1b_SpePayload]
  apply Entails.sepExists_elim
  rintro (_ | _)
  · refine Entails.sepExists_right false ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Entails.sepExists_elim fun cap => Entails.sepExists_right cap <|
      Entails.sepExists_elim fun ptr => Entails.sepExists_right ptr <|
      Entails.sepExists_elim fun len => Entails.sepExists_right len <|
      Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    apply Entails.pure_left
    rintro ⟨htag, hregs⟩
    exact Entails.pure_right ⟨htag, hregs.of_zext_r9_r22⟩ (Entails.refl _)
  · exact Entails.sepExists_right true (Entails.refl _)

theorem r1b_pack_speOwnedAt (A : RustAlloc) (a tag w1 w2 w3 w4 w5 : BitVec 64)
    (r9 r23 r27 r16 r14 r15 r28 r22 : BitVec 64)
    (hw1 : w1 = ((r9 &&& 0xffffffff#64) ||| (r23 <<< 32)))
    (hw2 : w2 = ((r27 &&& 0x00ffffffffffffff#64) ||| ((r16 &&& 0xff#64) <<< 56)))
    (hw3 : w3 = ((((r14 &&& 16777215#64) <<< 32) ||| (r28 <<< 56)) |||
      (((r15 <<< 8) &&& 0xffffff00#64) ||| (r22 &&& 0xff#64)))) :
    r1b_SpePayload A tag r9 r23 r27 r16 r14 r15 r28 r22 ∗
      ((a ↦₆₄ tag) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k := by
  have htail16 : ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 0x20#64) 16 := by
    have h40 : a + 40#64 = (a + 32#64) + 8#64 := by bv_omega
    rw [h40]; exact r1b_cells2_to_region16 (a + 32#64) w4 w5
  have htail40 : ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion (a + 8#64) 40 := by
    have h24 : ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 0x20#64) 16 ⊢ memRegion (a + 24#64) 24 := by
      have ha : a + 0x20#64 = (a + 24#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w3 (by decide)
    have h16 : ((a + 16#64) ↦₆₄ w2) ∗ memRegion (a + 24#64) 24 ⊢ memRegion (a + 16#64) 32 := by
      have ha : a + 24#64 = (a + 16#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w2 (by decide)
    have h08 : ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
      have ha : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
      rw [ha]; exact r1b_cell64_cons w1 (by decide)
    exact Entails.trans (sepConj_mono_right (Entails.trans
      (sepConj_mono_right (Entails.trans (sepConj_mono_right htail16) h24)) h16)) h08
  dsimp only [r1b_SpePayload]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  rintro (_ | _)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro len
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro bs
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨rfl, hregs⟩
    rcases hregs.repack with ⟨hcap, hptr, hlen⟩
    rw [hw1, hcap, hw2, hptr, hw3, hlen]
    refine Entails.sepExists_right (.withString 1 (by decide)) ?_
    dsimp only [RunDrop.speOwnedAt]
    have hvec : ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        ((a + 24#64) ↦₆₄ len) ∗ ownedBytes A cap ptr len bs ⊢
        ∃∗ bs' : List (BitVec 8), vecU8 A (a + 8#64) bs' := by
      have ha16 : a + 16#64 = (a + 8#64) + 8#64 := by bv_omega
      have ha24 : a + 24#64 = (a + 8#64) + 16#64 := by bv_omega
      rw [ha16, ha24]
      exact Entails.trans (r1b_ownedBytes_to_vecU8 A (a + 8#64) cap ptr len bs)
        (Entails.sepExists_right bs (Entails.refl _))
    refine Entails.trans (Entails.of_eq (show
      ownedBytes A cap ptr len bs ∗ ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗
        ((a + 16#64) ↦₆₄ ptr) ∗ ((a + 24#64) ↦₆₄ len) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) =
      (a ↦₆₄ speWord 1) ∗ (((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        ((a + 24#64) ↦₆₄ len) ∗ ownedBytes A cap ptr len bs) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hvec htail16)
  · simp only [↓reduceIte]
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro i
    rw [← sepConj_emp ⌜RunDrop.PlainSpeTag i ∧ tag = speWord i⌝, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hi, rfl⟩
    refine Entails.sepExists_right (.plain i hi) ?_
    dsimp only [RunDrop.speOwnedAt]
    rw [emp_sepConj]
    exact sepConj_mono_right htail40

/-! ## OOM `alloc::raw_vec::handle_error` Panic Stubs (`R+0x2d44 .. R+0x2d7c`) -/

@[expose] def r1b_errFrameRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x110 ∗
  memRegion (fsp + 0x118#64) 4 ∗
  memRegion (fsp + 0x130#64) 0x20 ∗
  memRegion (fsp + 0x160#64) 0x08 ∗
  memRegion (fsp + 0x180#64) 0x08 ∗
  memRegion (fsp + 0x1d0#64) 0xd0 ∗
  memRegion (fsp + 0x2c0#64) 0x210 ∗
  memRegion (fsp + 0x500#64) 0x24f0

private theorem r1b_merge_region (fsp : BitVec 64) (o1 n1 n2 : Nat)
    (ho : BitVec.ofNat 64 o1 + BitVec.ofNat 64 n1 = BitVec.ofNat 64 (o1 + n1) := by decide)
    (hb : n1 + n2 ≤ 2 ^ 64 := by decide) :
    memRegion (fsp + BitVec.ofNat 64 o1) n1 ∗ memRegion (fsp + BitVec.ofNat 64 (o1 + n1)) n2 =
      memRegion (fsp + BitVec.ofNat 64 o1) (n1 + n2) := by
  have heq : fsp + BitVec.ofNat 64 (o1 + n1) = (fsp + BitVec.ofNat 64 o1) + BitVec.ofNat 64 n1 := by
    rw [BitVec.add_assoc, ho]
  rw [heq]
  exact (ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o1) n1 n2 hb).symm

theorem r1b_rejoin_errFrame (fsp : BitVec 64) :
    r1b_errFrameRest fsp ∗
    memRegion (fsp + 0x110#64) 8 ∗
    memRegion (fsp + 0x11c#64) 4 ∗
    memRegion (fsp + 0x120#64) 16 ∗
    memRegion (fsp + 0x150#64) 16 ∗
    memRegion (fsp + 0x168#64) 24 ∗
    memRegion (fsp + 0x188#64) 48 ∗
    memRegion (fsp + 0x1b8#64) 24 ∗
    memRegion (fsp + 0x2a0#64) 32 ∗
    memRegion (fsp + 0x4d0#64) 48 ⊢
    runLocals fsp [] := by
  dsimp only [r1b_errFrameRest, runLocals, runLocalsFrom]
  have hf0 : memRegion fsp 0x110 = memRegion (fsp + 0#64) 0x110 := by
    have hz : fsp + 0#64 = fsp := by bv_omega
    rw [hz]
  refine Entails.of_eq ?_
  calc
    _ = memRegion (fsp + 0#64) 0x110 ∗
        (memRegion (fsp + 0x110#64) 8 ∗
        (memRegion (fsp + 0x118#64) 4 ∗
        (memRegion (fsp + 0x11c#64) 4 ∗
        (memRegion (fsp + 0x120#64) 16 ∗
        (memRegion (fsp + 0x130#64) 0x20 ∗
        (memRegion (fsp + 0x150#64) 16 ∗
        (memRegion (fsp + 0x160#64) 8 ∗
        (memRegion (fsp + 0x168#64) 24 ∗
        (memRegion (fsp + 0x180#64) 8 ∗
        (memRegion (fsp + 0x188#64) 48 ∗
        (memRegion (fsp + 0x1b8#64) 24 ∗
        (memRegion (fsp + 0x1d0#64) 0xd0 ∗
        (memRegion (fsp + 0x2a0#64) 32 ∗
        (memRegion (fsp + 0x2c0#64) 0x210 ∗
        (memRegion (fsp + 0x4d0#64) 48 ∗
         memRegion (fsp + 0x500#64) 0x24f0))))))))))))))) := by rw [hf0]; ac_rfl
    _ = memRegion (fsp + 0#64) runLocalBytes := by
      rw [r1b_merge_region fsp 0x4d0 48 0x24f0,
          r1b_merge_region fsp 0x2c0 0x210 0x2520,
          r1b_merge_region fsp 0x2a0 32 0x2730,
          r1b_merge_region fsp 0x1d0 0xd0 0x2750,
          r1b_merge_region fsp 0x1b8 24 0x2820,
          r1b_merge_region fsp 0x188 48 0x2838,
          r1b_merge_region fsp 0x180 8 0x2868,
          r1b_merge_region fsp 0x168 24 0x2870,
          r1b_merge_region fsp 0x160 8 0x2888,
          r1b_merge_region fsp 0x150 16 0x2890,
          r1b_merge_region fsp 0x130 0x20 0x28a0,
          r1b_merge_region fsp 0x120 16 0x28c0,
          r1b_merge_region fsp 0x11c 4 0x28d0,
          r1b_merge_region fsp 0x118 4 0x28d4,
          r1b_merge_region fsp 0x110 8 0x28d8,
          r1b_merge_region fsp 0 0x110 0x28e0]

@[expose] def r1b_errCore (A : RustAlloc) (g : RunCall) (d : Init1Data) (s0 : State) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗
  memRegion g.call 56 ∗
  storesAt A g.stores StoresGhost.opened ∗
  (g.inp ↦ₛ inputOf g.i g.c) ∗
  addrNameHeap A d.meG ∗
  ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
  runSaved s0 ∗
  r1b_errFrameRest fsp ∗
  ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
  ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
  ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
  protocolAddressAt A d.peerG (fsp + 0x2a0#64)

@[expose] def r1b_errCommon (A : RustAlloc) (g : RunCall) (d : Init1Data) (s0 : State)
    (resStack : Nat) : SepProp :=
  r1b_errCore A g d s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap

/-! ## Cleanup Tail (`2c68 ← 2c54 ← 2c34 ← 2bf0`) -/

private theorem r1b_addrNameHeap_to_ownedBytes (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  dsimp only [addrNameHeap, ownedBytes]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hne⟩
  refine Entails.pure_right ⟨by simp, hle, hlt, hne⟩ (Entails.refl _)

end CryptoVerification.SignalSession.Cli.RunCompose
