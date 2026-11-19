/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``protocolAddressAt, #[2]), (``signalMessageAt, #[2]), (``recErrAt, #[1]), (``recFramePlaced, #[2])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

namespace SegExitDeallocFacts

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

end SegExitDeallocFacts

/-! ## `SatEntails` and `.rodata` drop jump table -/

@[expose] def SatEntails_shared_lb (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

theorem SatEntails_shared_lb.refl (P : SepProp) : SatEntails_shared_lb P P :=
  fun _ _ hm => hm

theorem SatEntails_shared_lb.of_eq {P Q : SepProp} (h : P = Q) : SatEntails_shared_lb P Q :=
  h ▸ SatEntails_shared_lb.refl P

theorem SatEntails_shared_lb.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntails_shared_lb P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

theorem SatEntails_shared_lb.trans {P Q S : SepProp}
    (h1 : SatEntails_shared_lb P Q) (h2 : SatEntails_shared_lb Q S) : SatEntails_shared_lb P S :=
  fun m R hm => h2 m R (h1 m R hm)

theorem SatEntails_shared_lb.drop_left (P Q : SepProp) : SatEntails_shared_lb (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

theorem SatEntails_shared_lb.drop_right (P Q : SepProp) : SatEntails_shared_lb (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

theorem SatEntails_shared_lb.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntails_shared_lb P₁ P₂) (h2 : SatEntails_shared_lb Q₁ Q₂) :
    SatEntails_shared_lb (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

theorem SatEntails_shared_lb.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntails_shared_lb P₁ P₂) {Q : SepProp} : SatEntails_shared_lb (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntails_shared_lb.sepConj_mono h (SatEntails_shared_lb.refl Q)

theorem SatEntails_shared_lb.sepConj_mono_right {P Q₁ Q₂ : SepProp}
    (h : SatEntails_shared_lb Q₁ Q₂) : SatEntails_shared_lb (P ∗ Q₁) (P ∗ Q₂) :=
  SatEntails_shared_lb.sepConj_mono (SatEntails_shared_lb.refl P) h

theorem SatEntails_shared_lb.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, SatEntails_shared_lb (P x) Q) : SatEntails_shared_lb (∃∗ x, P x) Q := by
  intro m R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x m R hx

theorem SatEntails_shared_lb.sepExists_right {α : Type} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : SatEntails_shared_lb P (Q x)) : SatEntails_shared_lb P (∃∗ y, Q y) :=
  SatEntails_shared_lb.trans h (SatEntails_shared_lb.of_entails (Entails.sepExists_right x (Entails.refl _)))

theorem SepWP_weaken_pre_sat_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntails_shared_lb P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)
private abbrev SepWP.weaken_pre_sat := @SepWP_weaken_pre_sat_shared_lb

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have hm' : s.mem ⊨ ⌜False⌝ ∗ (P ∗ Q ∗ R) := Satisfies.mono (by bi_entail) hm
  rw [satisfies_pure_sepConj] at hm'
  exact False.elim hm'.1

@[expose] def exitJumpTable_shared_lb : List (BitVec 8) :=
  [0x00#8, 0x3b#8, 0x36#8, 0x2c#8, 0x0b#8, 0x16#8, 0x40#8, 0x31#8,
   0x5f#8, 0x75#8, 0x6f#8, 0x31#8, 0x06#8, 0x1e#8, 0x11#8, 0x0d#8,
   0x0d#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
   0x00#8, 0x00#8, 0x00#8, 0x0d#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
   0x00#8, 0x0d#8, 0x11#8, 0x00#8, 0x00#8, 0x0d#8, 0x00#8, 0x0d#8,
   0x0d#8, 0x16#8, 0x0d#8]

/-! ## `RecErr` and `speAt` weakening helpers -/

theorem strRefAt_entails_memRegion16_shared_lb (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails_shared_lb (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntails_shared_lb.sepExists_elim
  intro p
  refine SatEntails_shared_lb.trans (SatEntails_shared_lb.sepConj_mono_right (SatEntails_shared_lb.drop_right _ _)) ?_
  exact SatEntails_shared_lb.of_entails (by sep_interval)

theorem spe_word8_40_entails_48_shared_lb (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  sep_interval

theorem spe_u64_at_8_entails_40_shared_lb (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  sep_interval

theorem spe_u32_at_8_entails_40_shared_lb (a : BitVec 64) (v : BitVec 32) :
    ((a + 8#64) ↦₃₂ v) ∗ memRegion (a + 12#64) 36 ⊢ memRegion (a + 8#64) 40 := by
  sep_interval

theorem spe_u8_at_8_entails_40_shared_lb (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  sep_interval

theorem spe_u8_at_32_entails_16_shared_lb (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  sep_interval

theorem spe_u32x2_at_8_entails_40_shared_lb (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  sep_interval

theorem spe_strRef_at_8_entails_40_shared_lb (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails_shared_lb (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    sep_interval_eq
  rw [h]
  exact SatEntails_shared_lb.sepConj_mono_left (strRefAt_entails_memRegion16_shared_lb (a + 8#64) lit)

/-- `RecErr.iscmk` (`DecX.iscmkErrAt`, tag `speWord 20` + static `&str`) exposes its tag word and a
40-byte payload region. -/
theorem iscmk_entails_40_shared_lb (A : RustAlloc) (a : BitVec 64) :
    SatEntails_shared_lb (recErrAt A a .iscmk) ((a ↦₆₄ speWord 20) ∗ memRegion (a + 8#64) 40) := by
  simp only [recErrAt, Proofs.libsignal.SR.DecX.iscmkErrAt, Proofs.libsignal.SR.DecX.iscmkBodyAt]
  rw [show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  exact SatEntails_shared_lb.sepConj_mono_right (spe_strRef_at_8_entails_40_shared_lb _ _)

private theorem vecU8At_entails_dealloc (A : RustAlloc) (a : BitVec 64) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) _)) ?_
  refine sepConj_mono_right ?_
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, _⟩
  by_cases hcap : cap = 0#64
  · subst hcap
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  · have hcap0 : ¬ cap = 0 := hcap
    have hbeq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap0, hbeq, Bool.false_eq_true, ↓reduceIte]
    refine sepConj_mono_right ?_
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      exact memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

private theorem vecU8_at_8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_dealloc A (a + 8#64) cap ptr bs)) ?_
  generalize (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) = D
  sep_interval

theorem spe_str_words_entails_48_shared_lb (a w cap ptr : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  sep_interval

theorem spe_str_after_weaken_shared_lb (a w cap ptr : BitVec 64) (ro rest : SepProp) :
    SatEntails_shared_lb
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ rest)
      (memRegion a 48 ∗ rest) := by
  refine SatEntails_shared_lb.trans
    (SatEntails_shared_lb.of_entails (by sep_interval : _ ⊢ memRegion a 48 ∗ (ro ∗ rest))) ?_
  exact SatEntails_shared_lb.sepConj_mono_right (SatEntails_shared_lb.drop_left ro rest)

theorem spe_noop_after_weaken_shared_lb (a w : BitVec 64) (ro rest : SepProp) :
    SatEntails_shared_lb
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ rest)
      (memRegion a 48 ∗ rest) := by
  refine SatEntails_shared_lb.trans
    (SatEntails_shared_lb.of_entails (by sep_interval : _ ⊢ memRegion a 48 ∗ (ro ∗ rest))) ?_
  exact SatEntails_shared_lb.sepConj_mono_right (SatEntails_shared_lb.drop_left ro rest)

private theorem speAt_invalidState_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails_shared_lb (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails_shared_lb.sepExists_elim; intro bs
  refine SatEntails_shared_lb.trans
    (SatEntails_shared_lb.sepConj_mono_right (SatEntails_shared_lb.sepConj_mono_right (strRefAt_entails_memRegion16_shared_lb (a + 32#64) fnName))) ?_
  apply SatEntails_shared_lb.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

theorem invalidMessageStrAt_entails_vecU8_shared_lb (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right tooFarInFutureStr (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right macFailedStr (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem speAt_invalidMessage_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails_shared_lb (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails_shared_lb.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8_shared_lb A (a + 8#64) r)
      (spe_u8_at_32_entails_16_shared_lb a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weaken (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (r : RecErr) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails_shared_lb ro_tbl ro_byte)
    (he : SatEntails_shared_lb (recErrAt A a r)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails_shared_lb (ro_tbl ∗ (recErrAt A a r ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails_shared_lb.trans (SatEntails_shared_lb.sepConj_mono hbyte (SatEntails_shared_lb.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails_shared_lb.sepExists_elim; intro cap
  apply SatEntails_shared_lb.sepExists_elim; intro ptr
  refine SatEntails_shared_lb.sepExists_right cap (SatEntails_shared_lb.sepExists_right ptr ?_)
  generalize (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) = D
  exact SatEntails_shared_lb.of_entails (by bi_entail)

theorem spe_unit_pre_weaken_shared_lb (A : RustAlloc)
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (r : RecErr) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails_shared_lb ro_tbl ro_byte)
    (he : SatEntails_shared_lb (recErrAt A a r) ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40))
    (rest : SepProp) :
    SatEntails_shared_lb (ro_tbl ∗ (recErrAt A a r ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntails_shared_lb.trans (SatEntails_shared_lb.sepConj_mono hbyte (SatEntails_shared_lb.sepConj_mono_left he)) ?_
  exact SatEntails_shared_lb.of_entails (by bi_entail)

/-! ## Single-element error drop (`+0x1e8c → +0x1f34`) -/

private theorem stackAt_root_split_alloc (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack (rootStack - allocHookStack) (by decide)

/-! ## Frame folding and `segExit_ok` (`+0x1e8c → +0x1f50`) -/

theorem frame_high_entails_0x920_shared_lb (sp : BitVec 64)
    (w5b0 : BitVec 64) (b5bc : BitVec 8) (w5c0 w5c8 w5d0 w5d8 w5e0 w5e8 : BitVec 64) :
    memRegion (sp + 0x4e0#64) 0xd0 ∗
      ((sp + 0x5b0#64) ↦₆₄ w5b0) ∗ memRegion (sp + 0x5b8#64) 4 ∗
      ((sp + 0x5bc#64) ↦₈ b5bc) ∗ memRegion (sp + 0x5bd#64) 3 ∗
      ((sp + 0x5c0#64) ↦₆₄ w5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ w5c8) ∗
      ((sp + 0x5d0#64) ↦₆₄ w5d0) ∗
      ((sp + 0x5d8#64) ↦₆₄ w5d8) ∗ ((sp + 0x5d8#64 + 8#64) ↦₆₄ w5e0) ∗
      ((sp + 0x5d8#64 + 16#64) ↦₆₄ w5e8) ∗
      memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xca0#64) 344 ∗
      memRegion (sp + 0xdf8#64) 8 ⊢
      memRegion (sp + 0x4e0#64) 0x920 := by
  sep_interval

private theorem SepWP.elim_no_oom {prog : Program} {target : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target s P post) (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem) :
    ∃ sf, Steps prog s sf ∧ sf.pc = target ∧ sf.status = .Running ∧
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ post sf Pf := by
  obtain ⟨sf, hsteps, hok | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · exact ⟨sf, hsteps, hok⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

/-! ## Relocatable `[LibsignalPlacement]` `segExit_placed_ok` -/
abbrev exitJumpTableSym : String := "libsignal_session:.rodata.session_message_decrypt_signal"
theorem rodata_exitJumpTable_placed_intro [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsmpl.ρ exitJumpTableSym ↦ᵣ exitJumpTable_shared_lb) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

theorem exitJumpTable_byte_placed (roAddr : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : BitVec.ofNat 64 (15 + i) = off)
    (heq : exitJumpTable_shared_lb = exitJumpTable_shared_lb.take (15 + i) ++ (b :: exitJumpTable_shared_lb.drop (15 + i + 1)))
    (hlen : (exitJumpTable_shared_lb.take (15 + i)).length = 15 + i) :
    SatEntails_shared_lb (roAddr ↦ᵣ exitJumpTable_shared_lb) ((roAddr + off) ↦₈ᵣ b) := by
  have h : (roAddr ↦ᵣ exitJumpTable_shared_lb) =
      (roAddr ↦ᵣ exitJumpTable_shared_lb.take (15 + i)) ∗
        (((roAddr + BitVec.ofNat 64 (15 + i)) ↦₈ᵣ b) ∗
         ((roAddr + BitVec.ofNat 64 (15 + i) + 1#64) ↦ᵣ exitJumpTable_shared_lb.drop (15 + i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, hoff]
  exact SatEntails_shared_lb.trans (SatEntails_shared_lb.drop_left _ _) (SatEntails_shared_lb.drop_right _ _)

private def recFramePlacedRest [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost)
    (sp : BitVec 64) : SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ FromRecordCallees.lsLogOff ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - allocHookStack)

register_sep_key recFramePlacedRest [2]

private theorem recFramePlaced_split_alloc [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost)
    (sp : BitVec 64) :
    recFramePlaced A x sp =
      recFramePlacedRest A x sp ∗ stackAt sp allocHookStack ∗ A.pool := by
  unfold recFramePlaced recFramePlacedRest
  rw [stackAt_root_split_alloc sp]
  apply Entails.antisymm <;> bi_entail

private theorem recPostPlaced_of_frame_aux [LibsignalPlacement] {A : RustAlloc}
    (x : RecordDecryptGhost) (S_sess resSlot tape R : SepProp) (s0 sf : State)
    (w_cap w_ptr w_len : BitVec 64)
    (hm : sf.mem ⊨ recFramePlaced A x s0.sp ∗
      ((s0.sp + 0x5d8#64) ↦₆₄ w_cap) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ w_ptr) ∗
      ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ w_len) ∗ memRegion (s0.sp + 0xca0#64) 344 ∗
      S_sess ∗ resSlot ∗ tape ∗ R) :
    sf.mem ⊨ memRegion s0.sp 0xa0 ∗
      ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
      ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
      S_sess ∗ resSlot ∗ memRegion (s0.sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tape ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R := by
  dsimp only [recFramePlaced] at hm
  exact Satisfies.mono (by sep_interval) hm

local macro "seg_exit_noop_placed " r:term:max i:num w:term:max off:term:max he:term:max : tactic =>
  `(tactic| (
    refine SepWP.weaken_pre_sat (spe_unit_pre_weaken_shared_lb _ _ $r $i $w rfl
      (exitJumpTable_byte_placed _ $i $off 0x00#8 rfl (by rfl_kernel) (by rfl_kernel)) $he _) ?_
    wp_steps; refine SepWP.weaken_pre_sat (spe_noop_after_weaken_shared_lb _ _ _ _) ?_; wp_done))

local macro "seg_exit_str_placed " hsp:ident _s0:ident r:term:max i:num w:term:max off:term:max he:term:max : tactic =>
  `(tactic| (
    refine SepWP.weaken_pre_sat (spe_str_pre_weaken _ _ $r $i $w rfl
      (exitJumpTable_byte_placed _ $i $off 0x0d#8 rfl (by rfl_kernel) (by rfl_kernel)) $he _) ?_
    wp_pull_exists; rename_i cap ptr; by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps
      refine SepWP.weaken_pre_sat (spe_str_after_weaken_shared_lb _ _ _ _ _ _) ?_; wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]; wp_steps
      refine SepWP.weaken_pre_sat (spe_str_after_weaken_shared_lb _ _ _ _ _ _) ?_; wp_apply; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      rw [$hsp:ident]
      bi_entail))

private theorem segExit_drop_one_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (p : BitVec 64) (r : RecErr) (s0 s : State)
    (hpc_s : s.pc = (blkPl_197).base + 7820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s.spAligned = true) :
    SepWP ((blkPC_197).rebase (blkPl_197).base H)
      ((blkPl_197).base + 7988#64) s
      ((lsmpl.ρ exitJumpTableSym ↦ᵣ exitJumpTable_shared_lb) ∗
        (recErrAt A p r ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool)))
      (fun sm Pm =>
        (Pm ⊢ memRegion p 48 ∗
          (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
            stackAt s0.sp allocHookStack ∗ A.pool)) ∧
        sm.sp = s.sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x20 = p ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hdealloc := ls_hook_ok_226 (by decide) hdealloc_sat
  cases r with
  | version v =>
    seg_exit_noop_placed (.version v) 6 0x8000000000000006#64 21#64
      (SatEntails_shared_lb.of_entails (by simp only [recErrAt]; exact sepConj_mono_right (spe_u32_at_8_entails_40_shared_lb _ _)))
  | spe e =>
    cases e with
    | panic => simp only [recErrAt, speAt]; exact SepWP.false_elim
    | invalidState =>
      seg_exit_str_placed hsp s0 (.spe .invalidState) 1 0x8000000000000001#64 16#64
        (by simpa only [recErrAt] using speAt_invalidState_expose A (utf8 "decrypt") p)
    | invalidMessage t r =>
      seg_exit_str_placed hsp s0 (.spe (.invalidMessage t r)) 24 0x8000000000000018#64 39#64
        (by simpa only [recErrAt] using speAt_invalidMessage_expose A (utf8 "decrypt") p t r)
    | invalidProtobufEncoding =>
      seg_exit_noop_placed (.spe .invalidProtobufEncoding) 2 0x8000000000000002#64 17#64 (SatEntails_shared_lb.refl _)
    | ciphertextMessageTooShort n =>
      seg_exit_noop_placed (.spe (.ciphertextMessageTooShort n)) 3 0x8000000000000003#64 18#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_shared_lb _ _)))
    | legacyCiphertextVersion v =>
      seg_exit_noop_placed (.spe (.legacyCiphertextVersion v)) 4 0x8000000000000004#64 19#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | unrecognizedCiphertextVersion v =>
      seg_exit_noop_placed (.spe (.unrecognizedCiphertextVersion v)) 5 0x8000000000000005#64 20#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | noKeyTypeIdentifier =>
      seg_exit_noop_placed (.spe .noKeyTypeIdentifier) 7 0x8000000000000007#64 22#64 (SatEntails_shared_lb.refl _)
    | badKeyType t =>
      seg_exit_noop_placed (.spe (.badKeyType t)) 8 0x8000000000000008#64 23#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40_shared_lb _ _)))
    | badKeyLength n =>
      seg_exit_noop_placed (.spe (.badKeyLength n)) 9 0x8000000000000009#64 24#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40_shared_lb _ _)))
    | invalidKeyAgreement =>
      seg_exit_noop_placed (.spe .invalidKeyAgreement) 10 0x800000000000000a#64 25#64 (SatEntails_shared_lb.refl _)
    | invalidSessionStructure r =>
      seg_exit_noop_placed (.spe (.invalidSessionStructure r)) 20 0x8000000000000014#64 35#64
        (by simp only [recErrAt, speAt]; exact SatEntails_shared_lb.sepConj_mono_right (spe_strRef_at_8_entails_40_shared_lb _ _))
    | duplicatedMessage idx c =>
      seg_exit_noop_placed (.spe (.duplicatedMessage idx c)) 23 0x8000000000000017#64 38#64
        (SatEntails_shared_lb.of_entails (by simp only [recErrAt, speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40_shared_lb _ _ _)))
  | iscmk =>
    seg_exit_noop_placed .iscmk 20 0x8000000000000014#64 35#64 (iscmk_entails_40_shared_lb A p)

private theorem segExit_main_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : RecordDecryptGhost) (S_sess resSlot tape R : SepProp) (s0 s : State)
    (hpc_s : s.pc = recJPCPlaced)
    (hmeta : recMetaPlaced s0 s)
    (hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hx26 : s.readReg64 .x26 = s0.sp + 0xa0#64)
    (hx27 : s.readReg64 .x27 = x.sret)
    (hx28 : s.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1)
    (hmem : s.mem ⊨ recFramePlaced A x s0.sp ∗ S_sess ∗ resSlot ∗
      (∃∗ errs : List RecErr, errsAt A (s0.sp + 0x5d8#64) errs) ∗ memRegion (s0.sp + 0xca0#64) 344 ∗
      tape ∗ R)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem) :
    ∃ sf, Steps ((blkPC_197).rebase (blkPl_197).base H) s sf ∧
      sf.pc = recExitPlaced ∧ sf.status = .Running ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      ((x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
        sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
        sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
        sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1) ∧
      (sf.mem ⊨
        memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        S_sess ∗ resSlot ∗
        memRegion (s0.sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tape ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
  obtain ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, hvregs⟩ := hmeta
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hro := hfl.2
  have hdealloc := ls_hook_ok_226 (by decide) hdealloc_sat
  dsimp only [recJPCPlaced] at hpc_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  obtain ⟨errs, hmem⟩ := hmem
  rcases errs with _ | ⟨r_err, _ | ⟨r2, rest⟩⟩
  · have hmem_nil : s.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64)) ∗
        (recFramePlaced A x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) := by
      dsimp only [errsAt] at hmem
      exact Satisfies.mono (by bi_entail) hmem
    clear hmem
    have hwp_nil : SepWP ((blkPC_197).rebase (blkPl_197).base H)
        ((blkPl_197).base + 8016#64) s
        (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
         ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64))
        (fun sf Pf =>
          Pf = (((s0.sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ 8#64) ∗
            ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 0#64)) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      wp_steps
      exact SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨rfl, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
    rcases hwp_nil.elim hmem_nil hL with
      ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, rfl, hsp_sf, htr_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    refine ⟨sf, hsteps, hpc_sf, hrun_sf, hvregs_sf, ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    apply recPostPlaced_of_frame_aux x S_sess resSlot tape R s0 sf 0#64 8#64 0#64
    exact Satisfies.mono (by bi_entail) hmf
  · dsimp only [errsAt] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
    obtain ⟨p, hmem⟩ := hmem
    have hmem_ro := rodata_exitJumpTable_placed_intro hro hmem
    clear hmem
    rw [recFramePlaced_split_alloc A x s0.sp] at hmem_ro
    have hmem_p : s.mem ⊨ ⌜p ≠ 0⌝ ∗
        ((((lsmpl.ρ exitJumpTableSym) ↦ᵣ exitJumpTable_shared_lb) ∗
          (recErrAt A p r_err ∗
            (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
              stackAt s0.sp allocHookStack ∗ A.pool))) ∗
         (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion (p + 48#64) 144 ∗
          recFramePlacedRest A x s0.sp ∗
          memRegion (s0.sp + 0xca0#64) 344 ∗
          S_sess ∗ resSlot ∗ tape ∗ R)) := by
      exact Satisfies.mono (by bi_entail) hmem_ro
    clear hmem_ro
    rw [satisfies_pure_sepConj] at hmem_p
    obtain ⟨_hp, hmem_drop⟩ := hmem_p
    have hdrop := segExit_drop_one_placed hdealloc_sat p r_err s0 s hpc_s hrun hsp hsp_align
    rcases hdrop.elim hmem_drop hL with ⟨sm, hsteps1, ⟨hpc_sm, hrun_sm, Pm, hmm, hent_m, hsp_sm, htr_sm, hx20_sm,
      hx26_sm, hx27_sm, hx28_sm, hx29_sm, hvregs_sm0⟩ | ⟨_, hoom⟩⟩
    swap; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmem_drop hdrop
    have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hvregs_sm0.trans hvregs
    have hmm' := Satisfies.mono (sepConj_mono_left hent_m) hmm
    clear hmm hent_m
    have hmm_dealloc : sm.mem ⊨
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool) ∗
        (((s0.sp + 0x5d8#64 + 8#64) ↦₆₄ p) ∗ ((s0.sp + 0x5d8#64 + 16#64) ↦₆₄ 1#64) ∗
         recFramePlacedRest A x s0.sp ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗
         S_sess ∗ resSlot ∗ tape ∗ R) :=
      Satisfies.mono (by sep_interval) hmm'
    clear hmm'
    have hsp_sm0 : sm.sp = s0.sp := hsp_sm.trans hsp
    have hwp_dealloc : SepWP ((blkPC_197).rebase (blkPl_197).base H)
        ((blkPl_197).base + 8016#64) sm
        (((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ A.live p 192 8 ∗ memRegion p 192 ∗
         stackAt s0.sp allocHookStack ∗ A.pool)
        (fun sf Pf =>
          (Pf ⊢ ((s0.sp + 0x5d8#64) ↦₆₄ 4#64) ∗ stackAt s0.sp allocHookStack ∗ A.pool) ∧
          sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      wp_steps
      wp_apply
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨?_, by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      rw [hsp_sm0]
      bi_entail
    rcases hwp_dealloc.elim hmm_dealloc (hsteps1.codeLoaded hL) with
      ⟨sf, hsteps2, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_f, hsp_sf, htr_sf,
        hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ | ⟨_, hoom⟩⟩
    rotate_left; · exact (not_satisfies_false_sepConj hoom).elim
    clear hmm_dealloc hwp_dealloc
    have hmf' := Satisfies.mono (sepConj_mono_left hent_f) hmf
    clear hmf hent_f
    refine ⟨sf, hsteps1.trans hsteps2, hpc_sf, hrun_sf, hvregs_sf, ⟨hno_pan, htr_sf, hsp_sf, hx29_sf, hx27_sf, hx26_sf, hx28_sf⟩, ?_⟩
    apply recPostPlaced_of_frame_aux x S_sess resSlot tape R s0 sf 4#64 p 1#64
    rw [recFramePlaced_split_alloc A x s0.sp]
    exact Satisfies.mono (by bi_entail) hmf'
  · dsimp only [errsAt] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (recFramePlaced A x s0.sp ∗ S_sess ∗ resSlot ∗
         memRegion (s0.sp + 0xca0#64) 344 ∗ tape ∗ R) :=
      Satisfies.mono (by bi_entail) hmem
    rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1

theorem segExit_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} :
    SegExitPlacedSpec C A ctl uuidTryParse S H := by
  intro hdealloc_sat x R s0 s hJ hL
  obtain ⟨hpc_s, hmeta, hno_pan, hx26, hx27, hx28, hmem⟩ := hJ
  obtain ⟨sf, hsteps, hpc_sf, hrun_sf, hvregs_sf, hpure_sf, hmem_sf⟩ :=
    segExit_main_placed hdealloc_sat x _ _ _ R s0 s hpc_s hmeta hno_pan hx26 hx27 hx28 hmem hL
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hrun_sf, hvregs_sf, ?_⟩⟩
  simp only [recordDecryptPlacedSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpure_sf, hmem_sf⟩

end CryptoVerification.LibsignalTripleRatchet.Record
