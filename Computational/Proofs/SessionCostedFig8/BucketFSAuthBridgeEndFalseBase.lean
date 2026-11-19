/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux

/-!
# Base Semantics, State Invariants, and Initialization Hoare Proof for `la = false`

Defines `FSFalseSemantics`, slot-to-epoch decoding (`slotEpoch`, `slotOf`), the active and frozen
state invariants (`WinSafe`, `SessBound`, `EngineWF`, `SlotSync`, `ForgedInv`, `MainInv`,
`ActiveInv`, `FalseInv`), pure game-state lemmas, `lazy_cs_hoare`, frozen-state preservation, and
`initFSMultiBucketAuth_false_hoare`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (Pos Record GameState ltOpt healedBy maxOpt
  lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (PartyState Header healEpoch
  FSMultiSpec FSMultiBook mkParties sampleT)
open _root_.CryptoGames.SM.Engine (VP Ctx TComp EState liftH abortE commitE
  vSend vRecv deliverE injectE)
open _root_.CryptoGames.SM.Thm1L17 (le_maxOpt_left max?_cons_of_forall_le)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (postLeak bucketAuthCfg)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState FSMultiBucketAuthEState liftFSMultiBucket lookupMultiBucketF
  regSessMultiBucket regSessOptMultiBucket validGuessBucketParAuth rootFSMultiBucketAuth
  isHonestHdrMultiBucket hooksFSMultiBucketAuth initFSMultiBucketAuth implFSMultiBucketAuth)

/-! ## 1. `la = false` Ideal-Cutoff Semantics (`FSFalseSemantics`) & Slot Decoding -/

structure FSFalseSemantics (SS RS T M C : Type) where
  H : ∀ {α : Type},
    ((ℕ → ℕ) → (ℕ → Option ℕ) → Prop) →
    (α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop) →
    OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α → Prop
  pure : ∀ {α : Type} {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} (a : α),
    (∀ ns sc, Pre ns sc → Post a ns sc) → H Pre Post (Pure.pure a)
  conseq : ∀ {α : Type} {Pre₁ Pre₂ : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post₁ Post₂ : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α},
    H Pre₁ Post₁ x →
    (∀ ns sc, Pre₂ ns sc → Pre₁ ns sc) →
    (∀ a ns sc, Post₁ a ns sc → Post₂ a ns sc) →
    H Pre₂ Post₂ x
  bind : ∀ {α β : Type} {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Mid : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : β → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α}
    {f : α → OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) β},
    H Pre Mid x → (∀ a, H (Mid a) Post (f a)) → H Pre Post (x >>= f)
  coin : ∀ (n : unifSpec.Domain) {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop},
    H Pre (fun _ ns sc => Pre ns sc)
      (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS T M (ℕ × C)) (.inl n)))
  tr : ∀ {RSt K I : Type} (sIdx : ℕ) (hdr : Header T) (m : M)
    (hs : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop},
    H Pre
      (fun (out : Option (ℕ × C) × FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        out.2 = hs ∧ ∃ ns sc, Pre ns sc ∧ sc' = sc ∧
        ((out.1 = none ∧ ns' = ns) ∨
         (∃ ct, out.1 = some (ns sIdx + 1, ct) ∧ ns' = Function.update ns sIdx (ns sIdx + 1))))
      ((liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
          (SenderState := SS) (ReceiverState := RS) hdr m)).run hs)
  cs : ∀ {RSt K I : Type} (sIdx : ℕ)
    (hs : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop},
    H Pre
      (fun (out : Option SS × FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        out.2 = hs ∧ ∃ ns sc, Pre ns sc ∧ ns' = ns ∧
        ((out.1 = none ∧ sc' = sc) ∨
         (∃ w, out.1 = some w ∧
           sc' = Function.update sc sIdx (some ((sc sIdx).getD (ns sIdx))))))
      ((liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
          (ReceiverState := RS) (AssocData := Header T) (Message := M)
          (Ciphertext := ℕ × C))).run hs)
  dl : ∀ {RSt K I : Type} (sIdx : ℕ) (hdr : Header T) (e : ℕ × C)
    (hs : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop},
    H Pre
      (fun (out : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M) ×
          FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        out.2 = hs ∧ Pre ns' sc' ∧
        (∀ i mo', out.1 = some (.accepted i mo') → i = e.1))
      ((liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.deliverQuery
          (SenderState := SS) (ReceiverState := RS) hdr e)).run hs)
  ij : ∀ {RSt K I : Type} (sIdx : ℕ) (hdr : Header T) (e : ℕ × C)
    (hs : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop},
    H Pre
      (fun (out : Option (_root_.CryptoGames.FSAEAD.ReceiveResult M) ×
          FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        out.2 = hs ∧ Pre ns' sc' ∧
        (∀ i mo', out.1 = some (.accepted i mo') → i = e.1) ∧
        ((∀ c, sc' sIdx = some c → e.1 ≤ c) → ∀ i mo', out.1 ≠ some (.accepted i mo')))
      ((liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.injectQuery
          (SenderState := SS) (ReceiverState := RS) hdr e)).run hs)
  and_prop : ∀ {α : Type} (P : Prop)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α},
    (P → H Pre Post x) → H (fun ns sc => P ∧ Pre ns sc) Post x

theorem FSFalseSemantics.exfalso {SS RS T M C : Type} (S : FSFalseSemantics SS RS T M C)
    {α : Type} {Post : α → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {x : OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C)) α} :
    S.H (fun _ _ => False) Post x :=
  S.conseq (S.and_prop False (fun h => nomatch h) (Pre := fun _ _ => True))
    (fun _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h)

@[expose] def slotEpoch (L : ℕ) (gMain : Bool) (tL : Option ℕ) (sIdx : ℕ) : ℕ :=
  (if gMain then sIdx else sIdx - 1) / L + healEpoch tL

abbrev slotOf (q : ℕ) (tL : Option ℕ) (τ : ℕ) : ℕ :=
  (q + 1) * (τ - healEpoch tL)

theorem healEpoch_le_of_healedBy3 {tL : Option ℕ} {t0 : ℕ}
    (hh : healedBy tL 3 t0 = true) : healEpoch tL ≤ t0 := by
  cases tL with
  | none => simp [healEpoch]
  | some l => simp [healedBy, healEpoch] at hh ⊢; omega

theorem healEpoch_le_of_validGuess {tL : Option ℕ} {par : Bool} {t0 : ℕ}
    (hv : validGuessBucketParAuth 1 tL par t0 = true) : healEpoch tL ≤ t0 := by
  simp only [validGuessBucketParAuth, lastLeakGuessAdmissible, Bool.and_eq_true] at hv
  exact healEpoch_le_of_healedBy3 hv.1

theorem slotOf_inj {q : ℕ} {tL : Option ℕ} {τ₁ τ₂ : ℕ}
    (h₁ : healEpoch tL ≤ τ₁) (h₂ : healEpoch tL ≤ τ₂)
    (heq : slotOf q tL τ₁ = slotOf q tL τ₂) : τ₁ = τ₂ := by
  have hmul : τ₁ - healEpoch tL = τ₂ - healEpoch tL :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) heq
  omega

theorem slotEpoch_slotOf (q : ℕ) (tL : Option ℕ) {τ : ℕ}
    (hτ : healEpoch tL ≤ τ) :
    slotEpoch (q + 1) true tL (slotOf q tL τ) = τ := by
  unfold slotEpoch slotOf
  simp only [↓reduceIte, Nat.mul_div_cancel_left _ (Nat.succ_pos q)]
  omega

theorem regSessMultiBucket_slotEpoch {T RSt K I E : Type} [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (h : FSMultiBucketAuthState T RSt K I E)
    (htH : healEpoch tL ≤ t0) (hlen : (h.sessions t0).length < L) :
    slotEpoch L gMain tL (regSessMultiBucket L gMain tL t0 ik h).1 = t0 ∧
    (gMain = false → 0 < (regSessMultiBucket L gMain tL t0 ik h).1) ∧
    (gMain = true → h.sessions t0 = [] →
      (regSessMultiBucket L gMain tL t0 ik h).1 = L * (t0 - healEpoch tL)) := by
  unfold regSessMultiBucket slotEpoch
  dsimp only
  have hdiv : ∀ pos < L, (L * (t0 - healEpoch tL) + pos) / L + healEpoch tL = t0 := by
    intro pos hpos
    have h1 : (L * (t0 - healEpoch tL) + pos) / L = t0 - healEpoch tL := by
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hpos,
        Nat.zero_add]
    omega
  by_cases hik : ik ∈ h.sessions t0
  · simp only [hik, ↓reduceIte]
    have hidx : (h.sessions t0).idxOf ik < L :=
      Nat.lt_trans (List.idxOf_lt_length_of_mem hik) hlen
    refine ⟨?_, ?_, ?_⟩
    · cases gMain <;> simpa using hdiv _ hidx
    · intro hgf; subst hgf; simp
    · intro _ hnil; simp [hnil] at hik
  · simp only [hik, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · cases gMain <;> simpa using hdiv _ hlen
    · intro hgf; subst hgf; simp
    · intro hgt hnil; subst hgt; simp [hnil]

theorem regSessMultiBucket_sessions_bound {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (h : FSMultiBucketAuthState T RSt K I E) :
    let h' := (regSessMultiBucket L gMain tL t0 ik h).2
    h'.cache = h.cache ∧ h'.book = h.book ∧
    (∀ τ, τ ≠ t0 → h'.sessions τ = h.sessions τ) ∧
    ((h'.sessions t0).length ≤ (h.sessions t0).length + 1) := by
  intro h'
  dsimp only [h', regSessMultiBucket]
  by_cases hik : ik ∈ h.sessions t0
  · simp [hik]
  · refine ⟨by simp [hik], by simp [hik], fun τ hne => ?_, by simp [hik]⟩
    simp [hik, Function.update_of_ne hne]

theorem isHonestHdr_update_cache_of_none {T RSt K I E : Type} [DecidableEq T]
    {h h' : FSMultiBucketAuthState T RSt K I E} {t0 : ℕ}
    {val : Option (T × RSt × K × Option ℕ)} {hdr : Header T}
    (hnone : h.cache t0 = none)
    (hcache : h'.cache = Function.update h.cache t0 val)
    (hhdr : isHonestHdrMultiBucket h hdr = true) :
    isHonestHdrMultiBucket h' hdr = true := by
  unfold isHonestHdrMultiBucket at hhdr ⊢
  have hne : hdr.1 ≠ t0 := by
    intro heq
    rw [heq, hnone] at hhdr
    exact nomatch hhdr
  rw [hcache, Function.update_of_ne hne]
  exact hhdr

/-! ## 2. `la = false` State Invariants & Pure Game-State Lemmas -/

@[expose] def WinSafe {Γ T RSt K I SS RS M C : Type}
    (tL : Option ℕ) (par : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (winEp : Option ℕ) : Prop :=
  ∀ tWin, winEp = some tWin →
    (!es.abort && es.g.win && authLosingConditionsAvoided 3 tL tWin es.g &&
      (decide (Party.senderOf tWin == Party.A) == par)) = false

@[expose] def SessBound {T RSt K I E : Type}
    (q : ℕ) (gMain : Bool) (rem : ℕ) (h : FSMultiBucketAuthState T RSt K I E) : Prop :=
  ∀ τ, (h.sessions τ).length + rem ≤ (if gMain then q + 1 else q)

theorem sessBound_lt {T RSt K I E : Type}
    {q m : ℕ} {gMain : Bool} {h : FSMultiBucketAuthState T RSt K I E}
    (hsb : SessBound q gMain (m + 1) h) (τ : ℕ) :
    (h.sessions τ).length < q + 1 := by
  have h1 := hsb τ
  cases gMain <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 <;> omega

theorem sessBound_mono_noop {T RSt K I E : Type}
    {q m : ℕ} {gMain : Bool} {h h' : FSMultiBucketAuthState T RSt K I E}
    (hsb : SessBound q gMain (m + 1) h) (heq : h'.sessions = h.sessions) :
    SessBound q gMain m h' := by
  intro τ
  have h1 := hsb τ
  rw [heq]
  cases gMain <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 ⊢ <;> omega

theorem sessBound_regSess {T RSt K I E : Type} [DecidableEq I]
    {q m : ℕ} {gMain : Bool} {tL : Option ℕ} {t0 : ℕ} {ik : I}
    {h : FSMultiBucketAuthState T RSt K I E}
    (hsb : SessBound q gMain (m + 1) h) :
    SessBound q gMain m (regSessMultiBucket (q + 1) gMain tL t0 ik h).2 := by
  have hb := regSessMultiBucket_sessions_bound (q + 1) gMain tL t0 ik h
  intro τ
  have h1 := hsb τ
  by_cases hτ : τ = t0
  · subst hτ
    have h2 := hb.2.2.2
    cases gMain <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 ⊢ <;> omega
  · rw [hb.2.2.1 τ hτ]
    cases gMain <;> simp only [↓reduceIte, Bool.false_eq_true] at h1 ⊢ <;> omega

theorem sessBound_regSessOpt {T RSt K I E : Type} [DecidableEq I]
    {q m : ℕ} {gMain : Bool} {tL : Option ℕ} {t0 : ℕ} {sid : Option I}
    {h : FSMultiBucketAuthState T RSt K I E}
    (hsb : SessBound q gMain (m + 1) h) :
    SessBound q gMain m (regSessOptMultiBucket (q + 1) gMain tL t0 sid h).2 := by
  cases sid with
  | none => exact sessBound_mono_noop hsb rfl
  | some ik => exact sessBound_regSess hsb

structure EngineWF {Γ T RSt SS RS M C : Type}
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)) : Prop where
  vp_id : ∀ P, (s.st P).id = P
  vp_tcur : ∀ P, (s.st P).tcur = s.epoch P
  vp_vS_some : ∀ P, P.sendsIn (s.st P).tcur = true → (s.st P).vS ≠ none
  trans_wf : ∀ r ∈ s.trans,
    r.ct.1.1 = r.pos.epoch ∧
    r.pos.sender = Party.senderOf r.pos.epoch ∧
    r.pos.epoch ≤ s.epoch r.pos.sender
  tL_eq : s.tL = s.leaks.max?

theorem EngineWF.mem_leaks_of_tL {Γ T RSt SS RS M C : Type}
    {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} (hwf : EngineWF s) {m : ℕ}
    (hm : s.tL = some m) : m ∈ s.leaks ∧ ∀ lk ∈ s.leaks, lk ≤ m := by
  rw [hwf.tL_eq, List.max?_eq_some_iff] at hm
  exact hm

theorem EngineWF.tL_some_of_mem_leaks {Γ T RSt SS RS M C : Type}
    {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} (hwf : EngineWF s) {lk : ℕ}
    (hlk : lk ∈ s.leaks) : ∃ m, s.tL = some m ∧ lk ≤ m := by
  have hne : s.leaks ≠ [] := List.ne_nil_of_mem hlk
  cases hmax : s.leaks.max? with
  | none => exact absurd (List.max?_eq_none_iff.mp hmax) hne
  | some m =>
    exact ⟨m, hwf.tL_eq.trans hmax, (List.max?_eq_some_iff.mp hmax).2 lk hlk⟩

theorem EngineWF.not_healedBy_of_mem_leaks {Γ T RSt SS RS M C : Type}
    {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} (hwf : EngineWF s)
    {cur τ : ℕ} (hcur : cur ∈ s.leaks) (hle : τ ≤ cur) :
    healedBy s.tL 3 τ = false := by
  rcases hwf.tL_some_of_mem_leaks hcur with ⟨m, hm, hcm⟩
  simp only [hm, healedBy, decide_eq_false_iff_not]
  omega

theorem EngineWF.tL_leak_eq {Γ T RSt SS RS M C : Type}
    {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} (hwf : EngineWF s) (l₀ : ℕ) :
    (s.leak l₀).tL = (s.leak l₀).leaks.max? := by
  unfold GameState.leak
  dsimp only
  symm
  apply max?_cons_of_forall_le
  intro b hb
  rcases hwf.tL_some_of_mem_leaks hb with ⟨m, hm, hbm⟩
  rw [hm]
  exact hbm.trans (le_maxOpt_left m l₀)

theorem authAvoided_false_of_leak_between {St Msg C : Type}
    {tL : Option ℕ} {tWin cur : ℕ} {s : GameState St Msg C}
    (hmem : cur ∈ s.leaks) (hlt : ltOpt tL cur = true) (hcur_lt : cur < tWin) :
    authLosingConditionsAvoided 3 tL tWin s = false := by
  unfold authLosingConditionsAvoided
  have hall : s.leaks.all (fun l => !(ltOpt tL l && decide (l < tWin))) = false := by
    rw [List.all_eq_false]
    exact ⟨cur, hmem, by simp [hlt, hcur_lt]⟩
  simp only [hall, Bool.and_false, Bool.false_and]

theorem winSafe_of_leak_between {Γ T RSt K I SS RS M C : Type}
    {tL : Option ℕ} {par : Bool}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))}
    {tWin cur : ℕ}
    (hmem : cur ∈ es.g.leaks) (hlt : ltOpt tL cur = true) (hcur_lt : cur < tWin) :
    WinSafe tL par es (some tWin) := by
  intro tw htw
  cases htw
  rw [authAvoided_false_of_leak_between hmem hlt hcur_lt]
  simp only [Bool.and_false, Bool.false_and]

theorem trivial_true_of_leak_ge_and_comp {Γ T RSt SS RS M C : Type}
    {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} (hwf : EngineWF s)
    {cur : ℕ} (hcur : cur ∈ s.leaks) {pos : Pos} (hle : pos.epoch ≤ cur)
    (hcomp : ∀ r ∈ s.trans, r.pos = pos → r.pos ∈ s.comp) :
    s.trivial 3 pos = true := by
  unfold GameState.trivial
  by_cases hex : ∃ r ∈ s.trans, r.pos = pos
  · rcases hex with ⟨r, hr, rfl⟩
    have hc : r.pos ∈ s.comp := hcomp r hr rfl
    exact Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr hc))
  · have hno : s.trans.any (fun r => r.pos == pos) = false := by
      rw [List.any_eq_false]
      intro r hr
      simp only [beq_iff_eq]
      exact fun heq => hex ⟨r, hr, heq⟩
    have hnh : healedBy s.tL 3 pos.epoch = false :=
      hwf.not_healedBy_of_mem_leaks hcur hle
    simp only [hno, hnh, Bool.not_false, Bool.true_and, Bool.or_true]

theorem healedBy_s_of_postLeak_false {St Msg C : Type}
    {tL : Option ℕ} {s : GameState St Msg C} {τ : ℕ}
    (hpl : postLeak tL s = false) (hh : healedBy tL 3 τ = true) :
    healedBy s.tL 3 τ = true := by
  unfold postLeak at hpl
  cases hstL : s.tL with
  | none => rfl
  | some cur =>
    rw [hstL] at hpl
    cases tL with
    | none => simp [ltOpt] at hpl
    | some l =>
      simp only [ltOpt, decide_eq_false_iff_not] at hpl
      simp only [healedBy, decide_eq_true_eq] at hh ⊢
      omega

theorem leak_witness_of_not_healedBy_s {Γ T RSt SS RS M C : Type}
    {tL : Option ℕ} {s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)} {τ : ℕ}
    (hwf : EngineWF s) (hnh : healedBy s.tL 3 τ = false) (hh : healedBy tL 3 τ = true) :
    ∃ cur ∈ s.leaks, ltOpt tL cur = true := by
  cases hstL : s.tL with
  | none => simp [hstL, healedBy] at hnh
  | some cur =>
    rcases hwf.mem_leaks_of_tL hstL with ⟨hmem, _⟩
    refine ⟨cur, hmem, ?_⟩
    rw [hstL] at hnh
    cases tL with
    | none => rfl
    | some l =>
      simp only [healedBy, decide_eq_false_iff_not, decide_eq_true_eq] at hnh hh
      simp only [ltOpt, decide_eq_true_eq]
      omega

structure SlotSync {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C)) : Prop where
  cache_epoch : ∀ τ, (h.cache τ).isSome = true → 1 ≤ τ ∧ τ ≤ s.epoch (Party.senderOf τ)
  cache_inr : ∀ τ Tc σc kVal sIdx, h.cache τ = some (Tc, σc, kVal, some sIdx) →
    slotEpoch (q + 1) gMain tL sIdx = τ ∧
    validGuessBucketParAuth 1 tL par τ = true ∧ τ ≤ qep + 1
  vS_inr : ∀ P sIdx, (s.st P).vS = some (.inr sIdx) →
    let τ := slotEpoch (q + 1) gMain tL sIdx
    τ ≤ (s.st P).tcur ∧
    validGuessBucketParAuth 1 tL par τ = true ∧ τ ≤ qep + 1 ∧
    (gMain = false → 1 ≤ τ) ∧
    (P.sendsIn (s.st P).tcur = true →
      τ = (s.st P).tcur ∧
      ((s.st P).tcur = 0 ∨ isHonestHdrMultiBucket h ((s.st P).tcur, (s.st P).curCkaMsg) = true)) ∧
    (gMain = true →
      τ = 0 ∨ ∃ Tc σc kVal, h.cache τ = some (Tc, σc, kVal, some sIdx))
  vR_inr : ∀ P τ sIdx, (s.st P).vR τ = some (.inr sIdx) →
    slotEpoch (q + 1) gMain tL sIdx = τ ∧
    validGuessBucketParAuth 1 tL par τ = true ∧ τ ≤ qep + 1 ∧
    P = Party.receiverOf τ ∧
    (gMain = true →
      τ = 0 ∨ ∃ Tc σc kVal, h.cache τ = some (Tc, σc, kVal, some sIdx))

structure ForgedInv {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    (q : ℕ) (tL : Option ℕ)
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C))
    (sc : ℕ → Option ℕ) : Prop where
  hdr_honest : ∀ sIdx x, x ∈ ((h.book sIdx).getD {}).fsTrans →
    isHonestHdrMultiBucket h x.2.1 = true
  sc_not_healed : ∀ sIdx, sc sIdx ≠ none →
    healedBy s.tL 3 (slotEpoch (q + 1) false tL sIdx) = false

structure MainInv {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C))
    (ns : ℕ → ℕ) (sc : ℕ → Option ℕ) : Prop where
  fresh_above : ∀ τ, 1 ≤ τ → healEpoch tL ≤ τ → s.epoch (Party.senderOf τ) < τ →
    ns (slotOf q tL τ) = 0 ∧ sc (slotOf q tL τ) = none ∧
    h.book (slotOf q tL τ) = none ∧ h.sessions τ = []
  vR0_init : validGuessBucketParAuth 1 tL par 0 = true → (s.st .A).vR 0 = some (.inr 0)
  vS0_init : s.epoch .B = 0 → validGuessBucketParAuth 1 tL par 0 = true →
    (s.st .B).vS = some (.inr 0)
  vS_inl_cache : ∀ P ss, 1 ≤ (s.st P).tcur → P.sendsIn (s.st P).tcur = true →
    (s.st P).vS = some (.inl ss) → ∃ Tc σc kVal, h.cache (s.st P).tcur = some (Tc, σc, kVal, none)
  vR_none_of_cache_none : ∀ P τ, 1 ≤ τ → h.cache τ = none → (s.st P).vR τ = none
  slot_canon :
    (∀ P sIdx, (s.st P).vS = some (.inr sIdx) →
      sIdx = slotOf q tL (slotEpoch (q + 1) true tL sIdx)) ∧
    (∀ τ Tc σc kVal sIdx, h.cache τ = some (Tc, σc, kVal, some sIdx) →
      sIdx = slotOf q tL τ) ∧
    (∀ P τ sIdx, (s.st P).vR τ = some (.inr sIdx) → sIdx = slotOf q tL τ) ∧
    (∀ sIdx, h.book sIdx ≠ none →
      let τ := slotEpoch (q + 1) true tL sIdx
      sIdx = slotOf q tL τ ∧ validGuessBucketParAuth 1 tL par τ = true ∧ τ ≤ qep + 1 ∧
      (τ = 0 ∨ ∃ Tc σc kVal, h.cache τ = some (Tc, σc, kVal, some sIdx))) ∧
    (∀ τ Tc σc kVal sIdx rs, h.cache τ = some (Tc, σc, kVal, some sIdx) →
      (s.st (Party.receiverOf τ)).vR τ ≠ some (.inl rs))
  idx_sync : ∀ P sIdx, (s.st P).vS = some (.inr sIdx) → P.sendsIn (s.st P).tcur = true →
    s.idx P = ns sIdx ∧ ((h.book sIdx).getD {}).fsCount = ns sIdx
  trans_idx : ∀ r ∈ s.trans,
    validGuessBucketParAuth 1 tL par r.pos.epoch = true → r.pos.epoch ≤ qep + 1 →
    (r.pos.epoch = 0 ∨
      ∃ Tc σc kVal, h.cache r.pos.epoch = some (Tc, σc, kVal, some (slotOf q tL r.pos.epoch))) →
    r.pos.idx ≤ ns (slotOf q tL r.pos.epoch) ∧ r.ct.2.1 = r.pos.idx
  fsTrans_sub : ∀ sIdx x, x ∈ ((h.book sIdx).getD {}).fsTrans →
    h.book sIdx ≠ none ∧
    ∃ r ∈ s.trans,
      r.pos = ⟨Party.senderOf (slotEpoch (q + 1) true tL sIdx),
               slotEpoch (q + 1) true tL sIdx, x.1⟩ ∧
      r.ct = x.2 ∧ x.2.2.1 = x.1
  inl_comp : ∀ τ, τ ≤ qep + 1 → validGuessBucketParAuth 1 tL par τ = true →
    ((∃ Tc σc kVal, h.cache τ = some (Tc, σc, kVal, none)) ∨
     (∃ rs, (s.st (Party.receiverOf τ)).vR τ = some (.inl rs))) →
    ∃ cur ∈ s.leaks, ltOpt tL cur = true ∧
      (cur < τ ∨ (τ ≤ cur ∧ ∀ r ∈ s.trans, r.pos.epoch = τ → r.pos ∈ s.comp))
  sc_comp : ∀ sIdx c, sc sIdx = some c →
    let τ := slotEpoch (q + 1) true tL sIdx
    sIdx = slotOf q tL τ ∧ validGuessBucketParAuth 1 tL par τ = true ∧ τ ≤ qep + 1 ∧
    ∃ cur ∈ s.leaks, ltOpt tL cur = true ∧
      (cur < τ ∨ (τ ≤ cur ∧ ∀ r ∈ s.trans, r.pos.epoch = τ → c < r.pos.idx → r.pos ∈ s.comp))

structure ActiveInv {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    (q qep rem : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (winEp : Option ℕ) (ns : ℕ → ℕ) (sc : ℕ → Option ℕ) : Prop where
  no_abort : es.abort = false
  no_win : es.g.win = false
  winEp_none : winEp = none
  sess : SessBound q gMain rem es.h
  wf : EngineWF es.g
  sync : SlotSync q qep gMain tL par es.g es.h
  forged : gMain = false → ForgedInv q tL es.g es.h sc
  main : gMain = true → MainInv q qep tL par es.g es.h ns sc

@[expose] def FalseInv {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    (q qep rem : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I)
    (ns : ℕ → ℕ) (sc : ℕ → Option ℕ) : Prop :=
  ((st.1.abort = true ∨ st.1.g.win = true) ∧ WinSafe tL par st.1 st.2) ∨
  ActiveInv q qep rem gMain tL par st.1 st.2 ns sc

theorem FalseInv.to_winSafe {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I}
    {ns : ℕ → ℕ} {sc : ℕ → Option ℕ}
    (hinv : FalseInv q qep rem gMain tL par st ns sc) :
    WinSafe tL par st.1 st.2 := by
  rcases hinv with ⟨_, hws⟩ | hact
  · exact hws
  · intro tWin htw; rw [hact.winEp_none] at htw; exact nomatch htw

/-! ## 3. Monadic Coin/Lookup/Root/Lazy-CS/Frozen/Init Hoare Lemmas -/

private def liftProbT {ι : Type} {tspec : OracleSpec.{0, 0} ι} {α : Type} (mx : ProbComp α) :
    TComp tspec α :=
  (liftM mx : TComp tspec α)

private theorem liftM_probComp_hoare {SS RS T M C α : Type}
    (S : FSFalseSemantics SS RS T M C) (mx : ProbComp α)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    S.H Pre (fun _ ns sc => Pre ns sc)
      (liftProbT (tspec := FSMultiSpec SS RS T M (ℕ × C)) mx) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    change S.H Pre (fun _ ns sc => Pre ns sc) (Pure.pure a)
    exact S.pure (Post := fun _ ns sc => Pre ns sc) a fun _ _ hp => hp
  | query_bind t0 r ih =>
    change S.H Pre _ (simulateQ _ (liftM (query t0) >>= r))
    simp only [simulateQ_bind, simulateQ_query]
    exact S.bind (S.coin t0) ih

theorem stateT_lift_sampleT_hoare {SS RS T M C St α : Type} [SampleableType α]
    (S : FSFalseSemantics SS RS T M C) (st : St)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    S.H Pre (fun (p : α × St) ns sc => p.2 = st ∧ Pre ns sc)
      ((StateT.lift (sampleT α)).run st) := by
  rw [StateT.run_lift]
  exact S.bind (liftM_probComp_hoare S ($ᵗ α)) fun a =>
    S.pure (a, st) fun _ _ hp => ⟨rfl, hp⟩

theorem liftH_false_hoare {SS RS T M C Γ RSt SS' RS' M' E' HS α : Type}
    (S : FSFalseSemantics SS RS T M C)
    (es : EState (VP Γ T RSt SS' RS') M' (Header T × E') HS)
    (x : StateT HS (OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C))) α)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    {Post : α × HS → (ℕ → ℕ) → (ℕ → Option ℕ) → Prop}
    (hx : S.H Pre Post (x.run es.h)) :
    S.H Pre (fun (p : α × EState (VP Γ T RSt SS' RS') M' (Header T × E') HS) ns sc =>
      ∃ h', p.2 = { es with h := h' } ∧ Post (p.1, h') ns sc)
      ((liftH x).run es) := by
  change S.H Pre _ (x.run es.h >>= fun r => Pure.pure (r.1, { es with h := r.2 }))
  exact S.bind hx fun ⟨a, h'⟩ =>
    S.pure (a, { es with h := h' }) fun _ _ hp => ⟨h', rfl, hp⟩

theorem lazy_cs_hoare {SS RS T M C RSt K I : Type}
    (S : FSFalseSemantics SS RS T M C) (cond : Bool) (sIdx : ℕ)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    S.H Pre
      (fun (p : Bool × FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        ∃ sc, Pre ns' sc ∧
          p.2.cache = h.cache ∧ p.2.sessions = h.sessions ∧
          (∀ idx, ((p.2.book idx).getD {}).fsCount = ((h.book idx).getD {}).fsCount) ∧
          (∀ idx, ((p.2.book idx).getD {}).fsTrans = ((h.book idx).getD {}).fsTrans) ∧
          (∀ idx, idx ≠ sIdx → p.2.book idx = h.book idx) ∧
          (cond = false → p.1 = true ∧ p.2 = h ∧ sc' = sc) ∧
          (p.1 = false → sc' = sc) ∧
          (p.1 = true → cond = true →
            sc' = Function.update sc sIdx (some ((sc sIdx).getD (ns' sIdx))) ∧
            p.2.book sIdx ≠ none))
      ((if cond then do
          match ← liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
              (SenderState := SS) (ReceiverState := RS) (AssocData := Header T) (Message := M)
              (Ciphertext := ℕ × C)) with
          | none => Pure.pure false
          | some _ =>
            modify fun (s : FSMultiBucketAuthState T RSt K I (ℕ × C)) =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            Pure.pure true
        else Pure.pure true).run h) := by
  cases cond with
  | false =>
    exact S.pure (true, h) fun ns sc hp =>
      ⟨sc, hp, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
        fun _ => ⟨rfl, rfl, rfl⟩, fun h => (nomatch h), fun _ h => (nomatch h)⟩
  | true =>
    simp only [↓reduceIte, StateT.run_bind]
    refine S.bind (S.cs sIdx h) fun ⟨csRes, h1⟩ => ?_
    cases csRes with
    | none =>
      exact S.pure (false, h1) fun ns' sc' ⟨hh1, ns, sc, hp, hns, hbr⟩ => by
        subst hh1; subst hns
        rcases hbr with ⟨_, rfl⟩ | ⟨_, h, _⟩
        · exact ⟨sc', hp, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
            fun h => (nomatch h), fun _ => rfl, fun h => (nomatch h)⟩
        · exact nomatch h
    | some w =>
      refine S.pure _ fun ns' sc' ⟨hh1, ns, sc, hp, hns, hbr⟩ => ?_
      subst hh1; subst hns
      rcases hbr with ⟨h, _⟩ | ⟨_, _, hsc'⟩
      · exact nomatch h
      · refine ⟨sc, hp, rfl, rfl, ?_, ?_, ?_, fun h => (nomatch h), fun h => (nomatch h),
          fun _ _ => ⟨hsc', by simp⟩⟩
        · intro idx
          by_cases hidx : idx = sIdx
          · subst hidx; simp
          · simp [Function.update_of_ne hidx]
        · intro idx
          by_cases hidx : idx = sIdx
          · subst hidx; simp
          · simp [Function.update_of_ne hidx]
        · intro idx hidx; exact Function.update_of_ne hidx _ _

theorem implFSMultiBucketAuth_step_frozen
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (L : ℕ) (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (t : (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
      (Header T × (ℕ × C))).Domain)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I)
    (habw : st.1.abort = true ∨ st.1.g.win = true)
    (hws : WinSafe tL par st.1 st.2)
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    let hk := hooksFSMultiBucketAuth L cka prng fs 1 qep gMain tL par false
    S.H Pre
      (fun p ns sc =>
        ((p.2.1.abort = true ∨ p.2.1.g.win = true) ∧ WinSafe tL par p.2.1 p.2.2) ∧ Pre ns sc)
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL t).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  dsimp only at habw hws
  have hor : (es0.abort || es0.g.win) = true := by
    rcases habw with h | h <;> simp [h]
  rcases t with u | ((((⟨P, m, r⟩ | _) | x) | x) | P)
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    rw [StateT.run_lift]
    exact S.bind (S.coin u) fun _ => S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte, StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    simp only [StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    rcases x with ⟨P, c⟩
    have hdel : (deliverE hk maxSkip (bucketAuthCfg 1 tL) (P, c)).run es0 = Pure.pure (none, es0) := by
      unfold deliverE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hor, ↓reduceIte, StateT.run_pure]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hdel, StateT.run_lift,
      StateT.run_set, StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    rcases x with ⟨P, c⟩
    have hinj : (es0.abort || es0.g.win || (es0.g.inTransit P.other c).isSome ||
        !(es0.g.safeInj 3)) = true := by
      rcases habw with h | h <;> simp [h]
    have hinj0 : (injectE hk (2 + 1) qep (bucketAuthCfg 1 tL) (P, c)).run es0 = Pure.pure (none, es0) := by
      unfold injectE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hinj, ↓reduceIte, StateT.run_pure]
    have hwin' : (!es0.g.win && es0.g.win &&
        (gMain || (decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrMultiBucket es0.h c.1))) = false := by
      cases es0.g.win <;> rfl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hinj0, StateT.run_lift,
      hwin', Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩
  · dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
    have hcorr : (es0.abort || es0.g.win || !(es0.g.corrAllowed P)) = true := by
      rcases habw with h | h <;> simp [h]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hcorr, ↓reduceIte, StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨⟨habw, hws⟩, hp⟩

theorem lookupMultiBucketF_false_hoare {SS RS T M C RSt K I : Type}
    [DecidableEq I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (t0 : ℕ) (ik : I)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    S.H Pre
      (fun (p : K × FSMultiBucketAuthState T RSt K I (ℕ × C)) ns sc =>
        p.2.cache = h.cache ∧ p.2.sessions = h.sessions ∧ p.2.book = h.book ∧ Pre ns sc)
      ((lookupMultiBucketF (SS := SS) (RS := RS) (T := T) (M := M) (E := ℕ × C) t0 ik).run h) := by
  unfold lookupMultiBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some k =>
    simp only [StateT.run_pure]
    exact S.pure _ fun _ _ hp => ⟨rfl, rfl, rfl, hp⟩
  | none =>
    simp only [StateT.run_bind]
    refine S.bind (stateT_lift_sampleT_hoare S h) fun ⟨k, h1⟩ => ?_
    simp only [StateT.run_modify, pure_bind, StateT.run_pure]
    exact S.pure _ fun _ _ ⟨hh1, hp⟩ => by subst hh1; exact ⟨rfl, rfl, rfl, hp⟩

theorem rootFSMultiBucketAuth_false_hoare {SS RS T M C KR RSt I K : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C)
    (prng : PRFPRNG KR RSt I K) (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl0 : Bool) (ik0 : I) (σ0 : RSt)
    (h : FSMultiBucketAuthState T RSt K I (ℕ × C))
    {Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop} :
    S.H Pre
      (fun (p : (RSt × K × Option I) × FSMultiBucketAuthState T RSt K I (ℕ × C)) ns sc =>
        p.2.cache = h.cache ∧ p.2.sessions = h.sessions ∧ p.2.book = h.book ∧ Pre ns sc ∧
        (p.1.2.2.isSome = true ↔
          (pl0 = false ∧ t0 ≤ qep + 1 ∧ validGuessBucketParAuth 1 tL par t0 = true)))
      ((rootFSMultiBucketAuth (SS := SS) (RS := RS) (T := T) (M := M) (E := ℕ × C)
        prng 1 qep tL par t0 pl0 ik0 σ0).run h) := by
  unfold rootFSMultiBucketAuth; dsimp only
  by_cases hc1 : (pl0 || decide (qep + 1 < t0)) = true
  · simp only [hc1, ↓reduceIte, StateT.run_pure]
    refine S.pure _ fun _ _ hp => ⟨rfl, rfl, rfl, hp, ?_⟩
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro ⟨hpl, hle, _⟩
    simp [hpl, Nat.not_lt.mpr hle] at hc1
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    have hpl0 : pl0 = false := by cases pl0 <;> simp_all
    have hle0 : t0 ≤ qep + 1 := by
      rw [hpl0, Bool.false_or] at hc1; simp at hc1; exact hc1
    by_cases hv : validGuessBucketParAuth 1 tL par t0 = true
    · simp only [hv, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind]
        refine S.bind (stateT_lift_sampleT_hoare S h) fun ⟨ir, h1⟩ => ?_
        refine S.bind (stateT_lift_sampleT_hoare S h1) fun ⟨kS, h2⟩ => ?_
        simp only [StateT.run_pure]
        refine S.pure _ fun _ _ ⟨hh2, hh1, hp⟩ => ?_
        subst hh2; subst hh1
        exact ⟨rfl, rfl, rfl, hp, by simp [hpl0, hle0]⟩
      · simp only [StateT.run_bind]
        refine S.bind (lookupMultiBucketF_false_hoare S t0 ik0 h) fun ⟨kL, h1⟩ => ?_
        simp only [StateT.run_pure]
        refine S.pure _ fun _ _ ⟨hc, hs, hb, hp⟩ =>
          ⟨hc, hs, hb, hp, by simp [hpl0, hle0]⟩
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · simp only [StateT.run_bind]
        refine S.bind (stateT_lift_sampleT_hoare S h) fun ⟨ir, h1⟩ => ?_
        refine S.bind (stateT_lift_sampleT_hoare S h1) fun ⟨kS, h2⟩ => ?_
        simp only [StateT.run_pure]
        refine S.pure _ fun _ _ ⟨hh2, hh1, hp⟩ => ?_
        subst hh2; subst hh1
        exact ⟨rfl, rfl, rfl, hp, by simp⟩
      · simp only [StateT.run_bind]
        refine S.bind (lookupMultiBucketF_false_hoare S t0 ik0 h) fun ⟨kL, h1⟩ => ?_
        simp only [StateT.run_pure]
        exact S.pure _ fun _ _ ⟨hc, hs, hb, hp⟩ => ⟨hc, hs, hb, hp, by simp⟩
      · simp only [StateT.run_pure]
        exact S.pure _ fun _ _ hp => ⟨rfl, rfl, rfl, hp, by simp⟩

theorem initFSMultiBucketAuth_false_hoare {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C)
    (q qep : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (lam : I) (gMain : Bool) (tL : Option ℕ) (par : Bool) :
    S.H (fun ns sc => (∀ i, ns i = 0) ∧ (∀ i, sc i = none))
      (fun (p : (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) ×
                FSMultiBucketAuthState T RSt K I (ℕ × C)) ns sc =>
        let g0 : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C) :=
          { st := fun P => match P with | .A => p.1.1 | .B => p.1.2, b := false }
        ActiveInv q qep q gMain tL par { g := g0, h := p.2, abort := false } none ns sc)
      ((initFSMultiBucketAuth (q + 1) cka prng fs lam 1 qep gMain tL par).run
        ({} : FSMultiBucketAuthState T RSt K I (ℕ × C))) := by
  unfold initFSMultiBucketAuth
  simp only [StateT.run_bind]
  refine S.bind (stateT_lift_sampleT_hoare S ({} : FSMultiBucketAuthState T RSt K I (ℕ × C)))
    fun ⟨kr, h1⟩ => ?_
  refine S.bind (stateT_lift_sampleT_hoare S h1) fun ⟨kc, h2⟩ => ?_
  refine S.bind (rootFSMultiBucketAuth_false_hoare S prng qep tL par 0 false lam (prng.init kr) h2)
    fun ⟨⟨σ, kVal, sid⟩, h3⟩ => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  refine S.pure _ fun ns sc ⟨hc3, hs3, hb3, ⟨hh2, hh1, hns0, hsc0⟩, hsid⟩ => ?_
  subst hh2; subst hh1
  dsimp only
  cases gMain with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun h => (nomatch h)⟩
    · intro τ; rw [hs3]; simp
    · refine ⟨fun P => by cases P <;> rfl, fun P => by cases P <;> rfl,
        fun P h => by cases P <;> simp [mkParties, Party.sendsIn] at h ⊢,
        fun _ hr => (nomatch hr), rfl⟩
    · refine ⟨fun τ h => by rw [hc3] at h; exact (nomatch h),
        fun τ _ _ _ _ h => by rw [hc3] at h; exact (nomatch h),
        fun P _ h => by cases P <;> simp [mkParties] at h,
        fun P τ _ h => by cases P <;> simp [mkParties] at h⟩
    · intro _; refine ⟨fun sIdx x hx => ?_, fun sIdx hsc => absurd (hsc0 sIdx) hsc⟩
      rw [hb3] at hx; exact nomatch hx
  | true =>
    simp only [↓reduceIte]
    cases sid with
    | none =>
      simp only [regSessOptMultiBucket]
      have hnv : validGuessBucketParAuth 1 tL par 0 = false := by
        cases hv : validGuessBucketParAuth 1 tL par 0 with
        | false => rfl
        | true => simp [hv] at hsid
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, fun h => (nomatch h), ?_⟩
      · intro τ; rw [hs3]; simp
      · refine ⟨fun P => by cases P <;> rfl, fun P => by cases P <;> rfl,
          fun P h => by cases P <;> simp [mkParties, Party.sendsIn] at h ⊢,
          fun _ hr => (nomatch hr), rfl⟩
      · refine ⟨fun τ h => by rw [hc3] at h; exact (nomatch h),
          fun τ _ _ _ _ h => by rw [hc3] at h; exact (nomatch h),
          fun P _ h => by cases P <;> simp [mkParties] at h,
          fun P τ _ h => by cases P <;> simp [mkParties] at h⟩
      · intro _
        refine ⟨fun τ _ _ _ => ⟨hns0 _, hsc0 _, by rw [hb3], by rw [hs3]⟩,
          fun hv => by rw [hnv] at hv; exact (nomatch hv),
          fun _ hv => by rw [hnv] at hv; exact (nomatch hv),
          fun P _ h1 _ _ => by cases P <;> simp [mkParties] at h1,
          fun P τ h1 _ => by cases P <;> simp [mkParties, Nat.ne_of_gt h1],
          ⟨fun P _ h => by cases P <;> simp [mkParties] at h,
           fun τ _ _ _ _ h => by rw [hc3] at h; exact (nomatch h),
           fun P τ _ h => by cases P <;> simp [mkParties] at h,
           fun sIdx hb => by rw [hb3] at hb; exact absurd rfl hb,
           fun τ _ _ _ _ _ h => by rw [hc3] at h; exact (nomatch h)⟩,
          fun P _ h => by cases P <;> simp [mkParties] at h,
          fun _ hr => (nomatch hr),
          fun sIdx x hx => by rw [hb3] at hx; exact (nomatch hx),
          fun τ _ hv hinl => ?_,
          fun sIdx _ hsc => by simp [hsc0 sIdx] at hsc⟩
        rcases hinl with ⟨_, _, _, hc⟩ | ⟨rs, hvr⟩
        · rw [hc3] at hc; exact nomatch hc
        · cases τ with
          | zero => rw [hnv] at hv; exact nomatch hv
          | succ n =>
            cases hrec : Party.receiverOf (n + 1) <;>
              simp [hrec, mkParties] at hvr
    | some ik =>
      have hv0 : validGuessBucketParAuth 1 tL par 0 = true :=
        (hsid.mp rfl).2.2
      have htH0 : healEpoch tL = 0 := Nat.eq_zero_of_le_zero (healEpoch_le_of_validGuess hv0)
      have hlen0 : (h3.sessions 0).length < q + 1 := by rw [hs3]; exact Nat.succ_pos q
      have hnil0 : h3.sessions 0 = [] := by rw [hs3]
      have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) true tL 0 ik h3
        (by omega) hlen0
      have hidx0 : (regSessMultiBucket (q + 1) true tL 0 ik h3).1 = 0 := by
        rw [hreg.2.2 rfl hnil0]; simp
      have hbnd := regSessMultiBucket_sessions_bound (q + 1) true tL 0 ik h3
      simp only [regSessOptMultiBucket, hidx0]
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, fun h => (nomatch h), ?_⟩
      · intro τ
        by_cases hτ : τ = 0
        · subst hτ; have := hbnd.2.2.2; rw [hnil0] at this; simp at this ⊢; omega
        · rw [hbnd.2.2.1 τ hτ, hs3]; simp
      · refine ⟨fun P => by cases P <;> rfl, fun P => by cases P <;> rfl,
          fun P h => by cases P <;> simp [mkParties, Party.sendsIn] at h ⊢,
          fun _ hr => (nomatch hr), rfl⟩
      · refine ⟨fun τ h => by rw [hbnd.1, hc3] at h; exact (nomatch h),
          fun τ _ _ _ _ h => by rw [hbnd.1, hc3] at h; exact (nomatch h),
          fun P sIdx h => ?_,
          fun P τ sIdx h => ?_⟩
        · cases P <;> simp [mkParties] at h
          subst h
          have hep0 : slotEpoch (q + 1) true tL 0 = 0 := by simp [slotEpoch, htH0]
          exact ⟨by simp [mkParties, hep0], by simpa [hep0] using hv0,
            by simp [hep0], fun h => (nomatch h),
            fun _ => ⟨by simp [mkParties, hep0], Or.inl rfl⟩, fun _ => Or.inl hep0⟩
        · cases P <;> simp [mkParties] at h
          rcases h with ⟨rfl, rfl⟩
          have hep0 : slotEpoch (q + 1) true tL 0 = 0 := by simp [slotEpoch, htH0]
          exact ⟨hep0, hv0, Nat.zero_le _, rfl, fun _ => Or.inl rfl⟩
      · intro _
        have hep0 : slotEpoch (q + 1) true tL 0 = 0 := by simp [slotEpoch, htH0]
        have hsl0 : slotOf q tL 0 = 0 := by simp [slotOf, htH0]
        refine ⟨fun τ h1 _ _ => ⟨hns0 _, hsc0 _, by rw [hbnd.2.1, hb3], ?_⟩,
          fun _ => by simp [mkParties],
          fun _ _ => by simp [mkParties],
          fun P _ h1 _ _ => by cases P <;> simp [mkParties] at h1,
          fun P τ h1 _ => by cases P <;> simp [mkParties, Nat.ne_of_gt h1],
          ⟨fun P sIdx h => ?_,
           fun τ _ _ _ _ h => by rw [hbnd.1, hc3] at h; exact (nomatch h),
           fun P τ sIdx h => ?_,
           fun sIdx hb => by rw [hbnd.2.1, hb3] at hb; exact absurd rfl hb,
           fun τ _ _ _ _ _ h => by rw [hbnd.1, hc3] at h; exact (nomatch h)⟩,
          fun P sIdx h _ => ?_,
          fun _ hr => (nomatch hr),
          fun sIdx x hx => by rw [hbnd.2.1, hb3] at hx; exact (nomatch hx),
          fun τ _ _ hinl => ?_,
          fun sIdx _ hsc => by simp [hsc0 sIdx] at hsc⟩
        · rw [hbnd.2.2.1 τ (by omega), hs3]
        · cases P <;> simp [mkParties] at h; subst h; simp [hep0, hsl0]
        · cases P <;> simp [mkParties] at h; rcases h with ⟨rfl, rfl⟩; simp [hsl0]
        · cases P <;> simp [mkParties] at h; subst h
          exact ⟨(hns0 0).symm, by rw [hbnd.2.1, hb3]; simp [hns0 0]⟩
        · rcases hinl with ⟨_, _, _, hc⟩ | ⟨rs, hvr⟩
          · rw [hbnd.1, hc3] at hc; exact nomatch hc
          · cases τ with
            | zero => simp [Party.receiverOf, Party.senderOf, mkParties] at hvr
            | succ n =>
              cases hrec : Party.receiverOf (n + 1) <;>
                simp [hrec, mkParties] at hvr

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase
