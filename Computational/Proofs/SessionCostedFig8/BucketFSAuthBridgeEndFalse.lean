/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseSend
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecv
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Shallow `la = false` Ideal-Cutoff Hoare Proof for `redFSAuthMultiBucket`

Assembles the active `Reveal` (`i₅`) step, the full `implFSMultiBucketAuth` query-step dispatch,
bounded-query simulation induction, and `redFSAuthMultiBucket_false_hoare` (`Δcka = 1`,
`L = q + 1`) under `FSFalseSemantics`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalse

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (GameState ltOpt healedBy maxOpt
  lastLeakGuessAdmissible MakesAtMostQueries)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header healEpoch FSMultiSpec)
open _root_.CryptoGames.SM.Engine (VP Ctx EState)
open _root_.CryptoGames.SM.Thm1L17 (le_maxOpt_right not_healedBy_leak)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState FSMultiBucketAuthEState liftFSMultiBucket
  validGuessBucketParAuth hooksFSMultiBucketAuth implFSMultiBucketAuth redFSAuthMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase (
  FSFalseSemantics slotEpoch slotOf healEpoch_le_of_validGuess slotOf_inj
  WinSafe sessBound_mono_noop ActiveInv FalseInv
  implFSMultiBucketAuth_step_frozen initFSMultiBucketAuth_false_hoare)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseSend (i1_send_active_hoare)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecv (
  i3_deliver_active_hoare i4_inject_active_hoare)

/-! ## 1. Active `Reveal` (`i₅`) Step Proof -/

private theorem winSafe_abort_none {Γ T RSt K I SS RS M C : Type}
    {tL : Option ℕ} {par : Bool}
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))) :
    WinSafe tL par es none :=
  fun _ h => nomatch h

private theorem afterCorr_preserves_uncorrupted {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool} {P : Party}
    {es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))}
    {ns : ℕ → ℕ} {sc : ℕ → Option ℕ}
    (hact : ActiveInv q qep (rem + 1) gMain tL par es0 none ns sc) :
    ActiveInv q qep rem gMain tL par
      { es0 with g := es0.g.afterCorr P, h := es0.h } none ns sc := by
  let s := es0.g
  have hcomp_sub : ∀ p ∈ s.comp, p ∈ (s.afterCorr P).comp := by
    intro p hp; simp [GameState.afterCorr, GameState.leak, hp]
  have hleaks_sub : ∀ lk ∈ s.leaks, lk ∈ (s.afterCorr P).leaks := by
    intro lk hlk; simp [GameState.afterCorr, GameState.leak, hlk]
  refine ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl, ?_,
    ⟨hact.sync.cache_epoch, hact.sync.cache_inr, hact.sync.vS_inr, hact.sync.vR_inr⟩, ?_, ?_⟩
  · refine ⟨hact.wf.vp_id, hact.wf.vp_tcur, hact.wf.vp_vS_some, hact.wf.trans_wf, ?_⟩
    exact hact.wf.tL_leak_eq (max (s.epoch .A) (s.epoch .B))
  · intro hgf
    have hf := hact.forged hgf
    exact ⟨hf.hdr_honest, fun sIdx hsc => not_healedBy_leak (hf.sc_not_healed sIdx hsc)⟩
  · intro hgt
    have hm := hact.main hgt
    refine ⟨hm.fresh_above, hm.vR0_init, hm.vS0_init, hm.vS_inl_cache,
      hm.vR_none_of_cache_none, hm.slot_canon, hm.idx_sync, hm.trans_idx, hm.fsTrans_sub, ?_, ?_⟩
    · intro τ hle hv hinl
      rcases hm.inl_comp τ hle hv hinl with ⟨cur, hcur, hlt, hbr⟩
      refine ⟨cur, hleaks_sub cur hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq => hcomp_sub _ (hc r hr heq)⟩
    · intro sIdx c hsc
      rcases hm.sc_comp sIdx c hsc with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
      refine ⟨hsl, hv, hle, cur, hleaks_sub cur hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq hci => hcomp_sub _ (hc r hr heq hci)⟩

private theorem hooks_reveal_active_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool) (P : Party)
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (winEp0 : Option ℕ) :
    S.H (ActiveInv q qep (rem + 1) gMain tL par es0 winEp0)
      (fun (p : Option (PartyState Γ T RSt SS RS) × FSMultiBucketAuthState T RSt K I (ℕ × C))
          ns' sc' =>
        winEp0 = none ∧
        (p.1 = none ∨
         ActiveInv q qep rem gMain tL par { es0 with g := es0.g.afterCorr P, h := p.2 }
           none ns' sc'))
      (((hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false).reveal
        es0.g P (es0.g.st P)).run es0.h) := by
  unfold hooksFSMultiBucketAuth; dsimp only
  by_cases hg1 : (!gMain && (!(decide ((es0.g.st P).tcur < healEpoch tL)) ||
      !(decide (max (es0.g.epoch Party.A) (es0.g.epoch Party.B) < healEpoch tL)))) = true
  · simp only [hg1, ↓reduceIte, StateT.run_pure]
    exact S.pure _ fun _ _ hact => ⟨hact.winEp_none, Or.inl rfl⟩
  · simp only [hg1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    cases hvS : (es0.g.st P).vS with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      split_ifs <;> simp only [StateT.run_pure]
      · exact S.pure _ fun _ _ hact => ⟨hact.winEp_none, Or.inl rfl⟩
      · refine S.pure _ fun _ _ hact => ?_
        have hwe := hact.winEp_none; subst hwe
        exact ⟨rfl, Or.inr (afterCorr_preserves_uncorrupted hact)⟩
    | some vS =>
      cases vS with
      | inl _ =>
        simp only [StateT.run_pure, pure_bind]
        split_ifs <;> simp only [StateT.run_pure]
        · exact S.pure _ fun _ _ hact => ⟨hact.winEp_none, Or.inl rfl⟩
        · refine S.pure _ fun _ _ hact => ?_
          have hwe := hact.winEp_none; subst hwe
          exact ⟨rfl, Or.inr (afterCorr_preserves_uncorrupted hact)⟩
      | inr sIdx =>
        simp only [StateT.run_bind, bind_assoc]
        refine S.bind (S.cs sIdx es0.h) fun ⟨csRes, h1⟩ => ?_
        cases csRes with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact S.pure _ fun _ _ ⟨_, _, _, hact, _, _⟩ => ⟨hact.winEp_none, Or.inl rfl⟩
        | some _ =>
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
          split_ifs <;> simp only [StateT.run_pure]
          · exact S.pure _ fun _ _ ⟨_, _, _, hact, _, _⟩ => ⟨hact.winEp_none, Or.inl rfl⟩
          · refine S.pure _ fun ns' sc' ⟨hh1, ns, sc, hact, hns, hbr⟩ => ?_
            subst hh1; subst hns
            rcases hbr with ⟨h, _⟩ | ⟨_, _, hsc'⟩
            · exact nomatch h
            have hwe := hact.winEp_none; subst hwe
            have hgMain : gMain = true := by
              cases hgm : gMain with
              | true => rfl
              | false =>
                subst hgm
                have hvSr := hact.sync.vS_inr P sIdx hvS
                have htH := healEpoch_le_of_validGuess hvSr.2.1
                simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true',
                  decide_eq_false_iff_not, not_or, not_not] at hg1
                omega
            subst hgMain
            let s := es0.g
            let b0 := (es0.h.book sIdx).getD {}
            let b1 := { b0 with sCorr := true }
            let h' : FSMultiBucketAuthState T RSt K I (ℕ × C) :=
              { es0.h with book := Function.update es0.h.book sIdx (some b1) }
            have hbase := afterCorr_preserves_uncorrupted hact (P := P)
            have hm := hact.main rfl
            have hvSr := hact.sync.vS_inr P sIdx hvS
            let τ₀ := slotEpoch (q + 1) true tL sIdx
            have hsl₀ : sIdx = slotOf q tL τ₀ := hm.slot_canon.1 P sIdx hvS
            have htH₀ : healEpoch tL ≤ τ₀ := healEpoch_le_of_validGuess hvSr.2.1
            have hcnt : ∀ idx, ((h'.book idx).getD {}).fsCount = ((es0.h.book idx).getD {}).fsCount := by
              intro idx; by_cases hi : idx = sIdx <;> simp [h', b1, b0, hi, Function.update_of_ne]
            have hftr : ∀ idx, ((h'.book idx).getD {}).fsTrans = ((es0.h.book idx).getD {}).fsTrans := by
              intro idx; by_cases hi : idx = sIdx <;> simp [h', b1, b0, hi, Function.update_of_ne]
            refine ⟨rfl, Or.inr ?_⟩
            change ActiveInv q qep rem true tL par
              { es0 with g := es0.g.afterCorr P, h := h' } none ns' sc'
            refine ⟨hbase.no_abort, hbase.no_win, rfl, hbase.sess, hbase.wf,
              ⟨hbase.sync.cache_epoch, hbase.sync.cache_inr, hbase.sync.vS_inr, hbase.sync.vR_inr⟩,
              (fun h => nomatch h), fun _ => ?_⟩
            have hm1 := hbase.main rfl
            refine ⟨?_, hm1.vR0_init, hm1.vS0_init, hm1.vS_inl_cache, hm1.vR_none_of_cache_none,
              ⟨hm1.slot_canon.1, hm1.slot_canon.2.1, hm1.slot_canon.2.2.1, ?_, hm1.slot_canon.2.2.2.2⟩,
              ?_, hm1.trans_idx, ?_, hm1.inl_comp, ?_⟩
            · intro τ h1 htH hlt
              have hep : (es0.g.afterCorr P).epoch (Party.senderOf τ) = es0.g.epoch (Party.senderOf τ) := rfl
              dsimp only at hlt
              rw [hep] at hlt
              have hne_τ : τ ≠ τ₀ := by
                intro heq; subst heq
                rcases hvSr.2.2.2.2.2 rfl with h0 | ⟨_, _, _, hc⟩
                · omega
                · have hce := (hact.sync.cache_epoch τ₀ (by rw [hc]; rfl)).2
                  omega
              have hne_s : slotOf q tL τ ≠ sIdx := by
                rw [hsl₀]; exact fun heq => hne_τ (slotOf_inj htH htH₀ heq)
              have hf := hm1.fresh_above τ h1 htH (by simpa [hep] using hlt)
              exact ⟨hf.1, by rw [hsc', Function.update_of_ne hne_s]; exact hf.2.1,
                by simpa [h', Function.update_of_ne hne_s] using hf.2.2.1, hf.2.2.2⟩
            · intro idx hbne
              by_cases hi : idx = sIdx
              · subst idx; exact ⟨hsl₀, hvSr.2.1, hvSr.2.2.1, hvSr.2.2.2.2.2 rfl⟩
              · exact hm1.slot_canon.2.2.2.1 idx (by simpa [h', Function.update_of_ne hi] using hbne)
            · intro Q idx hQ hsQ
              have his := hm1.idx_sync Q idx hQ hsQ
              exact ⟨his.1, by rw [hcnt]; exact his.2⟩
            · intro idx x hx
              rw [hftr] at hx
              rcases hm1.fsTrans_sub idx x hx with ⟨hb0, hex⟩
              refine ⟨?_, hex⟩
              by_cases hi : idx = sIdx
              · subst idx; simp [h']
              · simpa [h', Function.update_of_ne hi] using hb0
            · intro idx c hsc_idx
              rw [hsc'] at hsc_idx
              by_cases hi : idx = sIdx
              · subst idx
                simp only [Function.update_self, Option.some.injEq] at hsc_idx
                cases hsc0 : sc sIdx with
                | some c0 =>
                  rw [hsc0, Option.getD_some] at hsc_idx; subst hsc_idx
                  exact hm1.sc_comp sIdx c0 hsc0
                | none =>
                  rw [hsc0, Option.getD_none] at hsc_idx; subst hsc_idx
                  let cur := maxOpt s.tL (max (s.epoch .A) (s.epoch .B))
                  have hcur_mem : cur ∈ (s.afterCorr P).leaks := by
                    simp [cur, GameState.afterCorr, GameState.leak]
                  have hτ_le_cur : τ₀ ≤ cur := by
                    have h1 : τ₀ ≤ (s.st P).tcur := hvSr.1
                    rw [hact.wf.vp_tcur P] at h1
                    have h2 : s.epoch P ≤ max (s.epoch .A) (s.epoch .B) := by cases P <;> simp
                    exact (h1.trans h2).trans (le_maxOpt_right _ _)
                  have hlt_cur : ltOpt tL cur = true := by
                    have hh : healedBy tL 3 τ₀ = true := by
                      simp only [validGuessBucketParAuth, lastLeakGuessAdmissible,
                        Bool.and_eq_true] at hvSr
                      exact hvSr.2.1.1
                    cases tL with
                    | none => rfl
                    | some l =>
                      simp only [healedBy, decide_eq_true_eq] at hh
                      simp only [ltOpt, decide_eq_true_eq]
                      omega
                  refine ⟨hsl₀, hvSr.2.1, hvSr.2.2.1, cur, hcur_mem, hlt_cur, Or.inr ⟨hτ_le_cur, ?_⟩⟩
                  intro r hr heq_ep hlt_idx
                  have hcache_or : r.pos.epoch = 0 ∨
                      ∃ Tc σc kVal, es0.h.cache r.pos.epoch =
                        some (Tc, σc, kVal, some (slotOf q tL r.pos.epoch)) := by
                    rw [heq_ep, ← hsl₀]; exact hvSr.2.2.2.2.2 rfl
                  have hri := hm.trans_idx r hr (by simpa [heq_ep] using hvSr.2.1)
                    (by simpa [heq_ep] using hvSr.2.2.1) hcache_or
                  rw [heq_ep, ← hsl₀] at hri
                  omega
              · simp only [Function.update_of_ne hi] at hsc_idx
                exact hm1.sc_comp idx c hsc_idx

theorem i5_reveal_active_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool) (P : Party)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par st.1 st.2)
      (fun p ns' sc' => FalseInv q qep rem gMain tL par p.2 ns' sc')
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL (.inr (.inr P))).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hguard
  · simp only [StateT.run_pure]
    exact S.pure _ fun _ _ hact => Or.inr
      ⟨hact.no_abort, hact.no_win, hact.winEp_none,
       sessBound_mono_noop hact.sess rfl, hact.wf, hact.sync, hact.forged, hact.main⟩
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
    refine S.bind (hooks_reveal_active_hoare S q qep rem cka prng fs gMain tL par P es0 winEp0)
      fun ⟨res, h'⟩ => ?_
    cases res with
    | none =>
      simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]
      refine S.pure _ fun _ _ ⟨hwe, _⟩ => ?_
      subst hwe; exact Or.inl ⟨Or.inl rfl, winSafe_abort_none _⟩
    | some stOut =>
      simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]
      refine S.pure _ fun _ _ ⟨hwe, hbr⟩ => ?_
      subst hwe
      rcases hbr with h | hact'
      · exact nomatch h
      · exact Or.inr hact'

/-! ## 2. Step Dispatch, Bounded-Query Simulation, and `redFSAuthMultiBucket_false_hoare` -/

theorem implFSMultiBucketAuth_step_false_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (smq : (_root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
      (Header T × (ℕ × C))).Domain)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (FalseInv q qep (rem + 1) gMain tL par st)
      (fun p ns' sc' => FalseInv q qep rem gMain tL par p.2 ns' sc')
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL (.inr smq)).run st) := by
  intro hk
  by_cases habw : st.1.abort = true ∨ st.1.g.win = true
  · refine S.conseq
      (S.and_prop (WinSafe tL par st.1 st.2) fun hws =>
        implFSMultiBucketAuth_step_frozen S (q + 1) cka prng fs qep maxSkip gMain tL par
          (.inr smq) st habw hws (Pre := fun _ _ => True))
      (fun _ _ hinv => ⟨hinv.to_winSafe, trivial⟩)
      (fun _ _ _ ⟨hfroz, _⟩ => Or.inl hfroz)
  · refine S.conseq ?_
      (fun _ _ (hinv : FalseInv q qep (rem + 1) gMain tL par st _ _) =>
        match hinv with
        | Or.inl ⟨h, _⟩ => False.elim (habw h)
        | Or.inr hact => hact)
      (fun _ _ _ h => h)
    rcases smq with (((⟨P, m, r⟩ | _) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact i1_send_active_hoare S q qep maxSkip rem cka prng fs gMain tL par P m r st
    · change S.H _ _ ((Pure.pure none : StateT _ _ _).run st)
      simp only [StateT.run_pure]
      exact S.pure _ fun _ _ hact => Or.inr
        ⟨hact.no_abort, hact.no_win, hact.winEp_none,
         sessBound_mono_noop hact.sess rfl, hact.wf, hact.sync, hact.forged, hact.main⟩
    · exact i3_deliver_active_hoare S q qep maxSkip rem cka prng fs gMain tL par P c st
    · exact i4_inject_active_hoare S q qep maxSkip rem cka prng fs gMain tL par P c st
    · exact i5_reveal_active_hoare S q qep maxSkip rem cka prng fs gMain tL par P st

theorem simulateQ_implFSMultiBucketAuth_false_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (oa : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins
      (Header T × (ℕ × C))) Bool)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I)
    (hq : MakesAtMostQueries oa rem) :
    S.H (FalseInv q qep rem gMain tL par st)
      (fun p _ _ => WinSafe tL par p.2.1 p.2.2)
      ((simulateQ
        (implFSMultiBucketAuth
          (hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false)
          1 qep maxSkip gMain tL) oa).run st) := by
  induction oa using OracleComp.inductionOn generalizing rem st with
  | pure _ =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact S.pure _ fun _ _ hinv => hinv.to_winSafe
  | query_bind t r ih =>
    rcases t with u | smq
    · have hq' : ∀ x, MakesAtMostQueries (r x) rem := by
        intro x
        unfold MakesAtMostQueries at hq ⊢
        rw [isQueryBoundP_query_bind_iff] at hq
        simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
          Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hq.2 x
      have hcoin : S.H (FalseInv q qep rem gMain tL par st)
          (fun p ns sc => p.2 = st ∧ FalseInv q qep rem gMain tL par st ns sc)
          ((implFSMultiBucketAuth
            (hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false)
            1 qep maxSkip gMain tL (.inl u)).run st) := by
        dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
        rw [StateT.run_lift]
        exact S.bind (S.coin u) fun x => S.pure (x, st) fun _ _ h => ⟨rfl, h⟩
      simp only [simulateQ_query_bind, StateT.run_bind]
      exact S.bind hcoin fun ⟨x, st'⟩ => S.conseq (ih x rem st' (hq' x))
        (fun _ _ ⟨hst, hinv⟩ => by dsimp only at hst; rwa [hst]) (fun _ _ _ h => h)
    · unfold MakesAtMostQueries at hq
      rw [isQueryBoundP_query_bind_iff] at hq
      have hpos : 0 < rem := by
        simpa only [OracleQuery.input_query, not_true_eq_false, false_or] using hq.1
      obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, (Nat.sub_add_cancel hpos).symm⟩
      have hq' : ∀ x, MakesAtMostQueries (r x) m := by
        intro x
        unfold MakesAtMostQueries
        simpa only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
          ↓reduceIte, Nat.add_sub_cancel] using hq.2 x
      simp only [simulateQ_query_bind, StateT.run_bind]
      exact S.bind
        (implFSMultiBucketAuth_step_false_hoare S q qep maxSkip m cka prng fs gMain tL par smq st)
        fun ⟨x, st'⟩ => ih x m st' (hq' x)

theorem redFSAuthMultiBucket_false_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (lam : I) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins (ℕ × C))
    (hq : MakesAtMostQueries A q) :
    S.H (fun ns sc => (∀ i, ns i = 0) ∧ (∀ i, sc i = none))
      (fun b _ _ => b = false)
      (redFSAuthMultiBucket (q + 1) cka prng fs lam 1 qep gMain false tL par A) := by
  unfold redFSAuthMultiBucket
  refine S.bind (initFSMultiBucketAuth_false_hoare S q qep cka prng fs lam gMain tL par)
    fun ⟨⟨vA, vB⟩, h0⟩ => ?_
  dsimp only
  let g0 : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C) :=
    { st := fun P => match P with | .A => vA | .B => vB, b := false }
  refine S.conseq
    (S.bind
      (simulateQ_implFSMultiBucketAuth_false_hoare S q qep fs.maxSkip q cka prng fs gMain tL par A
        ({ g := g0, h := h0, abort := false }, none) hq)
      fun ⟨_, es, winEp⟩ => ?_)
    (fun _ _ hact => Or.inr hact)
    (fun _ _ _ h => h)
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases winEp with
  | none => exact S.pure _ fun _ _ _ => rfl
  | some tWin => exact S.pure _ fun _ _ hws => hws tWin rfl

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalse
