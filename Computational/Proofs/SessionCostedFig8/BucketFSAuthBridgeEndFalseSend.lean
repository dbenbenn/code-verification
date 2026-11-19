/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux

/-!
# Active `Send` (`i₁`) Step Proof for `la = false`

Proves `i1_send_active_hoare` preserving `FalseInv` across one adversary transmit query
(`rem + 1 → rem`).-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseSend

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (Pos Record GameState ltOpt healedBy maxOpt
  lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (PartyState Header healEpoch
  FSMultiSpec FSMultiBook sampleT)
open _root_.CryptoGames.SM.Engine (VP Ctx EState vSend)
open _root_.CryptoGames.SM.Thm1L17 (sendsIn_of_sendsIn_add_one_eq_false
  senderOf_eq_of_sendsIn le_maxOpt_right not_healedBy_leak)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (postLeak)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState FSMultiBucketAuthEState liftFSMultiBucket
  regSessMultiBucket regSessOptMultiBucket validGuessBucketParAuth
  isHonestHdrMultiBucket hooksFSMultiBucketAuth implFSMultiBucketAuth)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase (
  FSFalseSemantics slotEpoch slotOf healEpoch_le_of_validGuess slotOf_inj slotEpoch_slotOf
  regSessMultiBucket_slotEpoch regSessMultiBucket_sessions_bound isHonestHdr_update_cache_of_none
  WinSafe SessBound sessBound_lt sessBound_mono_noop sessBound_regSessOpt
  EngineWF leak_witness_of_not_healedBy_s
  SlotSync ForgedInv MainInv ActiveInv FalseInv
  stateT_lift_sampleT_hoare lazy_cs_hoare rootFSMultiBucketAuth_false_hoare)

/-! ## Active `Send` (`i₁`) Step Proof -/

private theorem sample_or_pure_coins_hoare
    {T RSt K I SS RS M C CCoins : Type} [SampleableType CCoins]
    (S : FSFalseSemantics SS RS T M C)
    (Pre : (ℕ → ℕ) → (ℕ → Option ℕ) → Prop)
    (r : Option CCoins)
    (h0 : FSMultiBucketAuthState T RSt K I (ℕ × C)) :
    S.H Pre
      (fun (p : CCoins × _) ns sc => p.2 = h0 ∧ Pre ns sc)
      (((match r with
        | some c => Pure.pure c
        | none => StateT.lift (sampleT CCoins)) :
        StateT (FSMultiBucketAuthState T RSt K I (ℕ × C))
          (OracleComp (unifSpec + FSMultiSpec SS RS T M (ℕ × C))) CCoins).run h0) := by
  cases r with
  | some c => exact S.pure (c, h0) fun _ _ ha => ⟨rfl, ha⟩
  | none => exact stateT_lift_sampleT_hoare S h0

set_option linter.unusedSimpArgs false in
private theorem startSend_or_same_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (r : Option CCoins)
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (s₁ : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (hep : es0.g.epMgmt 3 qep P r.isSome = some s₁) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par es0 none)
      (fun (p : Option (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) ×
                FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        match p.1 with
        | none => True
        | some s_mid =>
          s₁.epoch P ≤ qep ∧
          P.sendsIn (s₁.epoch P) = true ∧
          ActiveInv q qep rem gMain tL par
            { g := { s₁ with st := Function.update s₁.st P s_mid },
              h := p.2, abort := false } none ns' sc')
      ((if (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) then do
          match ← hk.startSend s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r with
          | none => Pure.pure none
          | some (γ', T', σ', ss) =>
            Pure.pure (some { s₁.st P with tcur := (s₁.st P).tcur + 1, γ := γ',
                                           curCkaMsg := some T', root := σ', vS := some ss })
        else Pure.pure (some (s₁.st P))).run es0.h) := by
  intro hk
  let s₀ := es0.g
  change s₀.epMgmt 3 qep P r.isSome = some s₁ at hep
  unfold GameState.epMgmt at hep
  by_cases hsends1 : P.sendsIn (s₀.epoch P + 1) = true
  · simp only [hsends1, ↓reduceIte] at hep
    by_cases hqep_lt : qep < s₀.epoch P + 1
    · simp [hqep_lt] at hep
    · simp only [hqep_lt, ↓reduceIte, Option.some.injEq] at hep
      have ht0_le_qep : s₀.epoch P + 1 ≤ qep := by omega
      let t0 := s₀.epoch P + 1
      have ht0_def : t0 = es0.g.epoch P + 1 := rfl
      have hs₀_ep : ∀ Q, s₀.epoch Q = es0.g.epoch Q := fun _ => rfl
      have ht0_ge1 : 1 ≤ t0 := Nat.succ_pos _
      have hs₁_st : s₁.st = s₀.st := by rw [← hep]; split_ifs <;> rfl
      have hs₁_epP : s₁.epoch P = t0 := by rw [← hep]; split_ifs <;> simp [GameState.leak, t0]
      have hs₁_idxP : s₁.idx P = 0 := by rw [← hep]; split_ifs <;> simp [GameState.leak]
      have hs₁_win : s₁.win = s₀.win := by rw [← hep]; split_ifs <;> rfl
      have hs₁_trans : s₁.trans = s₀.trans := by rw [← hep]; split_ifs <;> rfl
      have hs₁_comp : s₁.comp = s₀.comp := by rw [← hep]; split_ifs <;> rfl
      have hs₁_leaks_sub : ∀ lk ∈ s₀.leaks, lk ∈ s₁.leaks := by
        intro lk hlk; rw [← hep]; split_ifs <;> simp [GameState.leak, hlk]
      have hsender_t0 : Party.senderOf t0 = P := senderOf_eq_of_sendsIn hsends1
      dsimp only [hk, hooksFSMultiBucketAuth]
      refine S.conseq
        (Pre₁ := ActiveInv q qep (rem + 1) gMain tL par es0 none)
        (Post₁ := fun p ns' sc' =>
          match p.1 with
          | none => True
          | some s_mid =>
            s₁.epoch P ≤ qep ∧
            P.sendsIn (s₁.epoch P) = true ∧
            ActiveInv q qep rem gMain tL par
              { g := { s₁ with st := Function.update s₁.st P s_mid },
                h := p.2, abort := false } none ns' sc') ?_ (fun _ _ h => h) (fun _ _ _ h => h)
      -- Since `s₁.st P = s₀.st P`, rewrite the `if` condition inside the Hoare proof
      by_cases hcond : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = true
      · simp only [hcond, ↓reduceIte, StateT.run_bind, bind_assoc]
        refine S.bind (sample_or_pure_coins_hoare S _ r es0.h) fun ⟨coins, h1⟩ => ?_
        simp only [StateT.run_bind, bind_assoc]
        refine S.bind (rootFSMultiBucketAuth_false_hoare S prng qep tL par
          ((s₁.st P).tcur + 1) (postLeak tL s₁) (cka.send (s₁.st P).γ coins).2.2 (s₁.st P).root h1)
          fun ⟨⟨σ', kVal, sid⟩, h2⟩ => ?_
        simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
        refine S.pure _ fun ns sc ⟨hc2, hs2, hb2, ⟨hh1, hact⟩, hsid⟩ => ?_
        subst hh1
        have htcur_eq : (s₁.st P).tcur + 1 = t0 := by
          rw [hs₁_st, hact.wf.vp_tcur P]
        rw [htcur_eq] at hsid ⊢
        have hc_t0_none : es0.h.cache t0 = none := by
          cases hc0 : es0.h.cache t0 with
          | none => rfl
          | some val =>
            have := (hact.sync.cache_epoch t0 (by simp [hc0])).2
            rw [hsender_t0] at this; omega
        have htL_s1 : s₁.tL = s₁.leaks.max? := by
          rw [← hep]
          split_ifs
          · exact hact.wf.tL_leak_eq t0
          · exact hact.wf.tL_eq
        let cOut := cka.send (s₁.st P).γ coins
        let reg := regSessOptMultiBucket (q + 1) gMain tL t0 sid h2
        let optIdx := reg.1
        let s2 := reg.2
        let h_mid : FSMultiBucketAuthState T RSt K I (ℕ × C) :=
          { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with
          | none => .inl (fs.initSender kVal)
          | some sIdx => .inr sIdx
        let s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
          { s₁.st P with tcur := t0, γ := cOut.1, curCkaMsg := some cOut.2.1,
                         root := σ', vS := some ssv }
        let s_upd := { s₁ with st := Function.update s₁.st P s_mid }
        have hs2_cache : s2.cache = es0.h.cache := by
          cases sid with
          | none => exact hc2
          | some ik => exact (regSessMultiBucket_sessions_bound (q + 1) gMain tL t0 ik h2).1.trans hc2
        have hs2_book : s2.book = es0.h.book := by
          cases sid with
          | none => exact hb2
          | some ik => exact (regSessMultiBucket_sessions_bound (q + 1) gMain tL t0 ik h2).2.1.trans hb2
        dsimp only [s2, reg] at hs2_cache hs2_book
        have hsess_s2 : SessBound q gMain rem s2 := by
          have hs_h2 : SessBound q gMain (rem + 1) h2 := by
            intro τ; rw [hs2]; exact hact.sess τ
          exact sessBound_regSessOpt hs_h2
        have hsess_mid : SessBound q gMain rem h_mid := hsess_s2
        have hep_mono : ∀ Q, s₀.epoch Q ≤ s_upd.epoch Q := by
          intro Q; dsimp only [s_upd]; rw [← hep]
          by_cases hQ : Q = P
          · subst Q; split_ifs <;> simp [GameState.leak]
          · split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
        have hwf_upd : EngineWF s_upd := by
          refine ⟨?_, ?_, ?_, ?_, htL_s1⟩
          · intro Q; by_cases hQ : Q = P
            · subst Q; simpa [s_upd, s_mid, hs₁_st] using hact.wf.vp_id P
            · simpa [s_upd, Function.update_of_ne hQ, hs₁_st] using hact.wf.vp_id Q
          · intro Q; by_cases hQ : Q = P
            · subst Q; simp [s_upd, s_mid, hs₁_epP]
            · have hne : s₁.epoch Q = s₀.epoch Q := by
                rw [← hep]; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
              simpa [s_upd, Function.update_of_ne hQ, hs₁_st, hne] using hact.wf.vp_tcur Q
          · intro Q hsQ; by_cases hQ : Q = P
            · subst Q; simp [s_upd, s_mid]
            · simp [s_upd, Function.update_of_ne hQ, hs₁_st] at hsQ ⊢
              exact hact.wf.vp_vS_some Q hsQ
          · intro rec hr
            rw [show s_upd.trans = s₀.trans from hs₁_trans] at hr
            rcases hact.wf.trans_wf rec hr with ⟨h1, h2, h3⟩
            exact ⟨h1, h2, h3.trans (hep_mono _)⟩
        refine ⟨by rw [hs₁_epP]; exact ht0_le_qep, by rw [hs₁_epP]; exact hsends1,
          rfl, by rw [show s_upd.win = s₀.win from hs₁_win]; exact hact.no_win,
          rfl, hsess_mid, hwf_upd, ?_, ?_, ?_⟩
        · -- `SlotSync` on `(s_upd, h_mid)`
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro τ hcs
            by_cases hτ : τ = t0
            · subst τ
              refine ⟨ht0_ge1, ?_⟩
              rw [hsender_t0]; simp [s_upd, hs₁_epP]
            · simp only [h_mid, Function.update_of_ne hτ, hs2_cache] at hcs
              rcases hact.sync.cache_epoch τ hcs with ⟨h1, h2⟩
              exact ⟨h1, h2.trans (hep_mono _)⟩
          · intro τ Tc σc kV sIdx hc_eq
            by_cases hτ : τ = t0
            · subst τ
              simp only [h_mid, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc_eq
              rcases hc_eq with ⟨_, _, _, hopt⟩
              cases hsid_v : sid with
              | none => simp [optIdx, reg, hsid_v, regSessOptMultiBucket] at hopt
              | some ik =>
                have hok := hsid.mp (by simp [hsid_v])
                have hlen : (h2.sessions t0).length < q + 1 := by
                  rw [hs2]; exact sessBound_lt hact.sess t0
                have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) gMain tL t0 ik h2
                  (healEpoch_le_of_validGuess hok.2.2) hlen
                simp only [optIdx, reg, hsid_v, regSessOptMultiBucket, Option.some.injEq] at hopt
                rw [← hopt]
                exact ⟨hreg.1, hok.2.2, hok.2.1⟩
            · simp only [h_mid, Function.update_of_ne hτ, hs2_cache] at hc_eq
              exact hact.sync.cache_inr τ Tc σc kV sIdx hc_eq
          · intro Q sIdx hvSQ
            by_cases hQ : Q = P
            · subst Q
              simp only [s_upd, Function.update_self, s_mid] at hvSQ ⊢
              cases hsid_v : sid with
              | none => simp [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket] at hvSQ
              | some ik =>
                have hok := hsid.mp (by simp [hsid_v])
                have hlen : (h2.sessions t0).length < q + 1 := by
                  rw [hs2]; exact sessBound_lt hact.sess t0
                have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) gMain tL t0 ik h2
                  (healEpoch_le_of_validGuess hok.2.2) hlen
                simp only [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket,
                  Option.some.injEq, Sum.inr.injEq] at hvSQ
                have hep_idx : slotEpoch (q + 1) gMain tL sIdx = t0 := by
                  rw [← hvSQ]; exact hreg.1
                refine ⟨by omega, by simpa [hep_idx] using hok.2.2, by omega,
                  fun _ => by omega, fun _ => ⟨hep_idx, Or.inr ?_⟩, fun _ => Or.inr ?_⟩
                · simp [isHonestHdrMultiBucket, h_mid]
                · refine ⟨cOut.2.1, σ', kVal, ?_⟩
                  simp [h_mid, optIdx, reg, hsid_v, regSessOptMultiBucket, hvSQ, hep_idx, cOut]
            · simp only [s_upd, Function.update_of_ne hQ, hs₁_st] at hvSQ ⊢
              have hv0 := hact.sync.vS_inr Q sIdx hvSQ
              refine ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1, fun hsQ => ?_, fun hgm => ?_⟩
              · rcases hv0.2.2.2.2.1 hsQ with ⟨h1, h2⟩
                refine ⟨h1, ?_⟩
                rcases h2 with h0 | hhdr
                · exact Or.inl h0
                · exact Or.inr (isHonestHdr_update_cache_of_none
                    hc_t0_none (by dsimp only; rw [hs2_cache]) hhdr)
              · rcases hv0.2.2.2.2.2 hgm with h0 | ⟨Tc, σc, kV, hc0⟩
                · exact Or.inl h0
                · have hne : slotEpoch (q + 1) gMain tL sIdx ≠ t0 := by
                    intro heq; rw [heq, hc_t0_none] at hc0; exact nomatch hc0
                  exact Or.inr ⟨Tc, σc, kV, by simp [h_mid, Function.update_of_ne hne, hs2_cache, hc0]⟩
          · intro Q τ sIdx hvrQ
            have hvr0 : (s₀.st Q).vR τ = some (.inr sIdx) := by
              by_cases hQ : Q = P
              · subst Q; simpa [s_upd, s_mid, hs₁_st] using hvrQ
              · simpa [s_upd, Function.update_of_ne hQ, hs₁_st] using hvrQ
            have hv0 := hact.sync.vR_inr Q τ sIdx hvr0
            refine ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1, fun hgm => ?_⟩
            rcases hv0.2.2.2.2 hgm with h0 | ⟨Tc, σc, kV, hc0⟩
            · exact Or.inl h0
            · have hne : τ ≠ t0 := by intro heq; rw [heq, hc_t0_none] at hc0; exact nomatch hc0
              exact Or.inr ⟨Tc, σc, kV, by simp [h_mid, Function.update_of_ne hne, hs2_cache, hc0]⟩
        · -- `ForgedInv` on `(s_upd, h_mid)`
          intro hgf
          have hf := hact.forged hgf
          refine ⟨?_, ?_⟩
          · intro sIdx x hx
            have hx0 : x ∈ ((es0.h.book sIdx).getD {}).fsTrans := by
              simpa [h_mid, hs2_book] using hx
            exact isHonestHdr_update_cache_of_none
              (h := es0.h) (h' := h_mid) (val := (cOut.2.1, σ', kVal, optIdx))
              hc_t0_none (by dsimp only [h_mid, s2, reg]; rw [hs2_cache])
              (hf.hdr_honest sIdx x hx0)
          · intro sIdx hsc
            have hnh := hf.sc_not_healed sIdx hsc
            dsimp only [s_upd]; rw [← hep]
            split_ifs
            · exact not_healedBy_leak hnh
            · exact hnh
        · -- `MainInv` on `(s_upd, h_mid)`
          intro hgt
          subst hgt
          have hm := hact.main rfl
          have hfresh_t0 : validGuessBucketParAuth 1 tL par t0 = true →
              ns (slotOf q tL t0) = 0 ∧ sc (slotOf q tL t0) = none ∧
              es0.h.book (slotOf q tL t0) = none ∧ es0.h.sessions t0 = [] := by
            intro hvt0
            exact hm.fresh_above t0 ht0_ge1 (healEpoch_le_of_validGuess hvt0)
              (by rw [hsender_t0]; omega)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro τ h1 htH hlt
            have hne_τ : τ ≠ t0 := by
              intro heq; subst heq; rw [hsender_t0] at hlt
              simp [s_upd, hs₁_epP] at hlt
            have hf := hm.fresh_above τ h1 htH (lt_of_le_of_lt (hep_mono _) hlt)
            refine ⟨hf.1, hf.2.1, by simp [h_mid, hs2_book, hf.2.2.1], ?_⟩
            cases sid with
            | none => simpa [h_mid, s2, reg, regSessOptMultiBucket, hs2] using hf.2.2.2
            | some ik =>
              have hb := regSessMultiBucket_sessions_bound (q + 1) true tL t0 ik h2
              simpa [h_mid, s2, reg, regSessOptMultiBucket, hb.2.2.1 τ hne_τ, hs2] using hf.2.2.2
          · intro hv0
            by_cases hPA : P = .A
            · simpa [s_upd, hPA, s_mid, hs₁_st] using hm.vR0_init hv0
            · simpa [s_upd, Function.update_of_ne (Ne.symm hPA), hs₁_st] using hm.vR0_init hv0
          · intro hB0 hv0
            by_cases hPB : P = .B
            · dsimp only [s_upd] at hB0; rw [← hPB, hs₁_epP] at hB0; omega
            · have hne : s₁.epoch .B = s₀.epoch .B := by
                rw [← hep]; split_ifs <;> simp [GameState.leak, Function.update_of_ne (Ne.symm hPB)]
              simp only [s_upd, hne] at hB0
              simpa [s_upd, Function.update_of_ne (Ne.symm hPB), hs₁_st] using hm.vS0_init hB0 hv0
          · intro Q ss h1 hsQ hvSQ
            by_cases hQ : Q = P
            · subst Q
              simp only [s_upd, Function.update_self, s_mid] at hvSQ ⊢
              cases hsid_v : sid with
              | none =>
                exact ⟨cOut.2.1, σ', kVal,
                  by simp [h_mid, optIdx, reg, hsid_v, regSessOptMultiBucket, cOut]⟩
              | some ik =>
                simp [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket] at hvSQ
            · simp only [s_upd, Function.update_of_ne hQ, hs₁_st] at h1 hsQ hvSQ ⊢
              rcases hm.vS_inl_cache Q ss h1 hsQ hvSQ with ⟨Tc, σc, kV, hc0⟩
              have hne : (s₀.st Q).tcur ≠ t0 := by
                intro heq; rw [heq, hc_t0_none] at hc0; exact nomatch hc0
              exact ⟨Tc, σc, kV, by
                rw [Function.update_of_ne hne, hs2_cache]
                exact hc0⟩
          · intro Q τ h1 hc_none
            have hne : τ ≠ t0 := by intro heq; subst τ; simp [h_mid] at hc_none
            simp only [h_mid, Function.update_of_ne hne, hs2_cache] at hc_none
            by_cases hQ : Q = P
            · subst Q; simpa [s_upd, s_mid, hs₁_st] using hm.vR_none_of_cache_none P τ h1 hc_none
            · simpa [s_upd, Function.update_of_ne hQ, hs₁_st] using hm.vR_none_of_cache_none Q τ h1 hc_none
          · -- `slot_canon` (5 conjuncts)
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro Q sIdx hvSQ
              by_cases hQ : Q = P
              · subst Q
                simp only [s_upd, Function.update_self, s_mid] at hvSQ
                cases hsid_v : sid with
                | none => simp [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket] at hvSQ
                | some ik =>
                  have hok := hsid.mp (by simp [hsid_v])
                  have hnil : h2.sessions t0 = [] := by rw [hs2]; exact (hfresh_t0 hok.2.2).2.2.2
                  have hlen : (h2.sessions t0).length < q + 1 := by rw [hnil]; exact Nat.succ_pos q
                  have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) true tL t0 ik h2
                    (healEpoch_le_of_validGuess hok.2.2) hlen
                  simp only [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket,
                    Option.some.injEq, Sum.inr.injEq] at hvSQ
                  rw [← hvSQ, hreg.1, hreg.2.2 rfl hnil]
              · simp only [s_upd, Function.update_of_ne hQ, hs₁_st] at hvSQ
                exact hm.slot_canon.1 Q sIdx hvSQ
            · intro τ Tc σc kV sIdx hc_eq
              by_cases hτ : τ = t0
              · subst τ
                simp only [h_mid, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc_eq
                rcases hc_eq with ⟨_, _, _, hopt⟩
                cases hsid_v : sid with
                | none => simp [optIdx, reg, hsid_v, regSessOptMultiBucket] at hopt
                | some ik =>
                  have hok := hsid.mp (by simp [hsid_v])
                  have hnil : h2.sessions t0 = [] := by rw [hs2]; exact (hfresh_t0 hok.2.2).2.2.2
                  have hlen : (h2.sessions t0).length < q + 1 := by rw [hnil]; exact Nat.succ_pos q
                  have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) true tL t0 ik h2
                    (healEpoch_le_of_validGuess hok.2.2) hlen
                  simp only [optIdx, reg, hsid_v, regSessOptMultiBucket, Option.some.injEq] at hopt
                  rw [← hopt, hreg.2.2 rfl hnil]
              · simp only [h_mid, Function.update_of_ne hτ, hs2_cache] at hc_eq
                exact hm.slot_canon.2.1 τ Tc σc kV sIdx hc_eq
            · intro Q τ sIdx hvrQ
              have hvr0 : (s₀.st Q).vR τ = some (.inr sIdx) := by
                by_cases hQ : Q = P
                · subst Q; simpa [s_upd, s_mid, hs₁_st] using hvrQ
                · simpa [s_upd, Function.update_of_ne hQ, hs₁_st] using hvrQ
              exact hm.slot_canon.2.2.1 Q τ sIdx hvr0
            · intro sIdx hb_ne
              simp only [h_mid, hs2_book] at hb_ne
              rcases hm.slot_canon.2.2.2.1 sIdx hb_ne with ⟨hsl, hv, hle, h0_or⟩
              refine ⟨hsl, hv, hle, ?_⟩
              rcases h0_or with h0 | ⟨Tc, σc, kV, hc0⟩
              · exact Or.inl h0
              · have hne : slotEpoch (q + 1) true tL sIdx ≠ t0 := by
                  intro heq; rw [heq, hc_t0_none] at hc0; exact nomatch hc0
                exact Or.inr ⟨Tc, σc, kV, by simp [h_mid, Function.update_of_ne hne, hs2_cache, hc0]⟩
            · intro τ Tc σc kV sIdx rs hc_eq
              by_cases hτ : τ = t0
              · subst τ
                have hnone := hm.vR_none_of_cache_none (Party.receiverOf t0) t0 ht0_ge1 hc_t0_none
                by_cases hrec : Party.receiverOf t0 = P
                · rw [hrec] at hnone ⊢; simp [s_upd, s_mid, hs₁_st, s₀, hnone]
                · simp [s_upd, Function.update_of_ne hrec, hs₁_st, s₀, hnone]
              · simp only [h_mid, Function.update_of_ne hτ, hs2_cache] at hc_eq
                have h0 := hm.slot_canon.2.2.2.2 τ Tc σc kV sIdx rs hc_eq
                by_cases hrec : Party.receiverOf τ = P
                · rw [hrec] at h0 ⊢; simpa [s_upd, s_mid, hs₁_st] using h0
                · simpa [s_upd, Function.update_of_ne hrec, hs₁_st] using h0
          · -- `idx_sync`
            intro Q sIdx hvSQ hsQ
            by_cases hQ : Q = P
            · subst Q
              simp only [s_upd, Function.update_self, s_mid] at hvSQ
              cases hsid_v : sid with
              | none => simp [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket] at hvSQ
              | some ik =>
                have hok := hsid.mp (by simp [hsid_v])
                have hfr := hfresh_t0 hok.2.2
                have hnil : h2.sessions t0 = [] := by rw [hs2]; exact hfr.2.2.2
                have hlen : (h2.sessions t0).length < q + 1 := by rw [hnil]; exact Nat.succ_pos q
                have hreg := regSessMultiBucket_slotEpoch (Nat.succ_pos q) true tL t0 ik h2
                  (healEpoch_le_of_validGuess hok.2.2) hlen
                simp only [ssv, optIdx, reg, hsid_v, regSessOptMultiBucket,
                  Option.some.injEq, Sum.inr.injEq] at hvSQ
                have hsIdx_eq : sIdx = slotOf q tL t0 := by
                  rw [← hvSQ]; exact hreg.2.2 rfl hnil
                rw [hsIdx_eq]
                exact ⟨by simp [s_upd, hs₁_idxP, hfr.1],
                  by simp [h_mid, ← hsid_v, hs2_book, hfr.2.2.1, hfr.1]⟩
            · simp only [s_upd, Function.update_of_ne hQ, hs₁_st] at hvSQ hsQ
              have his := hm.idx_sync Q sIdx hvSQ hsQ
              have hidxQ : s_upd.idx Q = s₀.idx Q := by
                dsimp only [s_upd]; rw [← hep]; split_ifs <;> simp [GameState.leak, Function.update_of_ne hQ]
              exact ⟨by rw [hidxQ]; exact his.1, by simpa [h_mid, hs2_book] using his.2⟩
          · -- `trans_idx`
            intro rec hr hv_r hle_r hcache_or
            rw [show s_upd.trans = s₀.trans from hs₁_trans] at hr
            have hne_r : rec.pos.epoch ≠ t0 := by
              rcases hact.wf.trans_wf rec hr with ⟨_, h2_r, h3⟩
              intro heq; rw [h2_r, heq, hsender_t0] at h3; omega
            refine hm.trans_idx rec hr hv_r hle_r ?_
            rcases hcache_or with h0 | ⟨Tc, σc, kV, hc⟩
            · exact Or.inl h0
            · simp only [h_mid, Function.update_of_ne hne_r, hs2_cache] at hc
              exact Or.inr ⟨Tc, σc, kV, hc⟩
          · -- `fsTrans_sub`
            intro sIdx x hx
            have hx0 : x ∈ ((es0.h.book sIdx).getD {}).fsTrans := by
              simpa [h_mid, hs2_book] using hx
            have ⟨hbn, r_mem⟩ := hm.fsTrans_sub sIdx x hx0
            exact ⟨by dsimp only [h_mid]; rw [hs2_book]; exact hbn,
              by dsimp only [s_upd]; rw [hs₁_trans]; exact r_mem⟩
          · -- `inl_comp`
            intro τ hle_τ hv_τ hinl
            by_cases hτ : τ = t0
            · subst τ
              have hpl1 : postLeak tL s₁ = true := by
                rcases hinl with ⟨Tc, σc, kV, hc_eq⟩ | ⟨rs, hvr_eq⟩
                · simp only [h_mid, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc_eq
                  rcases hc_eq with ⟨_, _, _, hopt⟩
                  cases hsid_v : sid with
                  | some ik => simp [optIdx, reg, hsid_v, regSessOptMultiBucket] at hopt
                  | none =>
                    cases hpl : postLeak tL s₁ with
                    | true => rfl
                    | false =>
                      have := hsid.mpr ⟨hpl, ht0_le_qep.trans (Nat.le_succ _), hv_τ⟩
                      simp [hsid_v] at this
                · have hnone := hm.vR_none_of_cache_none (Party.receiverOf t0) t0 ht0_ge1 hc_t0_none
                  by_cases hrec : Party.receiverOf t0 = P
                  · rw [hrec] at hvr_eq hnone; simp [s_upd, s_mid, hs₁_st, s₀, hnone] at hvr_eq
                  · simp [s_upd, Function.update_of_ne hrec, hs₁_st, s₀, hnone] at hvr_eq
              unfold postLeak at hpl1
              cases hstL : s₁.tL with
              | none => simp [hstL] at hpl1
              | some cur =>
                rw [hstL] at hpl1
                have hcur_mem : cur ∈ s₁.leaks := by
                  rw [htL_s1, List.max?_eq_some_iff] at hstL; exact hstL.1
                refine ⟨cur, hcur_mem, hpl1, ?_⟩
                by_cases hlt_c : cur < t0
                · exact Or.inl hlt_c
                · refine Or.inr ⟨Nat.le_of_not_lt hlt_c, fun rec hr heq_ep => ?_⟩
                  rw [show s_upd.trans = s₀.trans from hs₁_trans] at hr
                  rcases hact.wf.trans_wf rec hr with ⟨_, h2_r, h3⟩
                  rw [h2_r, heq_ep, hsender_t0] at h3; omega
            · have hinl0 : (∃ Tc σc kV, es0.h.cache τ = some (Tc, σc, kV, none)) ∨
                  (∃ rs, (s₀.st (Party.receiverOf τ)).vR τ = some (.inl rs)) := by
                rcases hinl with ⟨Tc, σc, kV, hc_eq⟩ | ⟨rs, hvr_eq⟩
                · simp only [h_mid, Function.update_of_ne hτ, hs2_cache] at hc_eq
                  exact Or.inl ⟨Tc, σc, kV, hc_eq⟩
                · refine Or.inr ⟨rs, ?_⟩
                  by_cases hrec : Party.receiverOf τ = P
                  · rw [hrec] at hvr_eq ⊢; simpa [s_upd, s_mid, hs₁_st] using hvr_eq
                  · simpa [s_upd, Function.update_of_ne hrec, hs₁_st] using hvr_eq
              rcases hm.inl_comp τ hle_τ hv_τ hinl0 with ⟨cur, hcur, hlt, hbr⟩
              refine ⟨cur, hs₁_leaks_sub cur hcur, hlt, ?_⟩
              rcases hbr with hlt' | ⟨hle', hc⟩
              · exact Or.inl hlt'
              · exact Or.inr ⟨hle', fun rec hr heq => by
                  rw [hs₁_comp]; exact hc rec (by simpa [hs₁_trans] using hr) heq⟩
          · -- `sc_comp`
            intro sIdx c hsc
            rcases hm.sc_comp sIdx c hsc with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
            refine ⟨hsl, hv, hle, cur, hs₁_leaks_sub cur hcur, hlt, ?_⟩
            rcases hbr with hlt' | ⟨hle', hc⟩
            · exact Or.inl hlt'
            · exact Or.inr ⟨hle', fun rec hr heq hci => by
                rw [hs₁_comp]; exact hc rec (by simpa [hs₁_trans] using hr) heq hci⟩
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        refine S.pure _ fun ns sc hact => ?_
        rw [hs₁_st, hact.wf.vp_id P, hact.wf.vp_tcur P] at hcond
        exact absurd hsends1 hcond
  · -- Same-epoch branch: `P.sendsIn (s₀.epoch P + 1) = false`
    simp only [hsends1, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hqep_lt : qep < s₀.epoch P
    · simp [hqep_lt] at hep
    · simp only [hqep_lt, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      have hsends0 : P.sendsIn (s₀.epoch P) = true :=
        sendsIn_of_sendsIn_add_one_eq_false (by simpa using hsends1)
      have hqep_le : s₀.epoch P ≤ qep := Nat.le_of_not_lt hqep_lt
      by_cases hcond : (s₀.st P).id.sendsIn ((s₀.st P).tcur + 1) = true
      · simp only [hcond, ↓reduceIte]
        refine S.conseq (Pre₁ := fun _ _ => False) (Post₁ := fun _ _ _ => False) S.exfalso ?_
          (fun _ _ _ h => False.elim h)
        intro _ _ hact
        rw [hact.wf.vp_id P, hact.wf.vp_tcur P] at hcond
        exact absurd hcond hsends1
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
        refine S.pure _ fun ns sc hact => ?_
        have hupd : { s₀ with st := Function.update s₀.st P (s₀.st P) } = s₀ := by
          simp
        dsimp only
        rw [hupd]
        exact ⟨hqep_le, hsends0, rfl, hact.no_win, rfl,
          sessBound_mono_noop hact.sess rfl, hact.wf, hact.sync, hact.forged, hact.main⟩

set_option linter.unusedSimpArgs false in
private theorem fsSend_record_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (m : M)
    (s₁ : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C))
    (s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h_mid : FSMultiBucketAuthState T RSt K I (ℕ × C))
    (hqep_le : s₁.epoch P ≤ qep)
    (hsends : P.sendsIn (s₁.epoch P) = true) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    let s_upd := { s₁ with st := Function.update s₁.st P s_mid }
    let hdr : Header T := (s_mid.tcur, s_mid.curCkaMsg)
    S.H (ActiveInv q qep rem gMain tL par { g := s_upd, h := h_mid, abort := false } none)
      (fun (p : Option (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × (Header T × (ℕ × C))) ×
                FSMultiBucketAuthState T RSt K I (ℕ × C)) ns' sc' =>
        match p.1 with
        | none => True
        | some (st', ct) =>
          let recE : Record M (Header T × (ℕ × C)) :=
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          ActiveInv q qep rem gMain tL par
            { g := s₁.record 3 P st' recE false, h := p.2, abort := false } none ns' sc')
      ((match s_mid.vS with
        | none => Pure.pure (some (s_mid, (hdr, default)))
        | some v => do
          match ← hk.fsSend s₁ P s_mid.tcur v hdr m none with
          | none => Pure.pure none
          | some (v', e) => Pure.pure (some ({ s_mid with vS := some v' }, (hdr, e)))).run h_mid) := by
  intro hk s_upd hdr
  have hsender : Party.senderOf (s₁.epoch P) = P := senderOf_eq_of_sendsIn hsends
  cases hvS : s_mid.vS with
  | none =>
    simp only [StateT.run_pure]
    refine S.pure _ fun ns sc hact => ?_
    have htcur : s_mid.tcur = s₁.epoch P := by simpa [s_upd] using hact.wf.vp_tcur P
    have hsome := hact.wf.vp_vS_some P (by simpa [s_upd, htcur] using hsends)
    simp [s_upd, hvS] at hsome
  | some v =>
    dsimp only [hk, hooksFSMultiBucketAuth]
    cases v with
    | inl ss =>
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine S.pure _ fun ns sc hact => ?_
      let st' := { s_mid with vS := some (Sum.inl (fs.send ss hdr m).1 : SS ⊕ ℕ) }
      let ct : Header T × (ℕ × C) := (hdr, (fs.send ss hdr m).2)
      let recE : Record M (Header T × (ℕ × C)) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
      let s' := s₁.record 3 P st' recE false
      have htcur : s_mid.tcur = s₁.epoch P := by simpa [s_upd] using hact.wf.vp_tcur P
      have hst_ne : ∀ {Q}, Q ≠ P → s'.st Q = s_upd.st Q := fun hQ => by
        simp [s', s_upd, GameState.record, Function.update_of_ne hQ]
      refine ⟨rfl, hact.no_win, rfl, hact.sess, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, hact.wf.tL_eq⟩
        · intro Q; by_cases hQ : Q = P
          · subst Q; simpa [s', GameState.record, st', s_upd] using hact.wf.vp_id P
          · rw [hst_ne hQ]; exact hact.wf.vp_id Q
        · intro Q; by_cases hQ : Q = P
          · subst Q; simp [s', GameState.record, st', htcur]
          · rw [hst_ne hQ]; exact hact.wf.vp_tcur Q
        · intro Q hsQ; by_cases hQ : Q = P
          · subst Q; simp [s', GameState.record, st']
          · rw [hst_ne hQ] at hsQ ⊢; exact hact.wf.vp_vS_some Q hsQ
        · intro r hr
          simp only [s', GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr0
          · exact ⟨htcur, hsender.symm, by simp [s', GameState.record, hsender]⟩
          · exact hact.wf.trans_wf r hr0
      · refine ⟨hact.sync.cache_epoch, hact.sync.cache_inr, ?_, ?_⟩
        · intro Q idx hvQ
          by_cases hQ : Q = P
          · subst Q; simp [s', GameState.record, st'] at hvQ
          · rw [hst_ne hQ] at hvQ ⊢; exact hact.sync.vS_inr Q idx hvQ
        · intro Q τ idx hvrQ
          by_cases hQ : Q = P
          · subst Q; exact hact.sync.vR_inr P τ idx (by simpa [s', GameState.record, st', s_upd] using hvrQ)
          · rw [hst_ne hQ] at hvrQ; exact hact.sync.vR_inr Q τ idx hvrQ
      · intro hgf
        exact ⟨(hact.forged hgf).hdr_honest, (hact.forged hgf).sc_not_healed⟩
      · intro hgt; subst hgt
        have hm := hact.main rfl
        refine ⟨hm.fresh_above, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hv0
          by_cases hPA : P = .A
          · subst P; simpa [s', GameState.record, st', s_upd] using hm.vR0_init hv0
          · rw [hst_ne (Ne.symm hPA)]; exact hm.vR0_init hv0
        · intro hB0 hv0
          have hvB := hm.vS0_init hB0 hv0
          by_cases hPB : P = .B
          · subst P; simp [s_upd, hvS] at hvB
          · rw [hst_ne (Ne.symm hPB)]; exact hvB
        · intro Q ss' h1 hsQ hvSQ
          by_cases hQ : Q = P
          · subst Q
            simp only [s', GameState.record, Function.update_self, st'] at h1 hsQ
            simpa [s', s_upd, GameState.record, st'] using
              hm.vS_inl_cache P ss (by simpa [s_upd] using h1) (by simpa [s_upd] using hsQ)
                (by simp [s_upd, hvS])
          · rw [hst_ne hQ] at h1 hsQ hvSQ ⊢
            exact hm.vS_inl_cache Q ss' h1 hsQ hvSQ
        · intro Q τ h1 hc0
          by_cases hQ : Q = P
          · subst Q; simpa [s', GameState.record, st', s_upd] using hm.vR_none_of_cache_none P τ h1 hc0
          · rw [hst_ne hQ]; exact hm.vR_none_of_cache_none Q τ h1 hc0
        · refine ⟨?_, hm.slot_canon.2.1, ?_, hm.slot_canon.2.2.2.1, ?_⟩
          · intro Q idx hvQ
            by_cases hQ : Q = P
            · subst Q; simp [s', GameState.record, st'] at hvQ
            · rw [hst_ne hQ] at hvQ; exact hm.slot_canon.1 Q idx hvQ
          · intro Q τ idx hvrQ
            by_cases hQ : Q = P
            · subst Q; exact hm.slot_canon.2.2.1 P τ idx (by simpa [s', GameState.record, st', s_upd] using hvrQ)
            · rw [hst_ne hQ] at hvrQ; exact hm.slot_canon.2.2.1 Q τ idx hvrQ
          · intro τ Tc σc kV idx rs hc_eq
            have h0 := hm.slot_canon.2.2.2.2 τ Tc σc kV idx rs hc_eq
            by_cases hrec : Party.receiverOf τ = P
            · rw [hrec] at h0 ⊢; simpa [s', GameState.record, st', s_upd] using h0
            · rw [hst_ne hrec]; exact h0
        · intro Q idx hvQ hsQ
          by_cases hQ : Q = P
          · subst Q; simp [s', GameState.record, st'] at hvQ
          · rw [hst_ne hQ] at hvQ hsQ
            simpa [s', GameState.record, Function.update_of_ne hQ] using hm.idx_sync Q idx hvQ hsQ
        · intro r hr hv_r hle_r hcache_or
          simp only [s', GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr0
          · dsimp only [recE] at hv_r hle_r hcache_or
            rcases hcache_or with h0 | ⟨Tc, σc, kV, hc_some⟩
            · have hPB : P = .B := by
                have := hsender; rw [h0] at this; exact this.symm
              subst P
              rw [h0] at hv_r
              have hvB := hm.vS0_init h0 hv_r
              simp [s_upd, hvS] at hvB
            · have hge1 : 1 ≤ s₁.epoch P :=
                (hact.sync.cache_epoch _ (by simp [hc_some])).1
              rcases hm.vS_inl_cache P ss (by simp [s_upd, htcur, hge1])
                (by simp [s_upd, htcur, hsends]) (by simp [s_upd, hvS]) with ⟨_, _, _, hc_none⟩
              dsimp only [s_upd] at hc_none
              simp only [Function.update_self, htcur] at hc_none
              rw [hc_some] at hc_none
              exact nomatch hc_none
          · exact hm.trans_idx r hr0 hv_r hle_r hcache_or
        · intro idx x hx
          rcases hm.fsTrans_sub idx x hx with ⟨hb, r0, hr0, hp0, hc0, hi0⟩
          exact ⟨hb, r0, List.mem_cons_of_mem _ hr0, hp0, hc0, hi0⟩
        · intro τ hle_τ hv_τ hinl
          have hinl0 : (∃ Tc σc kV, h_mid.cache τ = some (Tc, σc, kV, none)) ∨
              (∃ rs, (s_upd.st (Party.receiverOf τ)).vR τ = some (.inl rs)) := by
            rcases hinl with hL | ⟨rs, hR⟩
            · exact Or.inl hL
            · refine Or.inr ⟨rs, ?_⟩
              by_cases hrec : Party.receiverOf τ = P
              · rw [hrec] at hR ⊢; simpa [s', GameState.record, st', s_upd] using hR
              · rw [hst_ne hrec] at hR; exact hR
          rcases hm.inl_comp τ hle_τ hv_τ hinl0 with ⟨cur, hcur, hlt, hbr⟩
          refine ⟨cur, hcur, hlt, ?_⟩
          rcases hbr with hlt' | ⟨hle', hc⟩
          · exact Or.inl hlt'
          · refine Or.inr ⟨hle', fun r hr heq_ep => ?_⟩
            simp only [s', GameState.record, List.mem_cons] at hr
            rcases hr with rfl | hr0
            · dsimp only [recE] at heq_ep
              have hnh : s₁.safeCh 3 P = false :=
                hact.wf.not_healedBy_of_mem_leaks hcur (by simpa [← heq_ep] using hle')
              simp [s', GameState.record, hnh]
            · have hc0 := hc r hr0 heq_ep
              dsimp only [s', GameState.record]
              split_ifs
              · exact hc0
              · exact List.mem_cons_of_mem _ hc0
        · intro idx c hsc
          rcases hm.sc_comp idx c hsc with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
          refine ⟨hsl, hv, hle, cur, hcur, hlt, ?_⟩
          rcases hbr with hlt' | ⟨hle', hc⟩
          · exact Or.inl hlt'
          · refine Or.inr ⟨hle', fun r hr heq_ep hci => ?_⟩
            simp only [s', GameState.record, List.mem_cons] at hr
            rcases hr with rfl | hr0
            · dsimp only [recE] at heq_ep
              have hnh : s₁.safeCh 3 P = false :=
                hact.wf.not_healedBy_of_mem_leaks hcur (by simpa [← heq_ep] using hle')
              simp [s', GameState.record, hnh]
            · have hc0 := hc r hr0 heq_ep hci
              dsimp only [s', GameState.record]
              split_ifs
              · exact hc0
              · exact List.mem_cons_of_mem _ hc0
    | inr sIdx =>
      simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
      let cond := !(s₁.safeCh 3 P) && !((h_mid.book sIdx).getD {}).sCorr
      refine S.bind (lazy_cs_hoare S cond sIdx h_mid) fun ⟨ok, h1⟩ => ?_
      cases ok with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
        exact S.pure _ fun _ _ _ => trivial
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc]
        refine S.bind (S.tr sIdx hdr m h1) fun ⟨e?, h2⟩ => ?_
        cases e? with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact S.pure _ fun _ _ _ => trivial
        | some e =>
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, bind_assoc]
          refine S.pure _ fun ns' sc' ⟨hh2, ns, sc1,
              ⟨sc0, hact, hc1, hs1, hcnt1, hftr1, hbne1, hc_false, _, hc_true⟩,
              hsc_eq, htr_br⟩ => ?_
          subst h2; subst sc1
          rcases htr_br with ⟨h, _⟩ | ⟨ct0, he_eq, hns'⟩
          · exact nomatch h
          cases he_eq
          have htcur : s_mid.tcur = s₁.epoch P := by simpa [s_upd] using hact.wf.vp_tcur P
          have hvSr := hact.sync.vS_inr P sIdx (by simp [s_upd, hvS])
          have hep_sIdx : slotEpoch (q + 1) gMain tL sIdx = s₁.epoch P := by
            have := (hvSr.2.2.2.2.1 (by simpa [s_upd, htcur] using hsends)).1
            simpa [s_upd, htcur] using this
          let b1 := (h1.book sIdx).getD {}
          let cnt' := b1.fsCount + 1
          let b' : FSMultiBook T (ℕ × C) :=
            { b1 with fsCount := cnt', fsTrans := (cnt', hdr, (ns sIdx + 1, ct0)) :: b1.fsTrans }
          let h' : FSMultiBucketAuthState T RSt K I (ℕ × C) :=
            { h1 with book := Function.update h1.book sIdx (some b') }
          have hst'_eq : ({ s_mid with vS := some (Sum.inr sIdx : SS ⊕ ℕ) } :
              VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) = s_mid := by
            cases s_mid; simp at hvS ⊢; exact hvS.symm
          let ct : Header T × (ℕ × C) := (hdr, (ns sIdx + 1, ct0))
          let recE : Record M (Header T × (ℕ × C)) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          let s' := s₁.record 3 P s_mid recE false
          change ActiveInv q qep rem gMain tL par
            { g := s₁.record 3 P { s_mid with vS := some (Sum.inr sIdx) } recE false,
              h := h', abort := false } none ns' sc'
          rw [hst'_eq]
          change ActiveInv q qep rem gMain tL par { g := s', h := h', abort := false } none ns' sc'
          refine ⟨rfl, hact.no_win, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · intro τ; dsimp only [h']; rw [hs1]; exact hact.sess τ
          · refine ⟨?_, ?_, ?_, ?_, hact.wf.tL_eq⟩
            · intro Q; exact hact.wf.vp_id Q
            · intro Q; exact hact.wf.vp_tcur Q
            · intro Q hsQ; exact hact.wf.vp_vS_some Q hsQ
            · intro r hr
              simp only [s', GameState.record, List.mem_cons] at hr
              rcases hr with rfl | hr0
              · exact ⟨htcur, hsender.symm, by simp [recE, s', GameState.record]⟩
              · exact hact.wf.trans_wf r hr0
          · -- `SlotSync`
            have hhdr_same : ∀ hd, isHonestHdrMultiBucket h' hd = isHonestHdrMultiBucket h_mid hd := by
              intro hd; unfold isHonestHdrMultiBucket; dsimp only [h']; rw [hc1]
            refine ⟨fun τ hc => hact.sync.cache_epoch τ (by simpa [h', hc1] using hc),
              fun τ Tc σc kV idx hc => hact.sync.cache_inr τ Tc σc kV idx (by simpa [h', hc1] using hc),
              ?_, ?_⟩
            · intro Q idx hvQ
              have hv0 := hact.sync.vS_inr Q idx hvQ
              refine ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1, fun hsQ => ?_, fun hgm => ?_⟩
              · rcases hv0.2.2.2.2.1 hsQ with ⟨h1', h2'⟩
                exact ⟨h1', h2'.imp id (fun hh => by rw [hhdr_same]; exact hh)⟩
              · rcases hv0.2.2.2.2.2 hgm with h0 | ⟨Tc, σc, kV, hc⟩
                · exact Or.inl h0
                · exact Or.inr ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩
            · intro Q τ idx hvrQ
              have hv0 := hact.sync.vR_inr Q τ idx hvrQ
              refine ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1, fun hgm => ?_⟩
              rcases hv0.2.2.2.2 hgm with h0 | ⟨Tc, σc, kV, hc⟩
              · exact Or.inl h0
              · exact Or.inr ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩
          · -- `ForgedInv`
            intro hgf; subst hgf
            have hf := hact.forged rfl
            refine ⟨?_, ?_⟩
            · intro idx x hx
              have hhdr_eq : isHonestHdrMultiBucket h' x.2.1 = isHonestHdrMultiBucket h_mid x.2.1 := by
                unfold isHonestHdrMultiBucket; dsimp only [h']; rw [hc1]
              rw [hhdr_eq]
              by_cases hi : idx = sIdx
              · subst idx
                simp only [h', Function.update_self, Option.getD_some, b', List.mem_cons] at hx
                rcases hx with rfl | hx0
                · have hge1 := hvSr.2.2.2.1 rfl
                  rcases (hvSr.2.2.2.2.1 (by simpa [s_upd, htcur] using hsends)).2 with h0 | hhdr
                  · simp [s_upd, htcur] at h0; rw [hep_sIdx, h0] at hge1; omega
                  · simpa [s_upd, hdr] using hhdr
                · rw [hftr1 sIdx] at hx0; exact hf.hdr_honest sIdx x hx0
              · simp only [h', Function.update_of_ne hi, hftr1 idx] at hx
                exact hf.hdr_honest idx x hx
            · intro idx hsc_ne
              cases hcond : cond with
              | false =>
                rw [(hc_false hcond).2.2] at hsc_ne
                exact hf.sc_not_healed idx hsc_ne
              | true =>
                rw [(hc_true trivial hcond).1] at hsc_ne
                by_cases hi : idx = sIdx
                · subst idx
                  simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hcond
                  rw [hep_sIdx]; exact hcond.1
                · simp only [Function.update_of_ne hi] at hsc_ne
                  exact hf.sc_not_healed idx hsc_ne
          · -- `MainInv`
            intro hgt; subst hgt
            have hm := hact.main rfl
            have hsl_sIdx : sIdx = slotOf q tL (s₁.epoch P) := by
              have := hm.slot_canon.1 P sIdx (by simp [s_upd, hvS])
              rwa [hep_sIdx] at this
            have his_P := hm.idx_sync P sIdx (by simp [s_upd, hvS])
              (by simpa [s_upd, htcur] using hsends)
            have hcnt_eq : cnt' = ns sIdx + 1 := by
              dsimp only [cnt', b1]; rw [hcnt1 sIdx, his_P.2]
            have hidx_eq : s₁.idx P + 1 = ns sIdx + 1 := by
              have : s₁.idx P = ns sIdx := his_P.1; omega
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro τ h1_τ htH hlt
              have hne_τ : τ ≠ s₁.epoch P := by
                intro heq; subst τ; rw [hsender] at hlt
                dsimp only [s', GameState.record] at hlt; omega
              have hne_s : slotOf q tL τ ≠ sIdx := by
                rw [hsl_sIdx]
                exact fun heq => hne_τ (slotOf_inj htH
                  (healEpoch_le_of_validGuess (by simpa [hep_sIdx] using hvSr.2.1)) heq)
              have hf := hm.fresh_above τ h1_τ htH hlt
              refine ⟨by rw [hns', Function.update_of_ne hne_s]; exact hf.1, ?_, ?_,
                by dsimp only [h']; rw [hs1]; exact hf.2.2.2⟩
              · cases hcond : cond with
                | false => rw [(hc_false hcond).2.2]; exact hf.2.1
                | true => rw [(hc_true trivial hcond).1, Function.update_of_ne hne_s]; exact hf.2.1
              · dsimp only [h']; rw [Function.update_of_ne hne_s, hbne1 _ hne_s]; exact hf.2.2.1
            · intro hv0; exact hm.vR0_init hv0
            · intro hB0 hv0; exact hm.vS0_init hB0 hv0
            · intro Q ss' h1_Q hsQ hvSQ
              rcases hm.vS_inl_cache Q ss' h1_Q hsQ hvSQ with ⟨Tc, σc, kV, hc0⟩
              exact ⟨Tc, σc, kV, by dsimp only [h']; rw [hc1]; exact hc0⟩
            · intro Q τ h1_τ hc0
              exact hm.vR_none_of_cache_none Q τ h1_τ (by simpa [h', hc1] using hc0)
            · refine ⟨?_,
                fun τ Tc σc kV idx hc => hm.slot_canon.2.1 τ Tc σc kV idx (by simpa [h', hc1] using hc),
                ?_, ?_, ?_⟩
              · intro Q idx hvQ; exact hm.slot_canon.1 Q idx hvQ
              · intro Q τ idx hvrQ; exact hm.slot_canon.2.2.1 Q τ idx hvrQ
              · intro idx hb_ne
                by_cases hi : idx = sIdx
                · subst idx
                  refine ⟨by rw [hep_sIdx]; exact hsl_sIdx, hvSr.2.1, hvSr.2.2.1, ?_⟩
                  rcases hvSr.2.2.2.2.2 rfl with h0 | ⟨Tc, σc, kV, hc⟩
                  · exact Or.inl h0
                  · exact Or.inr ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩
                · simp only [h', Function.update_of_ne hi, hbne1 _ hi] at hb_ne
                  rcases hm.slot_canon.2.2.2.1 idx hb_ne with ⟨h1', h2', h3', h4'⟩
                  exact ⟨h1', h2', h3', h4'.imp id fun ⟨Tc, σc, kV, hc⟩ =>
                    ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩⟩
              · intro τ Tc σc kV idx rs hc
                exact hm.slot_canon.2.2.2.2 τ Tc σc kV idx rs (by simpa [h', hc1] using hc)
            · -- `idx_sync`
              intro Q idx hvQ hsQ
              by_cases hQ : Q = P
              · subst Q
                have hidx_eq_sIdx : idx = sIdx := by
                  simp [s', GameState.record, hvS] at hvQ; exact hvQ.symm
                subst idx
                exact ⟨by simp [s', GameState.record, recE, hns', hidx_eq],
                  by simp [h', b', hcnt_eq, hns']⟩
              · have his := hm.idx_sync Q idx hvQ hsQ
                have hne_idx : idx ≠ sIdx := by
                  intro heq; subst idx
                  have hvQ_r := hact.sync.vS_inr Q sIdx hvQ
                  have hepQ := (hvQ_r.2.2.2.2.1 hsQ).1
                  have hsndQ : Party.senderOf (slotEpoch (q + 1) true tL sIdx) = Q := by
                    rw [hepQ]; exact senderOf_eq_of_sendsIn hsQ
                  rw [hep_sIdx, hsender] at hsndQ
                  exact hQ hsndQ.symm
                exact ⟨by dsimp only [s', GameState.record]; rw [Function.update_of_ne hQ, hns',
                    Function.update_of_ne hne_idx]; exact his.1,
                  by simp [h', Function.update_of_ne hne_idx, hcnt1 idx, hns']; exact his.2⟩
            · -- `trans_idx`
              intro r hr hv_r hle_r hcache_or
              simp only [s', GameState.record, List.mem_cons] at hr
              rcases hr with rfl | hr0
              · dsimp only [recE]
                rw [← hsl_sIdx, hns', Function.update_self, hidx_eq]
                exact ⟨Nat.le_refl _, rfl⟩
              · have hcache_or0 : r.pos.epoch = 0 ∨
                    ∃ Tc σc kV, h_mid.cache r.pos.epoch =
                      some (Tc, σc, kV, some (slotOf q tL r.pos.epoch)) :=
                  hcache_or.imp id fun ⟨Tc, σc, kV, hc⟩ => ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩
                rcases hm.trans_idx r hr0 hv_r hle_r hcache_or0 with ⟨h1', h2'⟩
                refine ⟨h1'.trans ?_, h2'⟩
                rw [hns']
                by_cases hs : slotOf q tL r.pos.epoch = sIdx
                · rw [hs, Function.update_self]; omega
                · rw [Function.update_of_ne hs]
            · -- `fsTrans_sub`
              intro idx x hx
              by_cases hi : idx = sIdx
              · subst idx
                simp only [h', Function.update_self, Option.getD_some, b', List.mem_cons] at hx
                refine ⟨by simp [h'], ?_⟩
                rcases hx with rfl | hx0
                · refine ⟨recE, by simp [s', GameState.record], ?_, rfl, hcnt_eq.symm⟩
                  simp [recE, hep_sIdx, hsender, hidx_eq, hcnt_eq]
                · rw [hftr1 sIdx] at hx0
                  rcases hm.fsTrans_sub sIdx x hx0 with ⟨_, r0, hr0, hp0, hc0, hi0⟩
                  exact ⟨r0, List.mem_cons_of_mem _ hr0, hp0, hc0, hi0⟩
              · simp only [h', Function.update_of_ne hi, hftr1 idx] at hx
                rcases hm.fsTrans_sub idx x hx with ⟨hb0, r0, hr0, hp0, hc0, hi0⟩
                exact ⟨by simpa [h', Function.update_of_ne hi, hbne1 _ hi] using hb0,
                  r0, List.mem_cons_of_mem _ hr0, hp0, hc0, hi0⟩
            · -- `inl_comp`
              intro τ hle_τ hv_τ hinl
              have hinl0 : (∃ Tc σc kV, h_mid.cache τ = some (Tc, σc, kV, none)) ∨
                  (∃ rs, (s_upd.st (Party.receiverOf τ)).vR τ = some (.inl rs)) := by
                rcases hinl with ⟨Tc, σc, kV, hc⟩ | ⟨rs, hR⟩
                · exact Or.inl ⟨Tc, σc, kV, by simpa [h', hc1] using hc⟩
                · exact Or.inr ⟨rs, hR⟩
              rcases hm.inl_comp τ hle_τ hv_τ hinl0 with ⟨cur, hcur, hlt, hbr⟩
              refine ⟨cur, hcur, hlt, ?_⟩
              rcases hbr with hlt' | ⟨hle', hc⟩
              · exact Or.inl hlt'
              · refine Or.inr ⟨hle', fun r hr heq_ep => ?_⟩
                simp only [s', GameState.record, List.mem_cons] at hr
                rcases hr with rfl | hr0
                · dsimp only [recE] at heq_ep
                  have hnh : s₁.safeCh 3 P = false :=
                    hact.wf.not_healedBy_of_mem_leaks hcur (by simpa [← heq_ep] using hle')
                  simp [s', GameState.record, hnh]
                · have hc0 := hc r hr0 heq_ep
                  dsimp only [s', GameState.record]
                  split_ifs
                  · exact hc0
                  · exact List.mem_cons_of_mem _ hc0
            · -- `sc_comp`
              intro idx c hsc
              have hsc_mid : (idx = sIdx ∧ cond = true ∧ sc0 sIdx = none ∧ c = ns sIdx) ∨
                  sc0 idx = some c := by
                cases hcond : cond with
                | false => rw [(hc_false hcond).2.2] at hsc; exact Or.inr hsc
                | true =>
                  rw [(hc_true trivial hcond).1] at hsc
                  by_cases hi : idx = sIdx
                  · subst idx
                    simp only [Function.update_self, Option.some.injEq] at hsc
                    cases hsc0_v : sc0 sIdx with
                    | some c0 => rw [hsc0_v] at hsc; exact Or.inr (congrArg some hsc)
                    | none => rw [hsc0_v] at hsc; exact Or.inl ⟨rfl, rfl, rfl, hsc.symm⟩
                  · simp only [Function.update_of_ne hi] at hsc
                    exact Or.inr hsc
              rcases hsc_mid with ⟨rfl, hcond_t, _, rfl⟩ | hsc0_eq
              · simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hcond_t
                have hh_t0 : healedBy tL 3 (s₁.epoch P) = true := by
                  have hv := hvSr.2.1; rw [hep_sIdx] at hv
                  simp only [validGuessBucketParAuth, lastLeakGuessAdmissible, Bool.and_eq_true] at hv
                  exact hv.1
                rcases leak_witness_of_not_healedBy_s hact.wf hcond_t.1 hh_t0 with ⟨cur, hcur, hlt⟩
                refine ⟨by rw [hep_sIdx]; exact hsl_sIdx, hvSr.2.1, hvSr.2.2.1, cur, hcur, hlt, ?_⟩
                by_cases hlt_c : cur < slotEpoch (q + 1) true tL idx
                · exact Or.inl hlt_c
                · refine Or.inr ⟨Nat.le_of_not_lt hlt_c, fun r hr heq_ep hlt_idx => ?_⟩
                  simp only [s', GameState.record, List.mem_cons] at hr
                  rcases hr with rfl | hr0
                  · simp [s', GameState.record, hcond_t.1]
                  · have hcache_or0 : r.pos.epoch = 0 ∨
                        ∃ Tc σc kV, h_mid.cache r.pos.epoch =
                          some (Tc, σc, kV, some (slotOf q tL r.pos.epoch)) := by
                      have hslot_eq : slotOf q tL r.pos.epoch = idx := by
                        rw [heq_ep, hep_sIdx, ← hsl_sIdx]
                      rw [hslot_eq, heq_ep]
                      exact hvSr.2.2.2.2.2 rfl
                    have hri := hm.trans_idx r hr0 (by simpa [heq_ep] using hvSr.2.1)
                      (by simpa [heq_ep] using hvSr.2.2.1) hcache_or0
                    rw [heq_ep, hep_sIdx, ← hsl_sIdx] at hri
                    omega
              · rcases hm.sc_comp idx c hsc0_eq with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
                refine ⟨hsl, hv, hle, cur, hcur, hlt, ?_⟩
                rcases hbr with hlt' | ⟨hle', hc⟩
                · exact Or.inl hlt'
                · refine Or.inr ⟨hle', fun r hr heq_ep hci => ?_⟩
                  simp only [s', GameState.record, List.mem_cons] at hr
                  rcases hr with rfl | hr0
                  · dsimp only [recE] at heq_ep
                    have hnh : s₁.safeCh 3 P = false :=
                      hact.wf.not_healedBy_of_mem_leaks hcur (by simpa [← heq_ep] using hle')
                    simp [s', GameState.record, hnh]
                  · have hc0 := hc r hr0 heq_ep hci
                    dsimp only [s', GameState.record]
                    split_ifs
                    · exact hc0
                    · exact List.mem_cons_of_mem _ hc0
 
theorem i1_send_active_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (m : M) (r : Option CCoins)
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par st.1 st.2)
      (fun p ns' sc' => FalseInv q qep rem gMain tL par p.2 ns' sc')
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL
        (.inr (.inl (.inl (.inl (.inl ⟨P, m, r⟩)))))).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  dsimp only [implFSMultiBucketAuth, HAdd.hAdd, Add.add, QueryImpl.add]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hguard
  · simp only [StateT.run_pure]
    exact S.pure _ fun _ _ hact => Or.inr ⟨hact.no_abort, hact.no_win, hact.winEp_none,
      sessBound_mono_noop hact.sess rfl, hact.wf, hact.sync, hact.forged, hact.main⟩
  · cases hep : es0.g.epMgmt 3 qep P r.isSome with
    | none =>
      simp only [StateT.run_pure]
      exact S.pure _ fun _ _ hact => Or.inr ⟨hact.no_abort, hact.no_win, hact.winEp_none,
        sessBound_mono_noop hact.sess rfl, hact.wf, hact.sync, hact.forged, hact.main⟩
    | some s₁ =>
      cases winEp0 with
      | some w =>
        exact S.conseq S.exfalso (fun _ _ hact => nomatch hact.winEp_none) (fun _ _ _ h => h)
      | none =>
        have hvSend : vSend hk s₁ P (s₁.st P) m none r =
            (show _root_.CryptoGames.SM.Engine.HM (FSMultiSpec SS RS T M (ℕ × C))
                (FSMultiBucketAuthState T RSt K I (ℕ × C)) _ from do
              let s₁? ← (if (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) then do
                  match ← hk.startSend s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r with
                  | none => Pure.pure none
                  | some (γ', T', σ', ss) =>
                    Pure.pure (some { s₁.st P with tcur := (s₁.st P).tcur + 1, γ := γ',
                                                   curCkaMsg := some T', root := σ', vS := some ss })
                else Pure.pure (some (s₁.st P)))
              match s₁? with
              | none => Pure.pure none
              | some s_mid =>
                let hdr : Header T := (s_mid.tcur, s_mid.curCkaMsg)
                match s_mid.vS with
                | none => Pure.pure (some (s_mid, (hdr, default)))
                | some v => do
                  match ← hk.fsSend s₁ P s_mid.tcur v hdr m none with
                  | none => Pure.pure none
                  | some (v', e) => Pure.pure (some ({ s_mid with vS := some v' }, (hdr, e)))) := by
          unfold vSend
          by_cases hc : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = true
          · simp only [hc, ↓reduceIte, bind_assoc]
            congr 1; funext x
            rcases x with _ | ⟨γ', T', σ', ss⟩
            · simp [pure_bind]
            · simp only [pure_bind]
              congr 1; funext y; rcases y with _ | ⟨v', e⟩ <;> rfl
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind]
            cases (s₁.st P).vS with
            | none => rfl
            | some v =>
              dsimp only
              congr 1; funext y; rcases y with _ | ⟨v', e⟩ <;> rfl
        dsimp only
        rw [hvSend]
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc]
        refine S.bind
          (startSend_or_same_hoare S q qep rem cka prng fs gMain tL par P r es0 s₁ hep)
          fun ⟨s_mid?, h_mid⟩ => ?_
        cases s_mid? with
        | none =>
          simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_set]
          exact S.pure _ fun _ _ _ => Or.inl ⟨Or.inl rfl, fun _ h => nomatch h⟩
        | some s_mid =>
          have hab0 : es0.abort = false := by
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
            exact hguard.1
          refine S.conseq
            (S.and_prop (s₁.epoch P ≤ qep ∧ P.sendsIn (s₁.epoch P) = true) fun ⟨hqep_le, hsends⟩ =>
              S.bind (fsSend_record_hoare S q qep rem cka prng fs gMain tL par
                  P m s₁ s_mid h_mid hqep_le hsends)
                fun ⟨res, h'⟩ => ?_)
            (fun _ _ ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩)
            (fun _ _ _ h => h)
          cases res with
          | none =>
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]
            exact S.pure _ fun _ _ _ => Or.inl ⟨Or.inl rfl, fun _ h => nomatch h⟩
          | some pOut =>
            rcases pOut with ⟨st', ct⟩
            simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]
            exact S.pure _ fun _ _ hact' => by dsimp only; rw [hab0]; exact Or.inr hact'

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseSend
