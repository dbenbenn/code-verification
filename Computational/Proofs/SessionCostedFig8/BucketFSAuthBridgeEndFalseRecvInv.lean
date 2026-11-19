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
# State-Invariant Preservation Helpers for `vRecv` and `accept` (`la = false`)

Provides pure `ActiveInv` preservation lemmas across `startRecv` epoch advancement,
`lazy_cs_hoare` sender corruption, and `GameState.accept` (`inl` and `inr` receiver branches).-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecvInv

public section

set_option autoImplicit false

open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM (Pos GameState healedBy lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (Header healEpoch)
open _root_.CryptoGames.SM.Engine (VP Ctx EState)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState validGuessBucketParAuth isHonestHdrMultiBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase (
  slotEpoch slotOf healEpoch_le_of_validGuess slotOf_inj
  SessBound sessBound_mono_noop EngineWF leak_witness_of_not_healedBy_s
  SlotSync ForgedInv MainInv ActiveInv)

theorem party_recv_of_sendsIn_false {P : Party} {t : ℕ}
    (h : P.sendsIn t = false) :
    P.other.sendsIn t = true ∧ Party.senderOf t = P.other ∧ Party.receiverOf t = P := by
  cases P <;>
    simp only [Party.other, Party.sendsIn, Party.senderOf, Party.receiverOf] at h ⊢ <;>
    split_ifs at h ⊢ <;> simp_all

theorem activeInv_s_upd_of_startRecv
    {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {P : Party} {t : ℕ} {γ' : Γ} {σ' : RSt} {rsv : RS ⊕ ℕ}
    {es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))}
    {h_mid : FSMultiBucketAuthState T RSt K I (ℕ × C)}
    {ns : ℕ → ℕ} {sc : ℕ → Option ℕ}
    (hact : ActiveInv q qep (rem + 1) gMain tL par es0 none ns sc)
    (hsends_f : P.sendsIn t = false)
    (ht_eq : t = es0.g.epoch P + 1)
    (hsess : SessBound q gMain rem h_mid)
    (hcache_eq : h_mid.cache = es0.h.cache)
    (hbook_eq : h_mid.book = es0.h.book)
    (hsess_eq_main : gMain = true → h_mid.sessions = es0.h.sessions)
    (hrsv_main : gMain = true → ∃ Tc σc kVal optIdx,
      es0.h.cache t = some (Tc, σc, kVal, optIdx) ∧
      ((optIdx = none ∧ ∃ rs, rsv = .inl rs) ∨
       (∃ sIdx, optIdx = some sIdx ∧ rsv = .inr sIdx)))
    (hrsv_forged_inr : ∀ sIdx, gMain = false → rsv = .inr sIdx →
      slotEpoch (q + 1) false tL sIdx = t ∧
      validGuessBucketParAuth 1 tL par t = true ∧ t ≤ qep + 1) :
    let s := es0.g
    let s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
      { s.st P with tcur := t, γ := γ', root := σ',
                    vR := Function.update (s.st P).vR t (some rsv) }
    let s_upd := { s with st := Function.update s.st P s_mid,
                          epoch := Function.update s.epoch P (max (s.epoch P) t) }
    ActiveInv q qep rem gMain tL par { es0 with h := h_mid } none ns sc ∧
    ActiveInv q qep rem gMain tL par { g := s_upd, h := h_mid, abort := false } none ns sc := by
  intro s s_mid s_upd
  have ht_ge1 : 1 ≤ t := by omega
  have hmax_eq : max (s.epoch P) t = t := by dsimp only [s]; omega
  have ⟨_, _, hrecv_t⟩ := party_recv_of_sendsIn_false hsends_f
  have hhon_eq : ∀ hdr, isHonestHdrMultiBucket h_mid hdr = isHonestHdrMultiBucket es0.h hdr := by
    intro hdr; simp [isHonestHdrMultiBucket, hcache_eq]
  have hact_s : ActiveInv q qep rem gMain tL par { es0 with h := h_mid } none ns sc := by
    refine ⟨hact.no_abort, hact.no_win, rfl, hsess, hact.wf, ?_, ?_, ?_⟩
    · refine ⟨fun τ hs => hact.sync.cache_epoch τ (by simpa [hcache_eq] using hs),
        fun τ Tc σc kV sIdx hc =>
          hact.sync.cache_inr τ Tc σc kV sIdx (by simpa [hcache_eq] using hc),
        fun Q sIdx hv => ?_, fun Q τ sIdx hv => ?_⟩
      · have hv0 := hact.sync.vS_inr Q sIdx hv
        exact ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1,
          fun hsQ => ⟨(hv0.2.2.2.2.1 hsQ).1, by rw [hhon_eq]; exact (hv0.2.2.2.2.1 hsQ).2⟩,
          fun hgt => by simpa [hcache_eq] using hv0.2.2.2.2.2 hgt⟩
      · have hv0 := hact.sync.vR_inr Q τ sIdx hv
        exact ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1,
          fun hgt => by simpa [hcache_eq] using hv0.2.2.2.2 hgt⟩
    · intro hgf
      have hf := hact.forged hgf
      refine ⟨fun idx x hx => ?_, hf.sc_not_healed⟩
      rw [hhon_eq]
      exact hf.hdr_honest idx x (by simpa [hbook_eq] using hx)
    · intro hgt
      have hm := hact.main hgt
      have hsess_eq := hsess_eq_main hgt
      refine ⟨?_, hm.vR0_init, hm.vS0_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.sc_comp⟩
      · intro τ h1 htH hlt
        simpa [hbook_eq, hsess_eq] using hm.fresh_above τ h1 htH hlt
      · intro Q ss h1 hsQ hvQ
        simpa [hcache_eq] using hm.vS_inl_cache Q ss h1 hsQ hvQ
      · intro Q τ h1 hcn
        exact hm.vR_none_of_cache_none Q τ h1 (by simpa [hcache_eq] using hcn)
      · refine ⟨hm.slot_canon.1,
          fun τ Tc σc kV sIdx hc =>
            hm.slot_canon.2.1 τ Tc σc kV sIdx (by simpa [hcache_eq] using hc),
          hm.slot_canon.2.2.1,
          fun idx hb => by
            simpa [hcache_eq] using hm.slot_canon.2.2.2.1 idx (by simpa [hbook_eq] using hb),
          fun τ Tc σc kV sIdx rs hc =>
            hm.slot_canon.2.2.2.2 τ Tc σc kV sIdx rs (by simpa [hcache_eq] using hc)⟩
      · intro Q sIdx hvQ hsQ
        simpa [hbook_eq] using hm.idx_sync Q sIdx hvQ hsQ
      · intro r hr hv hle hcor
        exact hm.trans_idx r hr hv hle (by simpa [hcache_eq] using hcor)
      · intro idx x hx
        simpa [hbook_eq] using hm.fsTrans_sub idx x (by simpa [hbook_eq] using hx)
      · intro τ hle hv hdisj
        exact hm.inl_comp τ hle hv (by simpa [hcache_eq] using hdisj)
  refine ⟨hact_s, rfl, hact.no_win, rfl, hsess, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, hact.wf.tL_eq⟩
    · intro Q; by_cases hQP : Q = P
      · subst hQP; simpa [s_upd, s_mid] using hact.wf.vp_id Q
      · simpa [s_upd, Function.update_of_ne hQP] using hact.wf.vp_id Q
    · intro Q; by_cases hQP : Q = P
      · subst hQP; simp [s_upd, s_mid, hmax_eq]
      · simpa [s_upd, Function.update_of_ne hQP] using hact.wf.vp_tcur Q
    · intro Q hsQ
      by_cases hQP : Q = P
      · subst hQP; simp [s_upd, s_mid, hsends_f] at hsQ
      · simpa [s_upd, Function.update_of_ne hQP] using
          hact.wf.vp_vS_some Q (by simpa [s_upd, Function.update_of_ne hQP] using hsQ)
    · intro r hr
      have htw := hact.wf.trans_wf r hr
      refine ⟨htw.1, htw.2.1, htw.2.2.trans ?_⟩
      by_cases hQP : r.pos.sender = P
      · rw [hQP]; simp [s_upd]; omega
      · simp [s_upd, s, Function.update_of_ne hQP]
  · refine ⟨?_, hact_s.sync.cache_inr, ?_, ?_⟩
    · intro τ hs
      rcases hact_s.sync.cache_epoch τ hs with ⟨h1, hle⟩
      refine ⟨h1, hle.trans ?_⟩
      by_cases hQP : Party.senderOf τ = P
      · rw [hQP]; simp [s_upd]; omega
      · simp [s_upd, s, Function.update_of_ne hQP]
    · intro Q sIdx hvQ
      by_cases hQP : Q = P
      · subst hQP
        simp only [s_upd, s_mid, Function.update_self] at hvQ ⊢
        have hv0 := hact_s.sync.vS_inr Q sIdx hvQ
        have htcur0 : (s.st Q).tcur ≤ t := by rw [hact.wf.vp_tcur Q]; omega
        exact ⟨hv0.1.trans htcur0, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1,
          fun hsQ => absurd hsQ (by simp [hsends_f]), hv0.2.2.2.2.2⟩
      · simpa [s_upd, Function.update_of_ne hQP] using
          hact_s.sync.vS_inr Q sIdx (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
    · intro Q τ sIdx hvQ
      by_cases hQP : Q = P
      · subst hQP
        simp only [s_upd, s_mid, Function.update_self] at hvQ
        by_cases hτ : τ = t
        · subst hτ
          simp only [Function.update_self, Option.some.injEq] at hvQ
          cases hgm : gMain with
          | false =>
            rcases hrsv_forged_inr sIdx hgm hvQ with ⟨hsl, hv, hle⟩
            exact ⟨hsl, hv, hle, hrecv_t.symm, fun h => nomatch h⟩
          | true =>
            rcases hrsv_main hgm with ⟨Tc, σc, kV, optIdx, hc, hopt⟩
            rcases hopt with ⟨_, rs, hrs⟩ | ⟨sIdx₀, rfl, hrs⟩
            · rw [hrs] at hvQ; exact nomatch hvQ
            · cases hvQ.symm.trans hrs
              have hci := hact.sync.cache_inr τ Tc σc kV sIdx hc
              rw [hgm] at hci
              exact ⟨hci.1, hci.2.1, hci.2.2, hrecv_t.symm,
                fun _ => Or.inr ⟨Tc, σc, kV, by rw [hcache_eq]; exact hc⟩⟩
        · simp only [Function.update_of_ne hτ] at hvQ
          exact hact_s.sync.vR_inr Q τ sIdx hvQ
      · simpa [s_upd, Function.update_of_ne hQP] using
          hact_s.sync.vR_inr Q τ sIdx (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
  · intro hgf
    have hf := hact_s.forged hgf
    exact ⟨hf.1, hf.2⟩
  · intro hgt
    have hm := hact_s.main hgt
    rcases hrsv_main hgt with ⟨Tc, σc, kV, optIdx, hc_es0, hopt⟩
    have hc_mid : h_mid.cache t = some (Tc, σc, kV, optIdx) := by rw [hcache_eq]; exact hc_es0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.trans_idx, hm.fsTrans_sub, ?_, hm.sc_comp⟩
    · intro τ h1 htH hlt
      apply hm.fresh_above τ h1 htH
      have hle_ep : s.epoch (Party.senderOf τ) ≤ s_upd.epoch (Party.senderOf τ) := by
        by_cases hQP : Party.senderOf τ = P
        · rw [hQP]; simp [s_upd]
        · simp [s_upd, Function.update_of_ne hQP]
      dsimp only [s] at hlt hle_ep ⊢; omega
    · intro hv0
      by_cases hPA : P = .A
      · subst hPA
        have h0ne : (0 : ℕ) ≠ t := by omega
        simpa [s_upd, s_mid, Function.update_of_ne h0ne] using hm.vR0_init hv0
      · have hAP : (.A : Party) ≠ P := fun h => hPA h.symm
        simpa [s_upd, Function.update_of_ne hAP] using hm.vR0_init hv0
    · intro hepB hv0
      by_cases hPB : P = .B
      · subst hPB; simp [s_upd, hmax_eq] at hepB; omega
      · have hBP : (.B : Party) ≠ P := fun h => hPB h.symm
        simpa [s_upd, Function.update_of_ne hBP] using
          hm.vS0_init (by simpa [s_upd, Function.update_of_ne hBP] using hepB) hv0
    · intro Q ss h1 hsQ hvQ
      by_cases hQP : Q = P
      · subst hQP; simp [s_upd, s_mid, hsends_f] at hsQ
      · simpa [s_upd, s, Function.update_of_ne hQP] using
          hm.vS_inl_cache Q ss (by simpa [s_upd, Function.update_of_ne hQP] using h1)
            (by simpa [s_upd, Function.update_of_ne hQP] using hsQ)
            (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
    · intro Q τ h1 hcn
      by_cases hQP : Q = P
      · subst hQP
        simp only [s_upd, s_mid, Function.update_self]
        by_cases hτ : τ = t
        · subst hτ; simp [hc_mid] at hcn
        · simp only [Function.update_of_ne hτ]; exact hm.vR_none_of_cache_none Q τ h1 hcn
      · simpa [s_upd, Function.update_of_ne hQP] using hm.vR_none_of_cache_none Q τ h1 hcn
    · refine ⟨?_, hm.slot_canon.2.1, ?_, hm.slot_canon.2.2.2.1, ?_⟩
      · intro Q sIdx hvQ
        by_cases hQP : Q = P
        · subst hQP; exact hm.slot_canon.1 Q sIdx (by simpa [s_upd, s_mid] using hvQ)
        · exact hm.slot_canon.1 Q sIdx (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
      · intro Q τ sIdx hvQ
        by_cases hQP : Q = P
        · subst hQP
          simp only [s_upd, s_mid, Function.update_self] at hvQ
          by_cases hτ : τ = t
          · subst hτ
            simp only [Function.update_self, Option.some.injEq] at hvQ
            rcases hopt with ⟨_, rs, hrs⟩ | ⟨sIdx₀, rfl, hrs⟩
            · rw [hrs] at hvQ; exact nomatch hvQ
            · cases hvQ.symm.trans hrs
              exact hm.slot_canon.2.1 τ Tc σc kV sIdx hc_mid
          · simp only [Function.update_of_ne hτ] at hvQ
            exact hm.slot_canon.2.2.1 Q τ sIdx hvQ
        · exact hm.slot_canon.2.2.1 Q τ sIdx
            (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
      · intro τ Tc' σc' kV' sIdx rs hc'
        by_cases hQP : Party.receiverOf τ = P
        · rw [hQP]
          simp only [s_upd, s_mid, Function.update_self]
          by_cases hτ : τ = t
          · subst hτ
            rw [hc_mid] at hc'
            have hopt_eq : optIdx = some sIdx := congrArg (·.2.2.2) (Option.some.inj hc')
            rcases hopt with ⟨hnone, _⟩ | ⟨sIdx₀, hsome, hrs⟩
            · rw [hnone] at hopt_eq; exact nomatch hopt_eq
            · simp [hrs]
          · simp only [Function.update_of_ne hτ]
            rw [← hQP]; exact hm.slot_canon.2.2.2.2 τ Tc' σc' kV' sIdx rs hc'
        · simpa [s_upd, Function.update_of_ne hQP] using
            hm.slot_canon.2.2.2.2 τ Tc' σc' kV' sIdx rs hc'
    · intro Q sIdx hvQ hsQ
      by_cases hQP : Q = P
      · subst hQP; simp [s_upd, s_mid, hsends_f] at hsQ
      · simpa [s_upd] using hm.idx_sync Q sIdx
          (by simpa [s_upd, Function.update_of_ne hQP] using hvQ)
          (by simpa [s_upd, Function.update_of_ne hQP] using hsQ)
    · intro τ hle hv hdisj
      apply hm.inl_comp τ hle hv
      rcases hdisj with hcache | ⟨rs, hvR⟩
      · exact Or.inl hcache
      · by_cases hQP : Party.receiverOf τ = P
        · rw [hQP] at hvR
          simp only [s_upd, s_mid, Function.update_self] at hvR
          by_cases hτ : τ = t
          · subst hτ
            simp only [Function.update_self, Option.some.injEq] at hvR
            rcases hopt with ⟨rfl, _⟩ | ⟨sIdx₀, _, hrs⟩
            · exact Or.inl ⟨Tc, σc, kV, hc_mid⟩
            · rw [hrs] at hvR; exact nomatch hvR
          · simp only [Function.update_of_ne hτ] at hvR
            exact Or.inr ⟨rs, by simpa [hQP] using hvR⟩
        · exact Or.inr ⟨rs, by simpa [s_upd, Function.update_of_ne hQP] using hvR⟩

theorem lazy_cs_preserves_activeInv
    {Γ T RSt K I SS RS M C : Type} [DecidableEq T]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {s_any : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M (ℕ × C)}
    {h0 h1 : FSMultiBucketAuthState T RSt K I (ℕ × C)}
    {ns : ℕ → ℕ} {sc0 sc1 : ℕ → Option ℕ}
    {sIdx t : ℕ} {cond : Bool} {no_abort : Bool}
    (hact : ActiveInv q qep rem gMain tL par { g := s_any, h := h0, abort := no_abort } none ns sc0)
    (hsl_ep : slotEpoch (q + 1) gMain tL sIdx = t)
    (hvg : validGuessBucketParAuth 1 tL par t = true)
    (hle_qep : t ≤ qep + 1)
    (hmain_sIdx : gMain = true → sIdx = slotOf q tL t ∧
      (t = 0 ∨ ∃ Tc σc kVal, h0.cache t = some (Tc, σc, kVal, some sIdx)))
    (hcond_nh : cond = true → healedBy s_any.tL 3 t = false)
    (hcache : h1.cache = h0.cache)
    (hsess : h1.sessions = h0.sessions)
    (hcnt : ∀ idx, ((h1.book idx).getD {}).fsCount = ((h0.book idx).getD {}).fsCount)
    (hftr : ∀ idx, ((h1.book idx).getD {}).fsTrans = ((h0.book idx).getD {}).fsTrans)
    (hbook_ne : ∀ idx, idx ≠ sIdx → h1.book idx = h0.book idx)
    (hcond_f : cond = false → h1 = h0 ∧ sc1 = sc0)
    (hcond_t : cond = true →
      sc1 = Function.update sc0 sIdx (some ((sc0 sIdx).getD (ns sIdx))) ∧
      h1.book sIdx ≠ none) :
    ActiveInv q qep rem gMain tL par { g := s_any, h := h1, abort := no_abort } none ns sc1 := by
  cases hcond : cond with
  | false =>
    rcases hcond_f hcond with ⟨rfl, rfl⟩
    exact hact
  | true =>
    rcases hcond_t hcond with ⟨hsc1, hb_sIdx⟩
    have hnh : healedBy s_any.tL 3 t = false := hcond_nh hcond
    have hhon_eq : ∀ hdr, isHonestHdrMultiBucket h1 hdr = isHonestHdrMultiBucket h0 hdr := by
      intro hdr; simp [isHonestHdrMultiBucket, hcache]
    refine ⟨hact.no_abort, hact.no_win, rfl,
      fun τ => by rw [hsess]; exact hact.sess τ, hact.wf, ?_, ?_, ?_⟩
    · refine ⟨fun τ hs => hact.sync.cache_epoch τ (by simpa [hcache] using hs),
        fun τ Tc σc kV idx hc =>
          hact.sync.cache_inr τ Tc σc kV idx (by simpa [hcache] using hc),
        fun Q idx hv => ?_, fun Q τ idx hv => ?_⟩
      · have hv0 := hact.sync.vS_inr Q idx hv
        exact ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1,
          fun hsQ => ⟨(hv0.2.2.2.2.1 hsQ).1, by rw [hhon_eq]; exact (hv0.2.2.2.2.1 hsQ).2⟩,
          fun hgt => by simpa [hcache] using hv0.2.2.2.2.2 hgt⟩
      · have hv0 := hact.sync.vR_inr Q τ idx hv
        exact ⟨hv0.1, hv0.2.1, hv0.2.2.1, hv0.2.2.2.1,
          fun hgt => by simpa [hcache] using hv0.2.2.2.2 hgt⟩
    · intro hgf
      subst hgf
      have hf := hact.forged rfl
      refine ⟨fun idx x hx => ?_, ?_⟩
      · rw [hhon_eq]; exact hf.hdr_honest idx x (by rw [← hftr]; exact hx)
      · intro idx hsc_ne
        rw [hsc1] at hsc_ne
        by_cases hi : idx = sIdx
        · subst hi; rw [hsl_ep]; exact hnh
        · exact hf.sc_not_healed idx (by simpa [Function.update_of_ne hi] using hsc_ne)
    · intro hgt
      subst hgt
      have hm := hact.main rfl
      rcases hmain_sIdx rfl with ⟨hsl_eq, hcache_or⟩
      have htH_t : healEpoch tL ≤ t := healEpoch_le_of_validGuess hvg
      refine ⟨?_, hm.vR0_init, hm.vS0_init,
        fun Q ss h1 hsQ hvQ => by simpa [hcache] using hm.vS_inl_cache Q ss h1 hsQ hvQ,
        fun Q τ h1 hcn => hm.vR_none_of_cache_none Q τ h1 (by simpa [hcache] using hcn),
        ⟨hm.slot_canon.1,
         fun τ Tc σc kV idx hc => hm.slot_canon.2.1 τ Tc σc kV idx (by simpa [hcache] using hc),
         hm.slot_canon.2.2.1, ?_,
         fun τ Tc σc kV idx rs hc =>
           hm.slot_canon.2.2.2.2 τ Tc σc kV idx rs (by simpa [hcache] using hc)⟩,
        ?_,
        fun r hr hv hle hcor => hm.trans_idx r hr hv hle (by simpa [hcache] using hcor),
        ?_,
        fun τ hle hv hdisj => hm.inl_comp τ hle hv (by simpa [hcache] using hdisj),
        ?_⟩
      · intro τ h1_τ htH hlt
        have hne_τ : τ ≠ t := by
          intro heq; subst heq
          rcases hcache_or with rfl | ⟨Tc, σc, kV, hc⟩
          · omega
          · have := (hact.sync.cache_epoch τ (by simp [hc])).2
            dsimp only at hlt this; omega
        have hne_s : slotOf q tL τ ≠ sIdx := by
          rw [hsl_eq]; exact fun heq => hne_τ (slotOf_inj htH htH_t heq)
        have hf := hm.fresh_above τ h1_τ htH hlt
        exact ⟨hf.1, by rw [hsc1, Function.update_of_ne hne_s]; exact hf.2.1,
          by rw [hbook_ne _ hne_s]; exact hf.2.2.1,
          by rw [hsess]; exact hf.2.2.2⟩
      · intro idx hbne
        by_cases hi : idx = sIdx
        · subst hi; rw [hsl_ep]; exact ⟨hsl_eq, hvg, hle_qep, by simpa [hcache] using hcache_or⟩
        · rw [hbook_ne idx hi] at hbne
          simpa [hcache] using hm.slot_canon.2.2.2.1 idx hbne
      · intro Q idx hvQ hsQ
        have his := hm.idx_sync Q idx hvQ hsQ
        exact ⟨his.1, by rw [hcnt]; exact his.2⟩
      · intro idx x hx
        rw [hftr] at hx
        rcases hm.fsTrans_sub idx x hx with ⟨hb0, hex⟩
        refine ⟨?_, hex⟩
        by_cases hi : idx = sIdx
        · subst hi; exact hb_sIdx
        · rw [hbook_ne idx hi]; exact hb0
      · intro idx c hsc_idx
        rw [hsc1] at hsc_idx
        by_cases hi : idx = sIdx
        · subst idx
          simp only [Function.update_self, Option.some.injEq] at hsc_idx
          cases hsc0_eq : sc0 sIdx with
          | some c0 =>
            rw [hsc0_eq, Option.getD_some] at hsc_idx; subst hsc_idx
            exact hm.sc_comp sIdx c0 hsc0_eq
          | none =>
            rw [hsc0_eq, Option.getD_none] at hsc_idx; subst hsc_idx
            rw [hsl_ep]
            have hh_t : healedBy tL 3 t = true := by
              simp only [validGuessBucketParAuth, lastLeakGuessAdmissible, Bool.and_eq_true] at hvg
              exact hvg.1
            rcases leak_witness_of_not_healedBy_s hact.wf hnh hh_t with ⟨cur, hcur, hlt_cur⟩
            refine ⟨hsl_eq, hvg, hle_qep, cur, hcur, hlt_cur, ?_⟩
            by_cases hlt_t : cur < t
            · exact Or.inl hlt_t
            · refine Or.inr ⟨by omega, fun r hr heq_ep hlt_idx => ?_⟩
              have hcor : r.pos.epoch = 0 ∨ ∃ Tc σc kVal,
                  h0.cache r.pos.epoch = some (Tc, σc, kVal, some (slotOf q tL r.pos.epoch)) := by
                rw [heq_ep, ← hsl_eq]; exact hcache_or
              have hri := hm.trans_idx r hr (by simpa [heq_ep] using hvg)
                (by simpa [heq_ep] using hle_qep) hcor
              rw [heq_ep, ← hsl_eq] at hri
              omega
        · simp only [Function.update_of_ne hi] at hsc_idx
          exact hm.sc_comp idx c hsc_idx

theorem accept_inl_preserves_activeInv
    {Γ T RSt K I SS RS M C : Type} [DecidableEq T] [DecidableEq M] [DecidableEq C]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {P : Party} {t : ℕ} {rs rs' : RS} {pos : Pos}
    {es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))}
    {s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    {h_mid : FSMultiBucketAuthState T RSt K I (ℕ × C)}
    {ns : ℕ → ℕ} {sc : ℕ → Option ℕ}
    (hno_abort : es0.abort = false)
    (hsends_f : P.sendsIn t = false)
    (hvR_mid : s_mid.vR t = some (.inl rs))
    (hpos_ep : pos.epoch = t)
    (hact_upd : ActiveInv q qep rem gMain tL par
      { g := { es0.g with st := Function.update es0.g.st P s_mid,
                          epoch := Function.update es0.g.epoch P (max (es0.g.epoch P) t) },
        h := h_mid, abort := false } none ns sc) :
    let st' := { s_mid with vR := Function.update s_mid.vR t (some (.inl rs')) }
    ActiveInv q qep rem gMain tL par
      { es0 with g := es0.g.accept P st' pos, h := h_mid } none ns sc := by
  intro st'
  let s := es0.g
  let s_upd := { s with st := Function.update s.st P s_mid,
                        epoch := Function.update s.epoch P (max (s.epoch P) t) }
  let s_acc := s.accept P st' pos
  have ⟨_, _, hrecv_t⟩ := party_recv_of_sendsIn_false hsends_f
  have hst_acc : (es0.g.accept P st' pos).st = Function.update es0.g.st P st' := rfl
  have hep_eq : (es0.g.accept P st' pos).epoch =
      Function.update es0.g.epoch P (max (es0.g.epoch P) t) := by
    simp [GameState.accept, GameState.delete, hpos_ep]
  have hidx_eq : s_acc.idx = s_upd.idx := rfl
  have htL_eq : s_acc.tL = s_upd.tL := rfl
  have hleaks_eq : s_acc.leaks = s_upd.leaks := rfl
  have hwin_eq : s_acc.win = s_upd.win := rfl
  have htrans_mem : ∀ r ∈ s_acc.trans, r ∈ s_upd.trans ∧ r.pos ≠ pos := by
    intro r hr
    simp only [s_acc, GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
    exact hr
  have hcomp_iff : ∀ r ∈ s_acc.trans, r.pos ∈ s_acc.comp ↔ r.pos ∈ s_upd.comp := by
    intro r hr
    have hne := (htrans_mem r hr).2
    simp [s_acc, s_upd, GameState.accept, GameState.delete, hne]
  have hvR_inr_eq : ∀ Q τ sIdx, (s_acc.st Q).vR τ = some (.inr sIdx) ↔
      (s_upd.st Q).vR τ = some (.inr sIdx) := by
    intro Q τ sIdx
    by_cases hQP : Q = P
    · subst hQP
      simp only [s_acc, s_upd, st', GameState.accept, GameState.delete, Function.update_self]
      by_cases hτ : τ = t
      · subst hτ; simp [hvR_mid]
      · simp [Function.update_of_ne hτ]
    · simp [s_acc, s_upd, GameState.accept, GameState.delete, Function.update_of_ne hQP]
  refine ⟨hno_abort, by rw [hwin_eq]; exact hact_upd.no_win, rfl, hact_upd.sess, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, by rw [htL_eq, hleaks_eq]; exact hact_upd.wf.tL_eq⟩
    · intro Q; rw [hst_acc]; by_cases hQP : Q = P
      · subst hQP; simpa [st'] using hact_upd.wf.vp_id Q
      · simpa [Function.update_of_ne hQP] using hact_upd.wf.vp_id Q
    · intro Q; rw [hst_acc, hep_eq]; by_cases hQP : Q = P
      · subst hQP; simpa [st'] using hact_upd.wf.vp_tcur Q
      · simpa [Function.update_of_ne hQP] using hact_upd.wf.vp_tcur Q
    · intro Q hsQ; rw [hst_acc] at hsQ ⊢; by_cases hQP : Q = P
      · subst hQP; simpa [st'] using
          hact_upd.wf.vp_vS_some Q (by simpa [st'] using hsQ)
      · simpa [Function.update_of_ne hQP] using
          hact_upd.wf.vp_vS_some Q
            (by simpa [Function.update_of_ne hQP] using hsQ)
    · intro r hr; rw [hep_eq]; exact hact_upd.wf.trans_wf r (htrans_mem r hr).1
  · refine ⟨by rw [hep_eq]; exact hact_upd.sync.cache_epoch, hact_upd.sync.cache_inr, ?_, ?_⟩
    · intro Q sIdx hvQ; rw [hst_acc] at hvQ ⊢; by_cases hQP : Q = P
      · subst hQP; simpa [st'] using
          hact_upd.sync.vS_inr Q sIdx (by simpa [st'] using hvQ)
      · simpa [Function.update_of_ne hQP] using
          hact_upd.sync.vS_inr Q sIdx
            (by simpa [Function.update_of_ne hQP] using hvQ)
    · intro Q τ sIdx hvQ
      exact hact_upd.sync.vR_inr Q τ sIdx ((hvR_inr_eq Q τ sIdx).mp hvQ)
  · intro hgf
    have hf := hact_upd.forged hgf
    exact ⟨hf.1, hf.2⟩
  · intro hgt
    have hm := hact_upd.main hgt
    refine ⟨by rw [hep_eq]; exact hm.fresh_above, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hv0
      exact (hvR_inr_eq .A 0 0).mpr (hm.vR0_init hv0)
    · intro hepB hv0
      rw [hep_eq] at hepB; rw [hst_acc]
      by_cases hPB : P = .B
      · subst hPB; simpa [st'] using hm.vS0_init hepB hv0
      · have hBP : (.B : Party) ≠ P := fun h => hPB h.symm
        simpa [Function.update_of_ne hBP] using hm.vS0_init hepB hv0
    · intro Q ss h1 hsQ hvQ
      rw [hst_acc] at h1 hsQ hvQ ⊢
      by_cases hQP : Q = P
      · subst hQP; simpa [st'] using hm.vS_inl_cache Q ss
          (by simpa [st'] using h1)
          (by simpa [st'] using hsQ)
          (by simpa [st'] using hvQ)
      · simpa [Function.update_of_ne hQP] using hm.vS_inl_cache Q ss
          (by simpa [Function.update_of_ne hQP] using h1)
          (by simpa [Function.update_of_ne hQP] using hsQ)
          (by simpa [Function.update_of_ne hQP] using hvQ)
    · intro Q τ h1 hcn
      have hn := hm.vR_none_of_cache_none Q τ h1 hcn
      rw [hst_acc]
      by_cases hQP : Q = P
      · subst hQP
        simp only [Function.update_self] at hn
        simp only [st', Function.update_self]
        by_cases hτ : τ = t
        · subst hτ; rw [hvR_mid] at hn; exact nomatch hn
        · simp [Function.update_of_ne hτ, hn]
      · simpa [Function.update_of_ne hQP] using hn
    · refine ⟨?_, hm.slot_canon.2.1,
        fun Q τ sIdx hvQ => hm.slot_canon.2.2.1 Q τ sIdx ((hvR_inr_eq Q τ sIdx).mp hvQ),
        hm.slot_canon.2.2.2.1, ?_⟩
      · intro Q sIdx hvQ
        rw [hst_acc] at hvQ
        by_cases hQP : Q = P
        · subst hQP
          exact hm.slot_canon.1 Q sIdx (by simpa [st'] using hvQ)
        · exact hm.slot_canon.1 Q sIdx
            (by simpa [Function.update_of_ne hQP] using hvQ)
      · intro τ Tc σc kV sIdx rs'₀ hc
        have hne0 := hm.slot_canon.2.2.2.2 τ Tc σc kV sIdx
        rw [hst_acc]
        by_cases hQP : Party.receiverOf τ = P
        · rw [hQP]; simp only [st', Function.update_self]
          by_cases hτ : τ = t
          · subst hτ
            exact absurd (by simpa [hrecv_t] using hvR_mid) (hne0 rs hc)
          · simp only [Function.update_of_ne hτ]
            simpa [hQP] using hne0 rs'₀ hc
        · simpa [Function.update_of_ne hQP] using hne0 rs'₀ hc
    · intro Q sIdx hvQ hsQ
      rw [hidx_eq]; rw [hst_acc] at hvQ hsQ
      by_cases hQP : Q = P
      · subst hQP; exact hm.idx_sync Q sIdx
          (by simpa [st'] using hvQ)
          (by simpa [st'] using hsQ)
      · exact hm.idx_sync Q sIdx
          (by simpa [Function.update_of_ne hQP] using hvQ)
          (by simpa [Function.update_of_ne hQP] using hsQ)
    · intro r hr hv hle hcor
      exact hm.trans_idx r (htrans_mem r hr).1 hv hle hcor
    · intro idx x hx
      rcases hm.fsTrans_sub idx x hx with ⟨hbne, r, hr_mem, hr_pos, hr_ct, hx_eq⟩
      refine ⟨hbne, r, ?_, hr_pos, hr_ct, hx_eq⟩
      have hne_ep : slotEpoch (q + 1) true tL idx ≠ t := by
        intro heq_ep
        rcases hm.slot_canon.2.2.2.1 idx hbne with ⟨_, hv_t, _, hcor⟩
        rw [heq_ep] at hv_t hcor
        rcases hcor with rfl | ⟨Tc, σc, kV, hc⟩
        · have hvR0 := hm.vR0_init hv_t
          have hPA : P = .A := by simpa [Party.receiverOf, Party.senderOf] using hrecv_t.symm
          subst hPA; simp [hvR_mid] at hvR0
        · exact hm.slot_canon.2.2.2.2 t Tc σc kV idx rs hc
            (by simpa [hrecv_t] using hvR_mid)
      have hne_pos : r.pos ≠ pos := by
        intro hp
        have hep := congrArg Pos.epoch (hr_pos.symm.trans hp)
        exact hne_ep (hep.trans hpos_ep)
      simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne]
      exact ⟨hr_mem, hne_pos⟩
    · intro τ hle hv hdisj
      have hdisj' : (∃ Tc σc kV, h_mid.cache τ = some (Tc, σc, kV, none)) ∨
          (∃ rs0, (s_upd.st (Party.receiverOf τ)).vR τ = some (.inl rs0)) := by
        rcases hdisj with hc | ⟨rs0, hvR0⟩
        · exact Or.inl hc
        · rw [hst_acc] at hvR0
          by_cases hQP : Party.receiverOf τ = P
          · by_cases hτ : τ = t
            · subst hτ; exact Or.inr ⟨rs, by simpa [s_upd, hQP] using hvR_mid⟩
            · exact Or.inr ⟨rs0, by
                rw [hQP] at hvR0 ⊢
                simpa [s_upd, st', Function.update_of_ne hτ] using hvR0⟩
          · exact Or.inr ⟨rs0, by
              simpa [s_upd, s, Function.update_of_ne hQP] using hvR0⟩
      rcases hm.inl_comp τ hle hv hdisj' with ⟨cur, hcur, hlt, hbr⟩
      refine ⟨cur, hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq => (hcomp_iff r hr).mpr (hc r (htrans_mem r hr).1 heq)⟩
    · intro idx c hsc_idx
      rcases hm.sc_comp idx c hsc_idx with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
      refine ⟨hsl, hv, hle, cur, hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq hci =>
          (hcomp_iff r hr).mpr (hc r (htrans_mem r hr).1 heq hci)⟩

theorem accept_inr_preserves_activeInv
    {Γ T RSt K I SS RS M C : Type} [DecidableEq T] [DecidableEq M] [DecidableEq C]
    {q qep rem : ℕ} {gMain : Bool} {tL : Option ℕ} {par : Bool}
    {P : Party} {t sIdx drop : ℕ} {pos : Pos}
    {es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))}
    {s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    {h1 : FSMultiBucketAuthState T RSt K I (ℕ × C)}
    {ns : ℕ → ℕ} {sc1 : ℕ → Option ℕ}
    (hno_abort : es0.abort = false)
    (hvR_mid : s_mid.vR t = some (.inr sIdx))
    (hpos_ep : pos.epoch = t)
    (hdrop_main : gMain = true → drop = pos.idx)
    (hact1 : ActiveInv q qep rem gMain tL par
      { g := { es0.g with st := Function.update es0.g.st P s_mid,
                          epoch := Function.update es0.g.epoch P (max (es0.g.epoch P) t) },
        h := h1, abort := false } none ns sc1) :
    let st' := { s_mid with vR := Function.update s_mid.vR t (some (.inr sIdx)) }
    let b := (h1.book sIdx).getD {}
    let h2 : FSMultiBucketAuthState T RSt K I (ℕ × C) :=
      { h1 with
          book := Function.update h1.book sIdx
            (some { b with fsTrans := b.fsTrans.filter (·.1 != drop) }) }
    ActiveInv q qep rem gMain tL par
      { es0 with g := es0.g.accept P st' pos, h := h2 } none ns sc1 := by
  intro st' b h2
  have hst'_eq : st' = s_mid := by
    have hfun : Function.update s_mid.vR t (some (.inr sIdx)) = s_mid.vR := by
      ext τ; by_cases hτ : τ = t
      · subst hτ; simp [hvR_mid]
      · simp [Function.update_of_ne hτ]
    cases s_mid; simp [st', hfun]
  rw [hst'_eq]
  let s := es0.g
  let s_upd := { s with st := Function.update s.st P s_mid,
                        epoch := Function.update s.epoch P (max (s.epoch P) t) }
  let s_acc := s.accept P s_mid pos
  have hst_eq : s_acc.st = s_upd.st := rfl
  have hep_eq : s_acc.epoch = s_upd.epoch := by
    simp [s_acc, s_upd, GameState.accept, GameState.delete, hpos_ep]
  have hidx_eq : s_acc.idx = s_upd.idx := rfl
  have htL_eq : s_acc.tL = s_upd.tL := rfl
  have hleaks_eq : s_acc.leaks = s_upd.leaks := rfl
  have hwin_eq : s_acc.win = s_upd.win := rfl
  have hcnt : ∀ idx, ((h2.book idx).getD {}).fsCount = ((h1.book idx).getD {}).fsCount := by
    intro idx; by_cases hi : idx = sIdx <;> simp [h2, b, hi, Function.update_of_ne]
  have htrans_mem : ∀ r ∈ s_acc.trans, r ∈ s_upd.trans ∧ r.pos ≠ pos := by
    intro r hr
    simp only [s_acc, GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne] at hr
    exact hr
  have hcomp_iff : ∀ r ∈ s_acc.trans, r.pos ∈ s_acc.comp ↔ r.pos ∈ s_upd.comp := by
    intro r hr
    have hne := (htrans_mem r hr).2
    simp [s_acc, s_upd, GameState.accept, GameState.delete, hne]
  refine ⟨hno_abort, by rw [hwin_eq]; exact hact1.no_win, rfl, hact1.sess, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hst_eq]; exact hact1.wf.vp_id,
      by rw [hst_eq, hep_eq]; exact hact1.wf.vp_tcur,
      by rw [hst_eq]; exact hact1.wf.vp_vS_some,
      fun r hr => by rw [hep_eq]; exact hact1.wf.trans_wf r (htrans_mem r hr).1,
      by rw [htL_eq, hleaks_eq]; exact hact1.wf.tL_eq⟩
  · exact ⟨by rw [hep_eq]; exact hact1.sync.cache_epoch, hact1.sync.cache_inr,
      by rw [hst_eq]; exact hact1.sync.vS_inr, by rw [hst_eq]; exact hact1.sync.vR_inr⟩
  · intro hgf
    have hf := hact1.forged hgf
    refine ⟨fun idx x hx => ?_, hf.sc_not_healed⟩
    by_cases hi : idx = sIdx
    · subst idx
      simp only [h2, b, Function.update_self, Option.getD_some, List.mem_filter] at hx
      exact hf.hdr_honest sIdx x hx.1
    · exact hf.hdr_honest idx x (by simpa [h2, Function.update_of_ne hi] using hx)
  · intro hgt
    subst hgt
    have hm := hact1.main rfl
    have hvRr := hact1.sync.vR_inr P t sIdx (by simp [hvR_mid])
    have hsl_sIdx : sIdx = slotOf q tL t := hm.slot_canon.2.2.1 P t sIdx (by simp [hvR_mid])
    have htH_t : healEpoch tL ≤ t := healEpoch_le_of_validGuess hvRr.2.1
    have hdrop : drop = pos.idx := hdrop_main rfl
    refine ⟨?_, by rw [hst_eq]; exact hm.vR0_init,
      by rw [hep_eq, hst_eq]; exact hm.vS0_init,
      by rw [hst_eq]; exact hm.vS_inl_cache,
      by rw [hst_eq]; exact hm.vR_none_of_cache_none,
      ⟨by rw [hst_eq]; exact hm.slot_canon.1, hm.slot_canon.2.1,
       by rw [hst_eq]; exact hm.slot_canon.2.2.1, ?_,
       by rw [hst_eq]; exact hm.slot_canon.2.2.2.2⟩,
      ?_, fun r hr => hm.trans_idx r (htrans_mem r hr).1, ?_, ?_, ?_⟩
    · intro τ h1_τ htH hlt
      rw [hep_eq] at hlt
      have hne_τ : τ ≠ t := by
        intro heq; subst heq
        rcases hvRr.2.2.2.2 rfl with rfl | ⟨Tc, σc, kV, hc⟩
        · omega
        · have hce := (hact1.sync.cache_epoch τ (by dsimp only at hc ⊢; simp [hc])).2
          dsimp only [s_upd, s] at hlt hce; omega
      have hne_s : slotOf q tL τ ≠ sIdx := by
        rw [hsl_sIdx]; exact fun heq => hne_τ (slotOf_inj htH htH_t heq)
      have hf := hm.fresh_above τ h1_τ htH hlt
      refine ⟨hf.1, hf.2.1, ?_, hf.2.2.2⟩
      dsimp only
      rw [show h2.book (slotOf q tL τ) = h1.book (slotOf q tL τ) by
        simp [h2, Function.update_of_ne hne_s]]
      exact hf.2.2.1
    · intro idx hbne
      by_cases hi : idx = sIdx
      · subst idx; rw [hvRr.1]; exact ⟨hsl_sIdx, hvRr.2.1, hvRr.2.2.1, hvRr.2.2.2.2 rfl⟩
      · exact hm.slot_canon.2.2.2.1 idx (by simpa [h2, Function.update_of_ne hi] using hbne)
    · intro Q idx hvQ hsQ
      rw [hst_eq] at hvQ hsQ; rw [hidx_eq]
      have his := hm.idx_sync Q idx hvQ hsQ
      exact ⟨his.1, by rw [hcnt]; exact his.2⟩
    · intro idx x hx
      by_cases hi : idx = sIdx
      · subst idx
        simp only [h2, b, Function.update_self, Option.getD_some, List.mem_filter,
          bne_iff_ne] at hx
        rcases hm.fsTrans_sub sIdx x hx.1 with ⟨_, r, hr_mem, hr_pos, hr_ct, hx_eq⟩
        have hne_pos : r.pos ≠ pos := by
          intro hp
          have hidx : r.pos.idx = x.1 := congrArg Pos.idx hr_pos
          rw [hp, ← hdrop] at hidx
          exact hx.2 hidx.symm
        refine ⟨by simp [h2], r, ?_, hr_pos, hr_ct, hx_eq⟩
        simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne]
        exact ⟨hr_mem, hne_pos⟩
      · simp only [h2, Function.update_of_ne hi] at hx
        rcases hm.fsTrans_sub idx x hx with ⟨hb0, r, hr_mem, hr_pos, hr_ct, hx_eq⟩
        have hne_ep : slotEpoch (q + 1) true tL idx ≠ t := by
          intro heq_ep
          rcases hm.slot_canon.2.2.2.1 idx hb0 with ⟨hsl_idx, _, _, _⟩
          rw [heq_ep, ← hsl_sIdx] at hsl_idx
          exact hi hsl_idx
        have hne_pos : r.pos ≠ pos := by
          intro hp
          have hep := congrArg Pos.epoch (hr_pos.symm.trans hp)
          exact hne_ep (hep.trans hpos_ep)
        refine ⟨by simpa [h2, Function.update_of_ne hi] using hb0, r, ?_, hr_pos, hr_ct, hx_eq⟩
        simp only [GameState.accept, GameState.delete, List.mem_filter, bne_iff_ne]
        exact ⟨hr_mem, hne_pos⟩
    · intro τ hle hv hdisj
      rw [hst_eq] at hdisj
      rcases hm.inl_comp τ hle hv hdisj with ⟨cur, hcur, hlt, hbr⟩
      refine ⟨cur, hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq => (hcomp_iff r hr).mpr (hc r (htrans_mem r hr).1 heq)⟩
    · intro idx c hsc_idx
      rcases hm.sc_comp idx c hsc_idx with ⟨hsl, hv, hle, cur, hcur, hlt, hbr⟩
      refine ⟨hsl, hv, hle, cur, hcur, hlt, ?_⟩
      rcases hbr with hlt' | ⟨hle', hc⟩
      · exact Or.inl hlt'
      · exact Or.inr ⟨hle', fun r hr heq hci =>
          (hcomp_iff r hr).mpr (hc r (htrans_mem r hr).1 heq hci)⟩

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecvInv
