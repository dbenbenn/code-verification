/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecvInv
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux

/-!
# Active `Deliver` (`i₃`) and `Inject` (`i₄`) Step Proofs for `la = false`

Proves unified `vRecv_hoare` together with `i3_deliver_active_hoare` and
`i4_inject_active_hoare`, showing `FalseInv` is preserved across adversary `deliver` and `inject`
queries (`rem + 1 → rem`) and any newly latched `winEp` satisfies `WinSafe`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecv

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM (Pos Record RecvResult GameState ltOpt healedBy
  lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Construction (PartyState Header healEpoch
  FSMultiSpec FSMultiBook)
open _root_.CryptoGames.SM.Engine (VP Ctx EState liftH abortE commitE vRecv deliverE injectE)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (postLeak bucketAuthCfg)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (
  FSMultiBucketAuthState FSMultiBucketAuthEState liftFSMultiBucket lookupMultiBucketF
  regSessMultiBucket validGuessBucketParAuth isHonestHdrMultiBucket
  hooksFSMultiBucketAuth implFSMultiBucketAuth)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseBase (
  FSFalseSemantics slotEpoch slotOf healEpoch_le_of_validGuess
  regSessMultiBucket_slotEpoch
  WinSafe SessBound sessBound_lt sessBound_mono_noop sessBound_regSess
  EngineWF authAvoided_false_of_leak_between winSafe_of_leak_between
  trivial_true_of_leak_ge_and_comp healedBy_s_of_postLeak_false
  SlotSync ForgedInv MainInv ActiveInv FalseInv
  liftH_false_hoare lazy_cs_hoare lookupMultiBucketF_false_hoare)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecvInv (
  party_recv_of_sendsIn_false activeInv_s_upd_of_startRecv
  lazy_cs_preserves_activeInv accept_inl_preserves_activeInv accept_inr_preserves_activeInv)

/-! ## 1. Unified `vRecv_hoare` (`startRecv` + `fsRecv`) -/

private def VRecvPost {Γ T RSt K I SS RS M C : Type} [DecidableEq T] [DecidableEq M] [DecidableEq C]
    (q qep rem : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × (ℕ × C))
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (out : Option (Option (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × ℕ × ℕ × M)) ×
           FSMultiBucketAuthState T RSt K I (ℕ × C))
    (ns' : ℕ → ℕ) (sc' : ℕ → Option ℕ) : Prop :=
  match out.1 with
  | none => True
  | some none => ActiveInv q qep rem gMain tL par { es0 with h := out.2 } none ns' sc'
  | some (some (st', t', i', _)) =>
    t' = c.1.1 ∧
    ((qep + 1 < t' ∨ lastLeakGuessAdmissible 3 tL t' = false) →
      ActiveInv q qep rem gMain tL par { es0 with h := out.2 } none ns' sc') ∧
    (∀ pos : Pos, pos.epoch = t' →
      (pos.idx = i' ∨ ∃ r ∈ es0.g.trans, r.ct = c ∧ pos = r.pos) →
      ActiveInv q qep rem gMain tL par
        { es0 with g := es0.g.accept P st' pos, h := out.2 } none ns' sc') ∧
    ((es0.g.inTransit P.other c).isSome = false → es0.g.safeInj 3 = true →
      t' ≤ qep + 1 → es0.g.trivial 3 ⟨P.other, t', i'⟩ = false →
      lastLeakGuessAdmissible 3 tL t' = true →
      (gMain = true →
        WinSafe tL par { es0 with g := { es0.g with win := true }, h := out.2 } (some t')) ∧
      (gMain = false → t' = es0.g.epoch P + 1 → isHonestHdrMultiBucket es0.h c.1 = false →
        WinSafe tL par { es0 with g := { es0.g with win := true }, h := out.2 } (some t')))

private theorem fsRecv_step_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × (ℕ × C))
    (rec : Option (Record M (Header T × (ℕ × C))))
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C)))
    (s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h_mid : FSMultiBucketAuthState T RSt K I (ℕ × C))
    (hsends_f : P.sendsIn c.1.1 = false)
    (hcache_eq : h_mid.cache = es0.h.cache)
    (hforged_new_inr : gMain = false → c.1.1 = es0.g.epoch P + 1 →
      isHonestHdrMultiBucket es0.h c.1 = false → postLeak tL es0.g = false →
      validGuessBucketParAuth 1 tL par c.1.1 = true →
      ∀ rs, s_mid.vR c.1.1 ≠ some (.inl rs)) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    let t := c.1.1
    let s_upd := { es0.g with st := Function.update es0.g.st P s_mid,
                              epoch := Function.update es0.g.epoch P (max (es0.g.epoch P) t) }
    S.H (fun ns sc =>
          ActiveInv q qep rem gMain tL par { es0 with h := h_mid } none ns sc ∧
          ActiveInv q qep rem gMain tL par { g := s_upd, h := h_mid, abort := false } none ns sc)
      (VRecvPost q qep rem gMain tL par P c es0)
      ((match s_mid.vR t with
        | none => Pure.pure (some none)
        | some v => do
          match ← hk.fsRecv es0.g P t v c.1 c.2 rec with
          | none => Pure.pure none
          | some none => Pure.pure (some none)
          | some (some (v', i, m)) =>
            Pure.pure (some (some ({ s_mid with vR := Function.update s_mid.vR t (some v') },
                                   t, i, m)))).run h_mid) := by
  intro hk t s_upd
  let s := es0.g
  have ⟨_, hsender_t, hrecv_t⟩ := party_recv_of_sendsIn_false hsends_f
  cases hvR : s_mid.vR t with
  | none =>
    simp only [StateT.run_pure]
    exact S.pure _ fun _ _ ⟨hact_s, _⟩ => hact_s
  | some v =>
    cases v with
    | inl rs =>
      dsimp only [hk, hooksFSMultiBucketAuth]
      simp only [pure_bind]
      cases hfs : fs.receive rs c.1 c.2 with
      | none =>
        simp only [Option.map_none, StateT.run_pure]
        exact S.pure _ fun _ _ ⟨hact_s, _⟩ => hact_s
      | some o =>
        rcases o with ⟨rs', i', m'⟩
        simp only [Option.map_some, StateT.run_pure]
        refine S.pure _ fun ns sc ⟨hact_s, hact_upd⟩ => ⟨rfl, fun _ => hact_s, ?_, ?_⟩
        · intro pos hpos_ep _
          exact accept_inl_preserves_activeInv hact_s.no_abort hsends_f hvR hpos_ep hact_upd
        · intro _ hsafeInj hle_qep hntriv hadm
          refine ⟨fun hgt => ?_, fun hgf ht_ep hhon_f => ?_⟩
          · by_cases hpar_t : (decide (Party.senderOf t == Party.A) == par) = true
            · have hvg_t : validGuessBucketParAuth 1 tL par t = true := by
                dsimp only [validGuessBucketParAuth, Nat.reduceAdd]; rw [hadm, hpar_t]; rfl
              have hm := hact_upd.main hgt
              have hvR_upd : (s_upd.st (Party.receiverOf t)).vR t = some (.inl rs) := by
                dsimp only [s_upd, t] at *; rw [hrecv_t, Function.update_self]; exact hvR
              rcases hm.inl_comp t hle_qep hvg_t (Or.inr ⟨rs, hvR_upd⟩) with
                ⟨cur, hcur, hlt, hlt_t | ⟨hle_cur, hcomp_all⟩⟩
              · exact winSafe_of_leak_between hcur hlt hlt_t
              · have htriv := trivial_true_of_leak_ge_and_comp (pos := ⟨P.other, t, i'⟩)
                  hact_s.wf hcur hle_cur (fun r hr heq => hcomp_all r hr (by rw [heq]))
                rw [htriv] at hntriv; exact nomatch hntriv
            · unfold WinSafe
              intro tWin hsome; cases hsome
              dsimp only [t] at hpar_t
              rw [Bool.eq_false_iff.mpr hpar_t, Bool.and_false]
          · by_cases hpl : postLeak tL s = true
            · simp only [postLeak] at hpl
              cases hstL : s.tL with
              | none => simp [hstL] at hpl
              | some cur =>
                rw [hstL] at hpl
                rcases hact_s.wf.mem_leaks_of_tL hstL with ⟨hcur_mem, _⟩
                dsimp only [s, t] at hstL hsafeInj ⊢
                simp only [GameState.safeInj, hstL, healedBy, decide_eq_true_eq] at hsafeInj
                have hepP_ge : cur + 3 ≤ es0.g.epoch P := by
                  have hboth := Nat.le_min.mp hsafeInj
                  cases P <;> [exact hboth.1; exact hboth.2]
                have hcur_lt_t : cur < c.1.1 := by omega
                exact winSafe_of_leak_between hcur_mem hpl hcur_lt_t
            · simp only [Bool.not_eq_true] at hpl
              by_cases hpar_t : (decide (Party.senderOf t == Party.A) == par) = true
              · have hvg_t : validGuessBucketParAuth 1 tL par t = true := by
                  dsimp only [validGuessBucketParAuth, Nat.reduceAdd]; rw [hadm, hpar_t]; rfl
                exact False.elim (hforged_new_inr hgf ht_ep hhon_f hpl hvg_t rs hvR)
              · unfold WinSafe
                intro tWin hsome; cases hsome
                dsimp only [t] at hpar_t
                rw [Bool.eq_false_iff.mpr hpar_t, Bool.and_false]
    | inr sIdx =>
      dsimp only [hk, hooksFSMultiBucketAuth]
      let bk := ((h_mid.book sIdx).getD {})
      let findHdr {E : Type} [DecidableEq E]
          (xs : List (ℕ × Header T × E)) (he : Header T × E) :=
        xs.find? (fun x => x.2 == he)
      let matched := findHdr bk.fsTrans (c.1, c.2)
      let cond := matched.isNone && !(healedBy s.tL 3 t) && !bk.sCorr
      simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
      refine S.bind (lazy_cs_hoare S cond sIdx h_mid) fun ⟨ok, h1⟩ => ?_
      cases ok with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
        exact S.pure _ fun _ _ _ => trivial
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, bind_assoc]
        -- Step `ActiveInv` across `lazy_cs_hoare` for both `s` and `s_upd`!
        have hstep_lazy : ∀ ns sc1,
            (∃ sc0,
              (ActiveInv q qep rem gMain tL par { es0 with h := h_mid } none ns sc0 ∧
               ActiveInv q qep rem gMain tL par { g := s_upd, h := h_mid, abort := false } none ns sc0) ∧
              h1.cache = h_mid.cache ∧ h1.sessions = h_mid.sessions ∧
              (∀ idx, ((h1.book idx).getD {}).fsCount = ((h_mid.book idx).getD {}).fsCount) ∧
              (∀ idx, ((h1.book idx).getD {}).fsTrans = ((h_mid.book idx).getD {}).fsTrans) ∧
              (∀ idx, idx ≠ sIdx → h1.book idx = h_mid.book idx) ∧
              (cond = false → True ∧ h1 = h_mid ∧ sc1 = sc0) ∧
              (true = false → sc1 = sc0) ∧
              (True → cond = true →
                sc1 = Function.update sc0 sIdx (some ((sc0 sIdx).getD (ns sIdx))) ∧
                h1.book sIdx ≠ none)) →
            slotEpoch (q + 1) gMain tL sIdx = t ∧
            validGuessBucketParAuth 1 tL par t = true ∧ t ≤ qep + 1 ∧
            ((h1.book sIdx).getD {}).fsTrans = bk.fsTrans ∧
            h1.cache = es0.h.cache ∧
            (cond = false → True ∧ (∃ sc0, sc1 = sc0 ∧
              ActiveInv q qep rem gMain tL par { g := s_upd, h := h_mid, abort := false } none ns sc0)) ∧
            ActiveInv q qep rem gMain tL par { es0 with h := h1 } none ns sc1 ∧
            ActiveInv q qep rem gMain tL par { g := s_upd, h := h1, abort := false } none ns sc1 := by
          intro ns sc1 ⟨sc0, ⟨hact_s0, hact_u0⟩, hc1, hs1, hcnt1, hftr1, hbne1, hcf, _, hct⟩
          have hvRr := hact_u0.sync.vR_inr P t sIdx (by simp [s_upd, hvR])
          have hmain_sIdx : gMain = true → sIdx = slotOf q tL t ∧
              (t = 0 ∨ ∃ Tc σc kVal, h_mid.cache t = some (Tc, σc, kVal, some sIdx)) := by
            intro hgt
            exact ⟨(hact_u0.main hgt).slot_canon.2.2.1 P t sIdx (by simp [s_upd, hvR]),
              hvRr.2.2.2.2 hgt⟩
          have hcond_nh : cond = true → healedBy s.tL 3 t = false := by
            intro hc_eq
            simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hc_eq
            exact hc_eq.1.2
          have hact_s1 := lazy_cs_preserves_activeInv (s_any := s) (no_abort := es0.abort)
            hact_s0 hvRr.1 hvRr.2.1 hvRr.2.2.1 hmain_sIdx hcond_nh
            hc1 hs1 hcnt1 hftr1 hbne1
            (fun h => ⟨(hcf h).2.1, (hcf h).2.2⟩) (fun h => hct trivial h)
          have hact_u1 := lazy_cs_preserves_activeInv (s_any := s_upd) (no_abort := false)
            hact_u0 hvRr.1 hvRr.2.1 hvRr.2.2.1 hmain_sIdx hcond_nh
            hc1 hs1 hcnt1 hftr1 hbne1
            (fun h => ⟨(hcf h).2.1, (hcf h).2.2⟩) (fun h => hct trivial h)
          exact ⟨hvRr.1, hvRr.2.1, hvRr.2.2.1, hftr1 sIdx, hc1.trans hcache_eq,
            fun h => ⟨trivial, sc0, (hcf h).2.2, hact_u0⟩, hact_s1, hact_u1⟩
        -- Split `matched.isSome` (`deliverQuery` vs `injectQuery`)
        cases hmat : matched with
        | some y =>
          have hmat_mem : y ∈ bk.fsTrans := List.mem_of_find?_eq_some hmat
          have hy_ct : y.2 = c := by
            have hfind_eq : ∀ {E : Type} [DecidableEq E]
                {xs : List (ℕ × Header T × E)} {he : Header T × E} {z : ℕ × Header T × E},
                findHdr xs he = some z → z.2 = he := by
              intro E _ xs he z hz
              simpa [beq_iff_eq] using List.find?_some hz
            exact hfind_eq hmat
          have hmat_eq : findHdr ((h_mid.book sIdx).getD {}).fsTrans (c.1, c.2) = some y := hmat
          dsimp only [findHdr] at hmat_eq
          simp only [hmat_eq, Option.isSome_some, ↓reduceIte]
          refine S.conseq (S.bind (S.dl sIdx c.1 c.2 h1) fun ⟨res, h1'⟩ => ?_)
            hstep_lazy (fun _ _ _ h => h)
          cases res with
          | none =>
            simp only [StateT.run_pure, pure_bind]
            exact S.pure _ fun _ _ _ => trivial
          | some rRes =>
            cases rRes with
            | rejected =>
              simp only [StateT.run_pure, pure_bind]
              exact S.pure _ fun _ _ ⟨hh1', ⟨_, _, _, _, _, _, hact_s1, _⟩, _⟩ => by
                subst h1'; exact hact_s1
            | accepted i mo' =>
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                Option.map_some, Option.getD_some,
                StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
              have hfin_out : ∀ mOut : M,
                  S.H (fun ns' sc' => h1' = h1 ∧
                        (slotEpoch (q + 1) gMain tL sIdx = t ∧
                         validGuessBucketParAuth 1 tL par t = true ∧ t ≤ qep + 1 ∧
                         ((h1.book sIdx).getD {}).fsTrans = bk.fsTrans ∧
                         h1.cache = es0.h.cache ∧
                         (cond = false → True ∧ (∃ sc0, sc' = sc0 ∧
                           ActiveInv q qep rem gMain tL par
                             { g := s_upd, h := h_mid, abort := false } none ns' sc0)) ∧
                         ActiveInv q qep rem gMain tL par { es0 with h := h1 } none ns' sc' ∧
                         ActiveInv q qep rem gMain tL par
                           { g := s_upd, h := h1, abort := false } none ns' sc') ∧
                        (∀ i0 mo0, (some (_root_.CryptoGames.FSAEAD.ReceiveResult.accepted i mo') :
                          Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)) =
                            some (.accepted i0 mo0) → i0 = c.2.1))
                    (VRecvPost q qep rem gMain tL par P c es0)
                    (Pure.pure (some (some ({ s_mid with vR :=
                                                Function.update s_mid.vR t (some (.inr sIdx)) },
                                            t, i, mOut)),
                      { h1' with book := (Function.update h1'.book sIdx
                          (some { ((h1'.book sIdx).getD {}) with
                            fsTrans := ((h1'.book sIdx).getD {}).fsTrans.filter (·.1 != y.1) })) })) := by
                intro mOut
                refine S.pure _ fun ns' sc' ⟨hh1', ⟨hsl_ep, hvg, hle_qep, hftr_bk, hcache1, _,
                  hact_s1, hact_u1⟩, hi_eq_all⟩ => ?_
                subst h1'
                have hi_eq : i = c.2.1 := hi_eq_all i mo' rfl
                have hmat_h1 : y ∈ ((h1.book sIdx).getD {}).fsTrans := by
                  rw [hftr_bk]; exact hmat_mem
                refine ⟨rfl, ?_, ?_, ?_⟩
                · intro hbad
                  rcases hbad with hgt_qep | hadm_f
                  · omega
                  · simp [validGuessBucketParAuth, hadm_f] at hvg
                · intro pos hpos_ep hpos_idx
                  refine accept_inr_preserves_activeInv hact_s1.no_abort hvR hpos_ep ?_ hact_u1
                  intro hgt
                  have hm := hact_u1.main hgt
                  rcases hm.fsTrans_sub sIdx y hmat_h1 with ⟨_, _, _, _, _, hy_idx⟩
                  have hy1 : y.1 = c.2.1 := by rw [← hy_idx, hy_ct]
                  rcases hpos_idx with rfl | ⟨r, hr_mem, hr_ct, rfl⟩
                  · rw [hy1, hi_eq]
                  · have hsl_sIdx : sIdx = slotOf q tL t :=
                      hm.slot_canon.2.2.1 P t sIdx (by simp [s_upd, hvR])
                    have hcor : r.pos.epoch = 0 ∨ ∃ Tc σc kVal,
                        h1.cache r.pos.epoch =
                          some (Tc, σc, kVal, some (slotOf q tL r.pos.epoch)) := by
                      rw [hpos_ep, ← hsl_sIdx]
                      exact (hact_u1.sync.vR_inr P t sIdx (by simp [s_upd, hvR])).2.2.2.2 hgt
                    have hri := hm.trans_idx r hr_mem (by simpa [hpos_ep] using hvg)
                      (by simpa [hpos_ep] using hle_qep) hcor
                    rw [hy1, ← hr_ct, hri.2]
                · intro hinTrans_f _ _ _ _
                  refine ⟨fun hgt => ?_, fun hgf _ hhon_f => ?_⟩
                  · -- Contradiction: `y ∈ fsTrans` implies `s.inTransit P.other c` is `some`!
                    have hm := hact_u1.main hgt
                    rcases hm.fsTrans_sub sIdx y hmat_h1 with ⟨_, r, hr_mem, hr_pos, hr_ct, _⟩
                    have hpred : (r.pos.sender == P.other && decide (r.ct = c)) = true := by
                      subst hgt; rw [hr_pos, hsl_ep, hsender_t, hr_ct, hy_ct]; simp
                    have hsome_tr : (s.inTransit P.other c).isSome = true := by
                      unfold GameState.inTransit
                      rw [Option.isSome_iff_ne_none]
                      intro hnone
                      exact absurd hpred (by simp [List.find?_eq_none.mp hnone r hr_mem])
                    rw [hsome_tr] at hinTrans_f; exact nomatch hinTrans_f
                  · -- Contradiction: `ForgedInv.hdr_honest` implies `isHonestHdr es0.h c.1 = true`!
                    have hf := hact_u1.forged hgf
                    have hhon_t := hf.hdr_honest sIdx y hmat_h1
                    rw [hy_ct] at hhon_t
                    simp [isHonestHdrMultiBucket, hcache1] at hhon_t
                    simp [isHonestHdrMultiBucket] at hhon_f
                    rw [hhon_t] at hhon_f; exact nomatch hhon_f
              cases mo' with
              | some mOut =>
                simp only [StateT.run_pure, pure_bind]
                exact hfin_out mOut
              | none =>
                cases rec with
                | some rRec =>
                  simp only [StateT.run_pure, pure_bind]
                  exact hfin_out rRec.msg
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  exact S.pure _ fun _ _ _ => trivial
        | none =>
          have hmat_eq : findHdr ((h_mid.book sIdx).getD {}).fsTrans (c.1, c.2) = none := hmat
          dsimp only [findHdr] at hmat_eq
          simp only [hmat_eq, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          refine S.conseq (S.bind (S.ij sIdx c.1 c.2 h1) fun ⟨res, h1'⟩ => ?_)
            hstep_lazy (fun _ _ _ h => h)
          cases res with
          | none =>
            simp only [StateT.run_pure, pure_bind]
            exact S.pure _ fun _ _ _ => trivial
          | some rRes =>
            cases rRes with
            | rejected =>
              simp only [StateT.run_pure, pure_bind]
              exact S.pure _ fun _ _ ⟨hh1', ⟨_, _, _, _, _, _, hact_s1, _⟩, _⟩ => by
                subst h1'; exact hact_s1
            | accepted i mo' =>
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                Option.map_none, Option.getD_none,
                StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
              have hfin_out : ∀ mOut : M,
                  S.H (fun ns' sc' => h1' = h1 ∧
                        (slotEpoch (q + 1) gMain tL sIdx = t ∧
                         validGuessBucketParAuth 1 tL par t = true ∧ t ≤ qep + 1 ∧
                         ((h1.book sIdx).getD {}).fsTrans = bk.fsTrans ∧
                         h1.cache = es0.h.cache ∧
                         (cond = false → True ∧ (∃ sc0, sc' = sc0 ∧
                           ActiveInv q qep rem gMain tL par
                             { g := s_upd, h := h_mid, abort := false } none ns' sc0)) ∧
                         ActiveInv q qep rem gMain tL par { es0 with h := h1 } none ns' sc' ∧
                         ActiveInv q qep rem gMain tL par
                           { g := s_upd, h := h1, abort := false } none ns' sc') ∧
                        (∀ i0 mo0, (some (_root_.CryptoGames.FSAEAD.ReceiveResult.accepted i mo') :
                          Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)) =
                            some (.accepted i0 mo0) → i0 = c.2.1) ∧
                        ((∀ c_idx, sc' sIdx = some c_idx → c.2.1 ≤ c_idx) →
                          ∀ i0 mo0, (some (_root_.CryptoGames.FSAEAD.ReceiveResult.accepted i mo') :
                            Option (_root_.CryptoGames.FSAEAD.ReceiveResult M)) ≠
                              some (.accepted i0 mo0)))
                    (VRecvPost q qep rem gMain tL par P c es0)
                    (Pure.pure (some (some ({ s_mid with vR :=
                                                Function.update s_mid.vR t (some (.inr sIdx)) },
                                            t, i, mOut)),
                      { h1' with book := (Function.update h1'.book sIdx
                          (some { ((h1'.book sIdx).getD {}) with
                            fsTrans := ((h1'.book sIdx).getD {}).fsTrans.filter (·.1 != i) })) })) := by
                intro mOut
                refine S.pure _ fun ns' sc' ⟨hh1', ⟨hsl_ep, hvg, hle_qep, _, _, hcond_sc0,
                  hact_s1, hact_u1⟩, hi_eq_all, hij_noforge⟩ => ?_
                subst h1'
                have hi_eq : i = c.2.1 := hi_eq_all i mo' rfl
                -- Extract sender-corruption witness `sc' sIdx = some c_idx` with `c_idx < c.2.1`!
                have hsc_lt : ∃ c_idx, sc' sIdx = some c_idx ∧ c_idx < c.2.1 := by
                  by_contra hno
                  push Not at hno
                  exact hij_noforge hno i mo' rfl
                rcases hsc_lt with ⟨c_idx, hsc_eq, hci_lt⟩
                refine ⟨rfl, ?_, ?_, ?_⟩
                · intro hbad
                  rcases hbad with hgt_qep | hadm_f
                  · omega
                  · simp [validGuessBucketParAuth, hadm_f] at hvg
                · intro pos hpos_ep hpos_idx
                  refine accept_inr_preserves_activeInv hact_s1.no_abort hvR hpos_ep ?_ hact_u1
                  intro hgt
                  rcases hpos_idx with rfl | ⟨r, hr_mem, hr_ct, rfl⟩
                  · rfl
                  · have hm := hact_u1.main hgt
                    have hsl_sIdx : sIdx = slotOf q tL t :=
                      hm.slot_canon.2.2.1 P t sIdx (by simp [s_upd, hvR])
                    have hcor : r.pos.epoch = 0 ∨ ∃ Tc σc kVal,
                        h1.cache r.pos.epoch =
                          some (Tc, σc, kVal, some (slotOf q tL r.pos.epoch)) := by
                      rw [hpos_ep, ← hsl_sIdx]
                      exact (hact_u1.sync.vR_inr P t sIdx (by simp [s_upd, hvR])).2.2.2.2 hgt
                    have hri := hm.trans_idx r hr_mem (by simpa [hpos_ep] using hvg)
                      (by simpa [hpos_ep] using hle_qep) hcor
                    rw [hi_eq, ← hr_ct, hri.2]
                · intro _ hsafeInj _ hntriv hadm
                  refine ⟨fun hgt => ?_, fun hgf ht_ep _ => ?_⟩
                  · -- `gMain = true`: `MainInv.sc_comp` gives leak between or trivial forgery!
                    have hm := hact_u1.main hgt
                    rcases hm.sc_comp sIdx c_idx hsc_eq with ⟨_, _, _, cur, hcur, hlt, hbr⟩
                    subst hgt; rw [hsl_ep] at hbr
                    rcases hbr with hlt_t | ⟨hle_cur, hcomp_gt⟩
                    · exact winSafe_of_leak_between hcur hlt hlt_t
                    · have htriv := trivial_true_of_leak_ge_and_comp (pos := ⟨P.other, t, i⟩)
                        hact_s1.wf hcur hle_cur (fun r hr heq =>
                          hcomp_gt r hr (by rw [heq]) (by rw [heq, hi_eq]; exact hci_lt))
                      rw [htriv] at hntriv; exact nomatch hntriv
                  · -- `gMain = false` newly forged epoch `t = s.epoch P + 1`!
                    by_cases hpl : postLeak tL s = true
                    · simp only [postLeak] at hpl
                      cases hstL : s.tL with
                      | none => simp [hstL] at hpl
                      | some cur =>
                        rw [hstL] at hpl
                        rcases hact_s1.wf.mem_leaks_of_tL hstL with ⟨hcur_mem, _⟩
                        dsimp only [s, t] at hstL hsafeInj ⊢
                        simp only [GameState.safeInj, hstL, healedBy, decide_eq_true_eq] at hsafeInj
                        have hepP_ge : cur + 3 ≤ es0.g.epoch P := by
                          have hboth := Nat.le_min.mp hsafeInj
                          cases P <;> [exact hboth.1; exact hboth.2]
                        have hcur_lt_t : cur < c.1.1 := by omega
                        exact winSafe_of_leak_between hcur_mem hpl hcur_lt_t
                    · simp only [Bool.not_eq_true] at hpl
                      have hh_t : healedBy tL 3 t = true := by
                        simp only [lastLeakGuessAdmissible] at hadm
                        exact hadm
                      have hhs_t : healedBy s.tL 3 t = true :=
                        healedBy_s_of_postLeak_false hpl hh_t
                      have hcond_f : cond = false := by
                        simp [cond, hhs_t]
                      rcases (hcond_sc0 hcond_f).2 with ⟨sc0, rfl, hact_u0⟩
                      have hnh0 := (hact_u0.forged hgf).sc_not_healed sIdx
                        (by simp [hsc_eq])
                      subst hgf
                      rw [hsl_ep, hhs_t] at hnh0
                      exact nomatch hnh0
              cases mo' with
              | some mOut =>
                simp only [StateT.run_pure, pure_bind]
                exact hfin_out mOut
              | none =>
                cases rec with
                | some rRec =>
                  simp only [StateT.run_pure, pure_bind]
                  exact hfin_out rRec.msg
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  exact S.pure _ fun _ _ _ => trivial

private theorem vRecv_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × (ℕ × C))
    (rec : Option (Record M (Header T × (ℕ × C))))
    (es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
      (FSMultiBucketAuthState T RSt K I (ℕ × C))) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par es0 none)
      (VRecvPost q qep rem gMain tL par P c es0)
      ((vRecv hk es0.g P (es0.g.st P) c rec).run es0.h) := by
  intro hk
  let s := es0.g
  let t := c.1.1
  change S.H _ _ ((vRecv hk s P (s.st P) c rec).run es0.h)
  unfold vRecv
  dsimp only
  by_cases hg1 : ((s.st P).id.sendsIn c.1.1 || decide ((s.st P).tcur + 1 < c.1.1)) = true
  · simp only [hg1, ↓reduceIte, StateT.run_pure]
    exact S.pure _ fun _ _ hact =>
      ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
       hact.wf, hact.sync, hact.forged, hact.main⟩
  · simp only [hg1, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hg1
    -- Extract pure `(s.st P).id = P ∧ (s.st P).tcur = s.epoch P` from `ActiveInv` via `and_prop`!
    refine S.conseq
      (S.and_prop ((s.st P).id = P ∧ (s.st P).tcur = s.epoch P) fun ⟨hidP, htcurP⟩ => ?_)
      (fun _ _ hact => ⟨⟨hact.wf.vp_id P, hact.wf.vp_tcur P⟩, hact⟩)
      (fun _ _ _ h => h)
    have hsends_f : P.sendsIn t = false := by rw [← hidP]; exact hg1.1
    have ht_le_succ : t ≤ s.epoch P + 1 := by omega
    split_ifs with ht_next
    · have ht_ep : t = s.epoch P + 1 := by omega
      cases hc2 : c.1.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact S.pure _ fun _ _ hact =>
          ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
           hact.wf, hact.sync, hact.forged, hact.main⟩
      | some Tn =>
        have hc1_eq : c.1 = (t, some Tn) := by cases hc1 : c.1; simp [t, hc1] at hc2 ⊢; exact hc2
        simp only [StateT.run_bind]
        -- Step `hk.startRecv s P t (s.st P).γ (s.st P).root Tn`
        let startComp := hk.startRecv s P t (s.st P).γ (s.st P).root Tn
        have hstart : S.H (ActiveInv q qep (rem + 1) gMain tL par es0 none)
            (fun (p : Option (Option (Γ × RSt × (RS ⊕ ℕ))) ×
                      FSMultiBucketAuthState T RSt K I (ℕ × C)) ns sc =>
              match p.1 with
              | none => True
              | some none => ActiveInv q qep rem gMain tL par { es0 with h := p.2 } none ns sc
              | some (some (γ', σ', rsv)) =>
                let s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
                  { s.st P with tcur := t, γ := γ', root := σ',
                                vR := Function.update (s.st P).vR t (some rsv) }
                let s_upd := { s with st := Function.update s.st P s_mid,
                                      epoch := Function.update s.epoch P (max (s.epoch P) t) }
                p.2.cache = es0.h.cache ∧
                (gMain = false → t = s.epoch P + 1 →
                  isHonestHdrMultiBucket es0.h c.1 = false → postLeak tL s = false →
                  validGuessBucketParAuth 1 tL par t = true →
                  ∀ rs, s_mid.vR t ≠ some (.inl rs)) ∧
                ActiveInv q qep rem gMain tL par { es0 with h := p.2 } none ns sc ∧
                ActiveInv q qep rem gMain tL par
                  { g := s_upd, h := p.2, abort := false } none ns sc)
            (startComp.run es0.h) := by
          change S.H _ _ ((hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
            |>.startRecv s P t (s.st P).γ (s.st P).root Tn).run es0.h)
          unfold hooksFSMultiBucketAuth
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          cases hcache : es0.h.cache t with
          | some quad =>
            rcases quad with ⟨Tc, σc, kVal, optIdx⟩
            by_cases hTc : Tc = Tn
            · subst hTc
              simp only [↓reduceIte, StateT.run_pure]
              refine S.pure _ fun ns sc hact => ?_
              have hboth := activeInv_s_upd_of_startRecv
                (γ' := (cka.receive (s.st P).γ Tc).1) (σ' := σc)
                (rsv := match optIdx with | none => .inl (fs.initReceiver kVal) | some sIdx => .inr sIdx)
                hact hsends_f ht_ep (sessBound_mono_noop hact.sess rfl) rfl rfl (fun _ => rfl)
                (fun _ => ⟨Tc, σc, kVal, optIdx, hcache, by
                  cases optIdx with
                  | none => exact Or.inl ⟨rfl, _, rfl⟩
                  | some sIdx => exact Or.inr ⟨sIdx, rfl, rfl⟩⟩)
                (fun sIdx hgf hrsv => by
                  cases optIdx with
                  | none => exact nomatch hrsv
                  | some sIdx₀ =>
                    cases hrsv
                    have hci := hact.sync.cache_inr t Tc σc kVal sIdx hcache
                    subst hgf; exact hci)
              refine ⟨rfl, fun _ _ hhon_f _ _ _ _ => ?_, hboth.1, hboth.2⟩
              simp [isHonestHdrMultiBucket, hc1_eq, hcache] at hhon_f
            · simp only [hTc, ↓reduceIte]
              cases gMain with
              | true =>
                simp only [↓reduceIte]
                split_ifs <;> simp only [StateT.run_pure]
                · exact S.pure _ fun _ _ _ => trivial
                · exact S.pure _ fun _ _ hact =>
                    ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                     hact.wf, hact.sync, hact.forged, hact.main⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                split_ifs with hg_adm hg_tH hg_pl hg_vg hg_ge
                · simp only [StateT.run_pure]; exact S.pure _ fun _ _ _ => trivial
                · simp only [StateT.run_pure]
                  refine S.pure _ fun ns sc hact => ?_
                  let kk := cka.receive (s.st P).γ Tn
                  let p := prng.up (s.st P).root kk.2
                  have hboth := activeInv_s_upd_of_startRecv
                    (γ' := kk.1) (σ' := p.1) (rsv := .inl (fs.initReceiver p.2))
                    hact hsends_f ht_ep
                    (sessBound_mono_noop hact.sess rfl) rfl rfl (fun h => nomatch h)
                    (fun h => nomatch h) (fun _ _ h => nomatch h)
                  exact ⟨rfl, (fun _ _ _ hpl_f _ _ _ => by rw [hpl_f] at hg_pl; exact nomatch hg_pl),
                    hboth.1, hboth.2⟩
                · let kk := cka.receive (s.st P).γ Tn
                  simp only [StateT.run_bind]
                  refine S.bind (lookupMultiBucketF_false_hoare S t kk.2 es0.h) fun ⟨_, h1⟩ => ?_
                  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                  refine S.pure _ fun ns sc ⟨hc1, hs1, hb1, hact⟩ => ?_
                  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
                    not_lt] at hg_adm
                  let reg := regSessMultiBucket (q + 1) false tL t kk.2 h1
                  have hreg_c : reg.2.cache = es0.h.cache := by
                    dsimp [reg, regSessMultiBucket]; split_ifs <;> exact hc1
                  have hreg_b : reg.2.book = es0.h.book := by
                    dsimp [reg, regSessMultiBucket]; split_ifs <;> exact hb1
                  have hsess1 : SessBound q false (rem + 1) h1 :=
                    fun τ => by rw [hs1]; exact hact.sess τ
                  have hlt_q : (h1.sessions t).length < q + 1 := sessBound_lt hsess1 t
                  have htH_le : healEpoch tL ≤ t := healEpoch_le_of_validGuess hg_vg
                  have hsl_reg : slotEpoch (q + 1) false tL reg.1 = t :=
                    (regSessMultiBucket_slotEpoch (Nat.succ_pos q) false tL t kk.2 h1 htH_le hlt_q).1
                  have hboth := activeInv_s_upd_of_startRecv
                    (γ' := kk.1) (σ' := (prng.up (s.st P).root kk.2).1) (rsv := .inr reg.1)
                    hact hsends_f ht_ep (sessBound_regSess hsess1) hreg_c hreg_b
                    (fun h => nomatch h) (fun h => nomatch h)
                    (fun sIdx _ hrsv => by
                      injection hrsv with heq; subst heq
                      exact ⟨hsl_reg, hg_vg, hg_adm.1⟩)
                  exact ⟨hreg_c, (fun _ _ _ _ _ rs hvR => by simp at hvR), hboth.1, hboth.2⟩
                · let kk := cka.receive (s.st P).γ Tn
                  simp only [StateT.run_bind]
                  refine S.bind (lookupMultiBucketF_false_hoare S t kk.2 es0.h) fun ⟨k', h1⟩ => ?_
                  simp only [StateT.run_pure]
                  refine S.pure _ fun ns sc ⟨hc1, hs1, hb1, hact⟩ => ?_
                  have hboth := activeInv_s_upd_of_startRecv
                    (γ' := kk.1) (σ' := (prng.up (s.st P).root kk.2).1)
                    (rsv := .inl (fs.initReceiver k'))
                    hact hsends_f ht_ep (sessBound_mono_noop hact.sess hs1) hc1 hb1
                    (fun h => nomatch h) (fun h => nomatch h) (fun _ _ h => nomatch h)
                  exact ⟨hc1, fun _ _ _ _ hvg_t _ _ => by simp [hvg_t] at hg_vg, hboth.1, hboth.2⟩
                · simp only [StateT.run_pure]
                  exact S.pure _ fun _ _ hact =>
                    ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                     hact.wf, hact.sync, hact.forged, hact.main⟩
                · simp only [StateT.run_pure]
                  exact S.pure _ fun _ _ hact =>
                    ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                     hact.wf, hact.sync, hact.forged, hact.main⟩
          | none =>
            cases gMain with
            | true =>
              simp only [↓reduceIte]
              split_ifs <;> simp only [StateT.run_pure]
              · exact S.pure _ fun _ _ _ => trivial
              · exact S.pure _ fun _ _ hact =>
                  ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                   hact.wf, hact.sync, hact.forged, hact.main⟩
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              split_ifs with hg_adm hg_tH hg_pl hg_vg hg_ge
              · simp only [StateT.run_pure]; exact S.pure _ fun _ _ _ => trivial
              · simp only [StateT.run_pure]
                refine S.pure _ fun ns sc hact => ?_
                let kk := cka.receive (s.st P).γ Tn
                let p := prng.up (s.st P).root kk.2
                have hboth := activeInv_s_upd_of_startRecv
                  (γ' := kk.1) (σ' := p.1) (rsv := .inl (fs.initReceiver p.2))
                  hact hsends_f ht_ep
                  (sessBound_mono_noop hact.sess rfl) rfl rfl (fun h => nomatch h)
                  (fun h => nomatch h) (fun _ _ h => nomatch h)
                exact ⟨rfl, (fun _ _ _ hpl_f _ _ _ => by rw [hpl_f] at hg_pl; exact nomatch hg_pl),
                  hboth.1, hboth.2⟩
              · let kk := cka.receive (s.st P).γ Tn
                simp only [StateT.run_bind]
                refine S.bind (lookupMultiBucketF_false_hoare S t kk.2 es0.h) fun ⟨_, h1⟩ => ?_
                simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                refine S.pure _ fun ns sc ⟨hc1, hs1, hb1, hact⟩ => ?_
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
                  not_lt] at hg_adm
                let reg := regSessMultiBucket (q + 1) false tL t kk.2 h1
                have hreg_c : reg.2.cache = es0.h.cache := by
                  dsimp [reg, regSessMultiBucket]; split_ifs <;> exact hc1
                have hreg_b : reg.2.book = es0.h.book := by
                  dsimp [reg, regSessMultiBucket]; split_ifs <;> exact hb1
                have hsess1 : SessBound q false (rem + 1) h1 :=
                  fun τ => by rw [hs1]; exact hact.sess τ
                have hlt_q : (h1.sessions t).length < q + 1 := sessBound_lt hsess1 t
                have htH_le : healEpoch tL ≤ t := healEpoch_le_of_validGuess hg_vg
                have hsl_reg : slotEpoch (q + 1) false tL reg.1 = t :=
                  (regSessMultiBucket_slotEpoch (Nat.succ_pos q) false tL t kk.2 h1 htH_le hlt_q).1
                have hboth := activeInv_s_upd_of_startRecv
                  (γ' := kk.1) (σ' := (prng.up (s.st P).root kk.2).1) (rsv := .inr reg.1)
                  hact hsends_f ht_ep (sessBound_regSess hsess1) hreg_c hreg_b
                  (fun h => nomatch h) (fun h => nomatch h)
                  (fun sIdx _ hrsv => by
                    injection hrsv with heq; subst heq
                    exact ⟨hsl_reg, hg_vg, hg_adm.1⟩)
                exact ⟨hreg_c, (fun _ _ _ _ _ rs hvR => by simp at hvR), hboth.1, hboth.2⟩
              · let kk := cka.receive (s.st P).γ Tn
                simp only [StateT.run_bind]
                refine S.bind (lookupMultiBucketF_false_hoare S t kk.2 es0.h) fun ⟨k', h1⟩ => ?_
                simp only [StateT.run_pure]
                refine S.pure _ fun ns sc ⟨hc1, hs1, hb1, hact⟩ => ?_
                have hboth := activeInv_s_upd_of_startRecv
                  (γ' := kk.1) (σ' := (prng.up (s.st P).root kk.2).1)
                  (rsv := .inl (fs.initReceiver k'))
                  hact hsends_f ht_ep (sessBound_mono_noop hact.sess hs1) hc1 hb1
                  (fun h => nomatch h) (fun h => nomatch h) (fun _ _ h => nomatch h)
                exact ⟨hc1, fun _ _ _ _ hvg_t _ _ => by simp [hvg_t] at hg_vg, hboth.1, hboth.2⟩
              · simp only [StateT.run_pure]
                exact S.pure _ fun _ _ hact =>
                  ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                   hact.wf, hact.sync, hact.forged, hact.main⟩
              · simp only [StateT.run_pure]
                exact S.pure _ fun _ _ hact =>
                  ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
                   hact.wf, hact.sync, hact.forged, hact.main⟩
        refine S.bind hstart fun ⟨resStart, h_mid⟩ => ?_
        cases resStart with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact S.pure _ fun _ _ _ => trivial
        | some inner =>
          cases inner with
          | none =>
            simp only [StateT.run_pure, pure_bind]
            exact S.pure _ fun _ _ hact_s => hact_s
          | some tup =>
            rcases tup with ⟨γ', σ', rsv⟩
            simp only [pure_bind]
            let s_mid : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) :=
              { s.st P with tcur := t, γ := γ', root := σ',
                            vR := Function.update (s.st P).vR t (some rsv) }
            refine S.conseq
              (S.and_prop
                (h_mid.cache = es0.h.cache ∧
                 (gMain = false → t = s.epoch P + 1 →
                   isHonestHdrMultiBucket es0.h c.1 = false → postLeak tL s = false →
                   validGuessBucketParAuth 1 tL par t = true →
                   ∀ rs, s_mid.vR t ≠ some (.inl rs)))
                (Pre := fun ns sc =>
                  ActiveInv q qep rem gMain tL par { es0 with h := h_mid } none ns sc ∧
                  ActiveInv q qep rem gMain tL par
                    { g := { es0.g with st := Function.update es0.g.st P s_mid,
                                        epoch := Function.update es0.g.epoch P (max (es0.g.epoch P) t) },
                      h := h_mid, abort := false } none ns sc)
                fun ⟨hc_eq, hfn⟩ => by
                  have hstep := fsRecv_step_hoare S q qep rem cka prng fs gMain tL par P c rec
                    es0 s_mid h_mid hsends_f hc_eq hfn
                  simp only at hstep
                  convert hstep using 1
                  simp only [hk, s_mid, s, t]
                  congr 1
                  cases Function.update (es0.g.st P).vR c.1.1 (some rsv) c.1.1 with
                  | none => simp only
                  | some v =>
                    simp only
                    congr 1; funext x
                    rcases x with _ | _ | ⟨v', i, m⟩ <;> simp only)
              (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩)
              (fun _ _ _ h => h)
    · -- Same-or-earlier epoch: `t ≤ s.epoch P` (`s_mid = s.st P`, `s_upd = s`, `h_mid = es0.h`)!
      simp only [pure_bind]
      have ht_le : t ≤ s.epoch P := by omega
      have hs_upd_eq : { s with st := Function.update s.st P (s.st P),
                                epoch := Function.update s.epoch P (max (s.epoch P) t) } = s := by
        have hm_eq : max (s.epoch P) t = s.epoch P := Nat.max_eq_left ht_le
        rw [Function.update_eq_self, hm_eq, Function.update_eq_self]
      refine S.conseq
        (by
          have hstep := fsRecv_step_hoare S q qep rem cka prng fs gMain tL par P c rec
            es0 (s.st P) es0.h hsends_f rfl (fun _ ht_ep _ _ _ _ _ => by dsimp only [s, t] at ht_le; omega)
          simp only at hstep
          convert hstep using 1
          dsimp only [hk, s, t]
          congr 1
          cases (es0.g.st P).vR c.1.1 with
          | none => simp only
          | some v =>
            simp only
            congr 1; funext x
            rcases x with _ | _ | ⟨v', i, m⟩ <;> simp only)
        (fun ns sc hact => by
          have hact' : ActiveInv q qep rem gMain tL par es0 none ns sc :=
            ⟨hact.no_abort, hact.no_win, hact.winEp_none, sessBound_mono_noop hact.sess rfl,
             hact.wf, hact.sync, hact.forged, hact.main⟩
          refine ⟨hact', ?_⟩
          dsimp only [s] at hs_upd_eq
          rw [hs_upd_eq]
          exact ⟨rfl, hact'.no_win, rfl, hact'.sess, hact'.wf, hact'.sync,
            hact'.forged, hact'.main⟩)
        (fun _ _ _ h => h)

/-! ## 3. Active `Deliver` (`i₃`) and `Inject` (`i₄`) Step Proofs -/

private theorem accept_st_update_self {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    { (s.accept P st' pos) with st := Function.update (s.accept P st' pos).st P st' } =
      s.accept P st' pos := by
  cases s; simp [GameState.accept, GameState.delete]

theorem i3_deliver_active_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × (ℕ × C))
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par st.1 st.2)
      (fun p ns' sc' => FalseInv q qep rem gMain tL par p.2 ns' sc')
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL
        (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  cases winEp0 with
  | some w =>
    exact S.conseq S.exfalso (fun _ _ hact => nomatch hact.winEp_none) (fun _ _ _ h => h)
  | none =>
    change S.H _ _
      (StateT.run (σ := FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) (do
        let (es_cur, winEp_cur) ← get
        let (out, es') ← StateT.lift ((deliverE hk maxSkip (bucketAuthCfg 1 tL) (P, c)).run es_cur)
        set (es', winEp_cur)
        return out) (es0, none))
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift,
      pure_bind, bind_assoc]
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hguard
    · simp only [StateT.run_pure, pure_bind, StateT.run_set]
      exact S.pure _ fun _ _ hact => Or.inr
        ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
         hact.wf, hact.sync, hact.forged, hact.main⟩
    · cases hinTr : es0.g.inTransit P.other c with
      | none =>
        simp only [StateT.run_pure, pure_bind, StateT.run_set]
        exact S.pure _ fun _ _ hact => Or.inr
          ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
           hact.wf, hact.sync, hact.forged, hact.main⟩
      | some r =>
        have hr_mem : r ∈ es0.g.trans := List.mem_of_find?_eq_some hinTr
        have hr_ct : r.ct = c := by
          have hf := List.find?_some hinTr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
          exact hf.2
        -- Extract `r.pos.epoch = c.1.1` via `and_prop` from `EngineWF.trans_wf`!
        refine S.conseq
          (S.and_prop (r.pos.epoch = c.1.1) fun hr_ep => ?_)
          (fun _ _ hact => ⟨by rw [← hr_ct]; exact (hact.wf.trans_wf r hr_mem).1.symm, hact⟩)
          (fun _ _ _ h => h)
        have hmust : ((bucketAuthCfg (M := M) 1 tL).deliverWin &&
            es0.g.mustBeCorrect maxSkip P r) = false := rfl
        dsimp only [hk]
        rw [StateT.run_bind, bind_assoc]
        refine S.bind (liftH_false_hoare S es0 _
          (vRecv_hoare S q qep rem cka prng fs gMain tL par P c (some r) es0))
          fun ⟨vOut, es1⟩ => ?_
        cases vOut with
        | none =>
          unfold abortE
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, StateT.run_set]
          exact S.pure _ fun _ _ _ => Or.inl ⟨Or.inl rfl, fun _ h => nomatch h⟩
        | some inner =>
          cases inner with
          | none =>
            simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              pure_bind, StateT.run_set]
            exact S.pure _ fun _ _ ⟨h', heq, hact'⟩ => by subst heq; exact Or.inr hact'
          | some quad =>
            rcases quad with ⟨st', t', i', m'⟩
            dsimp only [commitE, hooksFSMultiBucketAuth, liftH]
            simp only [StateT.run_bind, StateT.run_pure,
              hmust, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              pure_bind, StateT.run_set]
            refine S.pure _ fun _ _ ⟨h', heq, ht'_eq, _, hacc, _⟩ => ?_
            subst heq; subst ht'_eq
            rw [accept_st_update_self]
            exact Or.inr (hacc r.pos hr_ep (Or.inr ⟨r, hr_mem, hr_ct, rfl⟩))

theorem i4_inject_active_hoare
    {KC Γ CCoins T I KR RSt K SS RS M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (S : FSFalseSemantics SS RS T M C) (q qep maxSkip rem : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × C))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (P : Party) (c : Header T × (ℕ × C))
    (st : FSMultiBucketAuthEState Γ T RSt SS RS M (ℕ × C) K I) :
    let hk := hooksFSMultiBucketAuth (q + 1) cka prng fs 1 qep gMain tL par false
    S.H (ActiveInv q qep (rem + 1) gMain tL par st.1 st.2)
      (fun p ns' sc' => FalseInv q qep rem gMain tL par p.2 ns' sc')
      ((implFSMultiBucketAuth hk 1 qep maxSkip gMain tL
        (.inr (.inl (.inr ⟨P, c⟩)))).run st) := by
  intro hk
  rcases st with ⟨es0, winEp0⟩
  cases winEp0 with
  | some w =>
    exact S.conseq S.exfalso (fun _ _ hact => nomatch hact.winEp_none) (fun _ _ _ h => h)
  | none =>
    change S.H _ _
      ((do
        let ((es0 : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × (ℕ × C))
          (FSMultiBucketAuthState T RSt K I (ℕ × C))), (winEp0 : Option ℕ)) ← get
        let wasWin := es0.g.win
        let isNewForged :=
          decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrMultiBucket es0.h c.1
        let (out, es') ← StateT.lift ((injectE hk 3 qep (bucketAuthCfg 1 tL) (P, c)).run es0)
        let winEp' :=
          if !wasWin && es'.g.win && (gMain || isNewForged) then some c.1.1 else winEp0
        set (es', winEp')
        return out).run (es0, none))
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift,
      pure_bind, bind_assoc]
    -- Extract `es0.g.win = false` and `(es0.g.st P).tcur = es0.g.epoch P` via `and_prop`!
    refine S.conseq
      (S.and_prop (es0.g.win = false ∧ (es0.g.st P).tcur = es0.g.epoch P) fun ⟨hnw, htcurP⟩ => ?_)
      (fun _ _ hact => ⟨⟨hact.no_win, hact.wf.vp_tcur P⟩, hact⟩)
      (fun _ _ _ h => h)
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hguard
    · simp only [StateT.run_pure, pure_bind, StateT.run_set,
        hnw]
      exact S.pure _ fun _ _ hact => Or.inr
        ⟨hact.no_abort, hact.no_win, rfl, sessBound_mono_noop hact.sess rfl,
         hact.wf, hact.sync, hact.forged, hact.main⟩
    · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hguard
      rcases hguard with ⟨⟨⟨_, _⟩, hinTrans_f⟩, hsafeInj⟩
      simp only [StateT.run_bind, bind_assoc]
      refine S.bind (liftH_false_hoare S es0 _
        (vRecv_hoare S q qep rem cka prng fs gMain tL par P c none es0))
        fun ⟨vOut, es1⟩ => ?_
      cases vOut with
      | none =>
        unfold abortE
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, StateT.run_set]
        exact S.pure _ fun _ _ ⟨h', heq, _⟩ => by
          subst heq
          simp only [hnw]
          exact Or.inl ⟨Or.inl rfl, fun _ h => nomatch h⟩
      | some inner =>
        cases inner with
        | none =>
          simp only [StateT.run_pure, pure_bind,
            StateT.run_set]
          exact S.pure _ fun _ _ ⟨h', heq, hact'⟩ => by
            subst heq
            simp only [hnw]
            exact Or.inr hact'
        | some quad =>
          rcases quad with ⟨st', t', i', m'⟩
          by_cases hqep_gt : qep + 1 < t'
          · simp only [hqep_gt, ↓reduceIte, StateT.run_pure, pure_bind,
              StateT.run_set]
            refine S.pure _ fun _ _ ⟨h', heq, _, hno_comm, _, _⟩ => ?_
            subst heq
            simp only [hnw]
            exact Or.inr (hno_comm (Or.inl hqep_gt))
          · simp only [hqep_gt, ↓reduceIte]
            have hle_qep : t' ≤ qep + 1 := Nat.le_of_not_lt hqep_gt
            let pos : Pos := ⟨P.other, t', i'⟩
            by_cases htriv : es0.g.trivial 3 pos = true
            · have htriv' : es0.g.trivial 3 ⟨P.other, t', i'⟩ = true := htriv
              simp only [htriv', ↓reduceIte]
              unfold commitE
              dsimp only [hk, hooksFSMultiBucketAuth]
              simp only [StateT.run_bind, StateT.run_pure,
                pure_bind, StateT.run_set]
              refine S.pure _ fun _ _ ⟨h', heq, ht'_eq, _, hacc, _⟩ => ?_
              subst heq
              rw [accept_st_update_self]
              have hwin_acc : (es0.g.accept P st' ⟨P.other, t', i'⟩).win = false := hnw
              simp only [hwin_acc, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact Or.inr (hacc pos rfl (Or.inl rfl))
            · have htriv' : ¬es0.g.trivial 3 ⟨P.other, t', i'⟩ = true := htriv
              simp only [htriv', Bool.false_eq_true, ↓reduceIte]
              simp only [Bool.not_eq_true] at htriv
              dsimp only [bucketAuthCfg, Nat.reduceAdd]
              by_cases hadm : lastLeakGuessAdmissible 3 tL t' = true
              · simp only [hadm, ↓reduceIte, StateT.run_bind, StateT.run_modify,
                  StateT.run_pure, pure_bind, StateT.run_set]
                refine S.pure _ fun _ _ ⟨h', heq, ht'_eq, _, _, hwin_safe⟩ => ?_
                subst heq
                rcases hwin_safe (Bool.eq_false_iff.mpr hinTrans_f) hsafeInj hle_qep htriv hadm
                  with ⟨hws_main, hws_forged⟩
                subst ht'_eq
                simp only [hnw, Bool.not_false, Bool.true_and]
                cases hgm : gMain with
                | true =>
                  simp only [Bool.true_or, ↓reduceIte]
                  exact Or.inl ⟨Or.inr rfl, hws_main hgm⟩
                | false =>
                  simp only [Bool.false_or]
                  by_cases hnf :
                      (decide (c.1.1 = (es0.g.st P).tcur + 1) &&
                        !isHonestHdrMultiBucket es0.h c.1) = true
                  · simp only [hnf, ↓reduceIte]
                    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hnf
                    rw [htcurP] at hnf
                    exact Or.inl ⟨Or.inr rfl, hws_forged hgm hnf.1 hnf.2⟩
                  · simp only [hnf, Bool.false_eq_true, ↓reduceIte]
                    exact Or.inl ⟨Or.inr rfl, fun _ h => nomatch h⟩
              · simp only [hadm, Bool.false_eq_true, ↓reduceIte,
                  StateT.run_pure, pure_bind, StateT.run_set]
                simp only [Bool.not_eq_true] at hadm
                refine S.pure _ fun _ _ ⟨h', heq, _, hno_comm, _, _⟩ => ?_
                subst heq
                simp only [hnw]
                exact Or.inr (hno_comm (Or.inr hadm))

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndFalseRecv
