/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect

/-! # Shared Helpers, Exits, and Per-Session Invariant for `BucketFSAuthBridgeForgedHop` -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState fromAEADPRG ReceiveResult
  transmitImpl deliverImpl injectImpl)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt HState hInit hp DG transmitHWith deliverH injectH
  SpecialOps)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (WFSeed SyncRM SyncRML syncRML_init mkRState keyAt
  transmit_syncRML inject_syncRML_of_not_lookahead injectH_run_of_wfSeed_not_lookahead
  deliverH_run_of_wfSeed isCompromised_of_wfState_lt)
open _root_.CryptoGames.FSAEAD.Thm5On (InTransitOk inTransitOk_hInit inTransitOk_of_transmitH
  deliver_syncRML_on inTransitOk_of_injectH_not_lookahead inTransitOk_of_injectH_lookahead_none
  pure_eq_iff)
open _root_.CryptoGames.SM (GameState Record Pos healedBy ltOpt maxOpt canon
  lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header healEpoch
  FSMultiSpec FSMultiBook)
open _root_.CryptoGames.SM.Engine (VP EState Hooks vSend deliverE injectE commitE abortE liftH)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lChainPRG lAead lAeadR lIdeal lPubOf lFS)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalRoundTripShort
  maxForwardJumps rustLenBound)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.ProstMsgAeadCorrect (lAeadR_correctOn_short_proof
  lPubOf_enc_short_proof)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (postLeak
  LocalBucketAuthState implLocalBucketAuthGen bucketAuthCfg isHonestHdrLocalBucket)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (validGuessBucketParAuth)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (mSessMain
  healedBy_imp_healEpoch_le lFS_initSender_eq lFS_initReceiver_eq
  lFS_send_eq lFS_receive_eq injectL_lookahead_some_accepted)

/-! ### 1. Forged-Slot Arithmetic & `CompUnhealed` -/

@[expose] def sIdxForged (q : ℕ) (tL : Option ℕ) (t0 idx : ℕ) : ℕ :=
  (q + 1) * (t0 - healEpoch tL) + idx + 1

theorem sIdxForged_lt_mSessMain (q qep : ℕ) (tL : Option ℕ) (par : Bool) {t0 idx : ℕ}
    (ht0 : !(decide (qep + 1 < t0)) = true) (hv : validGuessBucketParAuth 1 tL par t0 = true)
    (hidx : idx < q) : sIdxForged q tL t0 idx < mSessMain q qep tL := by
  have hle : t0 ≤ qep + 1 := by simp at ht0; exact ht0
  have hh : healEpoch tL ≤ t0 := healedBy_imp_healEpoch_le _ _ (by
    simp [validGuessBucketParAuth, lastLeakGuessAdmissible] at hv; exact hv.1)
  unfold sIdxForged mSessMain
  have hmul : (q + 1) * (t0 - healEpoch tL + 1) ≤ (q + 1) * ((qep + 2) - healEpoch tL) :=
    Nat.mul_le_mul_left (q + 1) (by omega)
  have hstep : (q + 1) * (t0 - healEpoch tL) + idx + 1 < (q + 1) * (t0 - healEpoch tL + 1) := by
    rw [Nat.mul_succ]; omega
  exact Nat.lt_of_lt_of_le hstep hmul

theorem sIdxForged_inj {q : ℕ} {tL : Option ℕ} {t1 idx1 t2 idx2 : ℕ}
    (ht1 : healEpoch tL ≤ t1) (ht2 : healEpoch tL ≤ t2) (hi1 : idx1 < q) (hi2 : idx2 < q)
    (heq : sIdxForged q tL t1 idx1 = sIdxForged q tL t2 idx2) : t1 = t2 ∧ idx1 = idx2 := by
  have hpos : 0 < q + 1 := Nat.succ_pos q
  have heq' : (t1 - healEpoch tL) * (q + 1) + (idx1 + 1) = (t2 - healEpoch tL) * (q + 1) + (idx2 + 1) := by
    unfold sIdxForged at heq; rw [Nat.mul_comm (t1 - healEpoch tL), Nat.mul_comm (t2 - healEpoch tL)]; omega
  have hdiv1 : ((t1 - healEpoch tL) * (q + 1) + (idx1 + 1)) / (q + 1) = t1 - healEpoch tL := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hdiv2 : ((t2 - healEpoch tL) * (q + 1) + (idx2 + 1)) / (q + 1) = t2 - healEpoch tL := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have ht_eq : t1 = t2 := by have := hdiv1.symm.trans (congrArg (· / (q + 1)) heq' |>.trans hdiv2); omega
  subst ht_eq; unfold sIdxForged at heq; exact ⟨rfl, by omega⟩

theorem not_isSome_and_eq_healEpoch_of_validGuess (tL : Option ℕ) (par : Bool) (t0 : ℕ)
    (hv : validGuessBucketParAuth 1 tL par t0 = true) :
    (tL.isSome && decide (t0 = healEpoch tL)) = false ∧
    (tL.isSome && (t0 == healEpoch tL)) = false := by
  cases tL with
  | none => simp
  | some l =>
    simp only [validGuessBucketParAuth, lastLeakGuessAdmissible, healedBy, Bool.and_eq_true,
      decide_eq_true_eq] at hv
    have hne : t0 ≠ healEpoch (some l) := by simp [healEpoch]; omega
    simp [hne, beq_eq_false_iff_ne]

@[expose] def CompUnhealed {St M C : Type} (g : GameState St M C) : Prop :=
  (∀ r ∈ g.trans, r.pos.epoch ≤ g.epoch r.pos.sender) ∧ (∀ p ∈ g.comp, healedBy g.tL 3 p.epoch = false)

theorem compUnhealed_init {St M C : Type} (st : Party → St) (b : Bool) :
    CompUnhealed ({ st := st, b := b } : GameState St M C) :=
  ⟨fun _ hr => by simp at hr, fun _ hp => by simp at hp⟩

private theorem healedBy_false_mono_maxOpt {tL : Option ℕ} {l ep : ℕ}
    (h : healedBy tL 3 ep = false) : healedBy (some (maxOpt tL l)) 3 ep = false := by
  cases tL <;> [simp [healedBy] at h; (simp only [healedBy, decide_eq_false_iff_not, not_le] at h ⊢; simp only [maxOpt]; omega)]

theorem compUnhealed_epMgmt {St M C : Type} {g g₁ : GameState St M C} {qep : ℕ} {P : Party}
    {bad : Bool} (hcu : CompUnhealed g) (hep : g.epMgmt 3 qep P bad = some g₁) : CompUnhealed g₁ := by
  rcases hcu with ⟨htr, hcp⟩; unfold GameState.epMgmt GameState.leak at hep
  split at hep
  · split at hep <;> [cases hep; cases hep]
    by_cases hbad : (bad && !g.safeCh 3 P) = true
    · simp only [hbad, ↓reduceIte]; refine ⟨fun r hr => ?_, fun p hp => healedBy_false_mono_maxOpt (hcp p hp)⟩
      have hle := htr r hr
      by_cases hP : r.pos.sender = P <;> [subst hP; skip] <;> [ (simp; omega); (simp [Function.update_of_ne hP]; exact hle) ]
    · simp only [hbad]; refine ⟨fun r hr => ?_, fun p hp => hcp p hp⟩
      have hle := htr r hr
      by_cases hP : r.pos.sender = P <;> [subst hP; skip] <;> [ (simp; omega); (simp [Function.update_of_ne hP]; exact hle) ]
  · split at hep <;> [cases hep; (cases hep; exact ⟨htr, hcp⟩)]

theorem compUnhealed_record {St M C : Type} {g₁ : GameState St M C} {P : Party} {st' : St}
    {recE : Record M C} (hcu : CompUnhealed g₁)
    (hep : recE.pos.epoch = g₁.epoch P ∧ recE.pos.sender = P) :
    CompUnhealed (g₁.record 3 P st' recE false) := by
  rcases hcu with ⟨htr, hcp⟩; refine ⟨fun r hr => ?_, fun p hp => ?_⟩
  · simp only [GameState.record, List.mem_cons] at hr ⊢
    rcases hr with rfl | hr <;> [rw [hep.1, hep.2]; exact htr r hr]
  · simp only [GameState.record] at hp ⊢
    split at hp
    · exact hcp p hp
    · rename_i hnsafe; rcases List.mem_cons.mp hp with rfl | hp
      · simp only [GameState.safeCh, Bool.not_eq_true] at hnsafe; rw [hep.1]; exact hnsafe
      · exact hcp p hp

theorem compUnhealed_accept {St M C : Type} [DecidableEq M] [DecidableEq C]
    {g : GameState St M C} {P : Party} {st' : St} {pos : Pos} (hcu : CompUnhealed g) :
    CompUnhealed (g.accept P st' pos) := by
  rcases hcu with ⟨htr, hcp⟩; refine ⟨fun r hr => ?_, fun p hp => ?_⟩
  · simp only [GameState.accept, GameState.delete, List.mem_filter] at hr ⊢
    have hle := htr r hr.1
    by_cases hP : r.pos.sender = P <;> [subst hP; skip] <;> [ (simp; omega); (simp [Function.update_of_ne hP]; exact hle) ]
  · simp only [GameState.accept, GameState.delete, List.mem_filter] at hp ⊢; exact hcp p hp.1

theorem compUnhealed_afterCorr {St M C : Type} {g : GameState St M C} {P : Party}
    (hcu : CompUnhealed g) : CompUnhealed (g.afterCorr P) := by
  rcases hcu with ⟨htr, hcp⟩; refine ⟨fun r hr => ?_, fun p hp => ?_⟩
  · simp only [GameState.afterCorr, GameState.leak] at hr ⊢; exact htr r hr
  · simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
      List.mem_filter] at hp ⊢
    rcases hp with ⟨r, ⟨hr, _⟩, rfl⟩ | hp
    · have hmax : r.pos.epoch ≤ max (g.epoch .A) (g.epoch .B) := le_trans (htr r hr)
        (by cases r.pos.sender <;> [exact le_max_left _ _; exact le_max_right _ _])
      have hopt : max (g.epoch .A) (g.epoch .B) ≤ maxOpt g.tL (max (g.epoch .A) (g.epoch .B)) := by
        cases g.tL <;> simp [maxOpt]
      dsimp only [healedBy]; rw [decide_eq_false_iff_not]; omega
    · exact healedBy_false_mono_maxOpt (hcp p hp)

theorem trivial_eq_false_of_healed {St M C : Type} [DecidableEq C]
    {g : GameState St M C} (hcu : CompUnhealed g) {pos : Pos}
    (hh : healedBy g.tL 3 pos.epoch = true) : g.trivial 3 pos = false := by
  unfold GameState.trivial; rw [hh]; simp only [Bool.not_true, Bool.and_false, Bool.or_false]
  rw [List.contains_eq_mem, decide_eq_false_iff_not]; intro hmem
  have hf := hcu.2 pos hmem; rw [hf] at hh; exact Bool.false_ne_true hh

/-! ### 2. Halted (`abort || win`), Lookahead-Win (`lfWin`), and Dead-Local (`LocDeadForged`) Exits -/

theorem authLosingConditionsAvoided_congr {St₁ St₂ Msg C : Type}
    (Δ : ℕ) (tLStar : Option ℕ) (tStar : ℕ)
    (g₁ : GameState St₁ Msg C) (g₂ : GameState St₂ Msg C)
    (hleaks : g₁.leaks = g₂.leaks) (hcorrs : g₁.corrs = g₂.corrs) :
    authLosingConditionsAvoided Δ tLStar tStar g₁ =
      authLosingConditionsAvoided Δ tLStar tStar g₂ := by
  simp [authLosingConditionsAvoided, canon, hleaks, hcorrs]

@[expose] def forgedParOut {St Msg C HS : Type} (Δ : ℕ) (tL : Option ℕ) (par : Bool)
    (es : EState St Msg C HS) (winEp : Option ℕ) : Bool :=
  match winEp with
  | none => false
  | some tWin =>
    !es.abort && es.g.win &&
      authLosingConditionsAvoided Δ tL tWin es.g &&
      (decide (Party.senderOf tWin == Party.A) == par)

@[expose] def LocEpochInv {Γv T Sv SSv RSv M E : Type}
    (g : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E) : Prop :=
  (∀ P : Party, (g.st P).id = P ∧ (g.st P).tcur = g.epoch P) ∧
  (∀ r ∈ g.trans, r.pos.epoch = r.ct.1.1)

theorem locEpochInv_init {Γv T Sv SSv RSv M E : Type}
    (γA γB : Γv) (σ : Sv) (ssB : SSv) (rsA : RSv) (b : Bool) :
    LocEpochInv ({ st := fun P => match P with
      | .A => (_root_.CryptoGames.SM.Construction.mkParties γA γB σ ssB rsA).1
      | .B => (_root_.CryptoGames.SM.Construction.mkParties γA γB σ ssB rsA).2, b := b } :
      _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E) :=
  ⟨fun P => by cases P <;> exact ⟨rfl, rfl⟩, fun _ hr => by simp at hr⟩

theorem vSend_support_id_tcur {ι : Type} {tspec : OracleSpec ι}
    {Γ T Sig SS RS M E CCoins Γv Sv SSv RSv HS : Type} [Inhabited E]
    (impl : QueryImpl (unifSpec + tspec) ProbComp)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E)
    (P : Party) (m : M) (r : Option CCoins) (h0 h' : HS)
    (st' : VP Γv T Sv SSv RSv) (ct : Header T × E) (hid : (ctx.st P).id = P)
    (hz : (some (st', ct), h') ∈ support (simulateQ impl ((vSend hk ctx P (ctx.st P) m none r).run h0))) :
    st'.id = P ∧
    st'.tcur = (if P.sendsIn ((ctx.st P).tcur + 1) then (ctx.st P).tcur + 1 else (ctx.st P).tcur) ∧
    ct.1.1 = st'.tcur := by
  unfold vSend at hz; rw [hid] at hz
  by_cases hs : P.sendsIn ((ctx.st P).tcur + 1) = true
  · simp only [hs, ↓reduceIte, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨⟨sr, _⟩, _, hz⟩
    cases sr with
    | none => simp at hz
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss⟩; dsimp only at hz
      simp only [pure_bind, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨fr, _⟩, _, hz⟩
      cases fr with
      | none => simp at hz
      | some ve =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj hz with ⟨hsome, _⟩; injection hsome with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩; exact ⟨rfl, by simp [hs], rfl⟩
  · simp only [Bool.eq_false_iff.mpr hs, Bool.false_eq_true, ↓reduceIte, pure_bind] at hz
    cases hvs : (ctx.st P).vS with
    | none =>
      simp only [hvs, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rcases Prod.mk.inj hz with ⟨hsome, _⟩; injection hsome with hpair
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩; exact ⟨hid, by simp [hs], rfl⟩
    | some v =>
      simp only [hvs, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨fr, _⟩, _, hz⟩
      cases fr with
      | none => simp at hz
      | some ve =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj hz with ⟨hsome, _⟩; injection hsome with hpair
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩; exact ⟨hid, by simp [hs], rfl⟩

theorem locEpochInv_send {Γv T Sv SSv RSv M E : Type}
    {g s₁ : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E} {Δ qep : ℕ}
    {P : Party} {bad : Bool} {st' : VP Γv T Sv SSv RSv} (m : M) {ct : Header T × E}
    (hinv : LocEpochInv g) (hep : g.epMgmt Δ qep P bad = some s₁)
    (hid : st'.id = P)
    (htcur : st'.tcur = if P.sendsIn ((s₁.st P).tcur + 1) then (s₁.st P).tcur + 1 else (s₁.st P).tcur)
    (hct : ct.1.1 = st'.tcur) :
    LocEpochInv (s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ false) := by
  have hst_s₁ : s₁.st = g.st ∧ s₁.trans = g.trans ∧
      s₁.epoch = (if P.sendsIn (g.epoch P + 1) then Function.update g.epoch P (g.epoch P + 1) else g.epoch) := by
    unfold GameState.epMgmt GameState.leak at hep
    split_ifs at hep with hs hq1 hb hq2 <;>
      (injection hep with hs₁; subst hs₁; exact ⟨rfl, rfl, by simp [hs]⟩)
  rcases hst_s₁ with ⟨hst1, htr1, hep1⟩
  rw [hst1, (hinv.1 P).2] at htcur
  have hst'_ep : st'.tcur = s₁.epoch P := by
    rw [htcur, hep1]; split_ifs <;> simp
  refine ⟨fun Q => ?_, fun r hr => ?_⟩
  · simp only [GameState.record]
    by_cases hQ : Q = P
    · subst hQ; simp [hid, hst'_ep]
    · simp only [Function.update_of_ne hQ, hst1]
      refine ⟨(hinv.1 Q).1, ?_⟩
      rw [(hinv.1 Q).2, hep1]; split_ifs <;> simp [Function.update_of_ne hQ]
  · simp only [GameState.record, List.mem_cons, htr1] at hr
    rcases hr with rfl | hr <;> [exact hst'_ep.symm.trans hct.symm; exact hinv.2 r hr]

theorem vRecv_support_id_tcur {ι : Type} {tspec : OracleSpec ι}
    {Γ T Sig SS RS M E CCoins Γv Sv SSv RSv HS : Type}
    (impl : QueryImpl (unifSpec + tspec) ProbComp)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E)
    (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E))) (h0 h' : HS)
    (st' : VP Γv T Sv SSv RSv) (t' i' : ℕ) (m' : M)
    (hz : (some (some (st', t', i', m')), h') ∈ support (simulateQ impl
      ((_root_.CryptoGames.SM.Engine.vRecv hk ctx P (ctx.st P) c rec).run h0))) :
    t' = c.1.1 ∧ st'.id = (ctx.st P).id ∧ st'.tcur = max (ctx.st P).tcur c.1.1 := by
  unfold _root_.CryptoGames.SM.Engine.vRecv at hz
  simp only [pure_bind] at hz
  split_ifs at hz with hbad hnext
  · simp at hz
  · cases hc2 : c.1.2 with
    | none => simp [hc2] at hz
    | some Tn =>
      simp only [hc2, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨sr, _⟩, _, hz⟩
      rcases sr with _ | (_ | ⟨γ', σ', rs⟩) <;> try (simp at hz; done)
      simp only [Function.update_self, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨fr, _⟩, _, hz⟩
      rcases fr with _ | (_ | ⟨v', i1, m1⟩) <;> simp at hz
      rcases hz.1 with ⟨rfl, rfl, _, _⟩; exact ⟨rfl, rfl, by dsimp only; omega⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbad
    cases hvr : (ctx.st P).vR c.1.1 with
    | none => simp [hvr] at hz
    | some rs =>
      simp only [hvr, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hz
      rcases hz with ⟨⟨fr, _⟩, _, hz⟩
      rcases fr with _ | (_ | ⟨v', i1, m1⟩) <;> simp at hz
      rcases hz.1 with ⟨rfl, rfl, _, _⟩; exact ⟨rfl, rfl, by dsimp only; omega⟩

theorem locEpochInv_accept {Γv T Sv SSv RSv M E : Type} [DecidableEq M] [DecidableEq T] [DecidableEq E]
    {g : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E}
    {P : Party} {st' : VP Γv T Sv SSv RSv} {pos : Pos}
    (hinv : LocEpochInv g) (hid : st'.id = (g.st P).id) (htcur : st'.tcur = max (g.st P).tcur pos.epoch) :
    LocEpochInv (g.accept P st' pos) := by
  refine ⟨fun Q => ?_, fun r hr => ?_⟩
  · simp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp [hid, (hinv.1 Q).1, htcur, (hinv.1 Q).2]
    · simp [Function.update_of_ne hQ, (hinv.1 Q).1, (hinv.1 Q).2]
  · simp only [GameState.accept, GameState.delete, List.mem_filter] at hr; exact hinv.2 r hr.1

/-- Dead-state predicate for `implLocalBucketAuthGen` once `postLeak tL` turns `true` while
`winEp = none`. -/
@[expose] def LocDeadForged {Γv T Sv SSv RSv M E HS : Type} (tL : Option ℕ)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (winEp : Option ℕ) : Prop :=
  es.abort = true ∨
    (LocEpochInv es.g ∧
     (∀ tWin, winEp = some tWin → ∃ lk ∈ es.g.leaks, ltOpt tL lk = true ∧ lk < tWin) ∧
     ∃ lk cur, lk ∈ es.g.leaks ∧ ltOpt tL lk = true ∧ es.g.tL = some cur ∧ lk ≤ cur)

theorem locDeadForged_of_postLeak {Γv T Sv SSv RSv M E HS : Type} {tL : Option ℕ}
    {g₀ : _root_.CryptoGames.SM.Engine.Ctx Γv T Sv SSv RSv M E}
    {es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS}
    (hepoch : LocEpochInv es.g)
    (hpl₀ : postLeak tL g₀ = false) (hpl₁ : postLeak tL es.g = true)
    (htL : ∀ cur, es.g.tL = some cur → g₀.tL = some cur ∨ (∃ lk ∈ es.g.leaks, cur = lk)) :
    LocDeadForged tL es none := by
  unfold LocDeadForged; refine Or.inr ⟨hepoch, (fun _ h => by cases h), ?_⟩
  unfold postLeak at hpl₀ hpl₁
  cases hcur : es.g.tL with
  | none => rw [hcur] at hpl₁; cases tL <;> simp at hpl₁
  | some cur =>
    rw [hcur] at hpl₁; rcases htL cur hcur with hg0 | ⟨lk, hmem, rfl⟩
    · rw [hg0] at hpl₀; rw [hpl₀] at hpl₁; cases hpl₁
    · exact ⟨cur, cur, hmem, hpl₁, rfl, le_rfl⟩

theorem leak_postLeak_witness {St M C : Type} {tL : Option ℕ}
    {g₀ : GameState St M C} {l : ℕ} (hpl₁ : postLeak tL (g₀.leak l) = true) :
    let cur := maxOpt g₀.tL l
    cur ∈ (g₀.leak l).leaks ∧ ltOpt tL cur = true ∧ (g₀.leak l).tL = some cur :=
  ⟨by simp [GameState.leak], by simpa [postLeak, GameState.leak] using hpl₁, rfl⟩

theorem forgedParOut_eq_false_of_locDead {Γv T Sv SSv RSv M E HS : Type}
    (Δ : ℕ) (tL : Option ℕ) (par : Bool)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (winEp : Option ℕ)
    (hdead : LocDeadForged tL es winEp) : forgedParOut Δ tL par es winEp = false := by
  cases winEp with
  | none => rfl
  | some tWin =>
    rcases hdead with hab | ⟨_, hwin, _⟩
    · simp only [forgedParOut, hab, Bool.not_true, Bool.false_and]
    · rcases hwin tWin rfl with ⟨lk, hmem, hgt, hlt⟩
      have hall : (es.g.leaks.all fun x => !(ltOpt tL x && decide (x < tWin))) = false := by
        rw [List.all_eq_false]; exact ⟨lk, hmem, by simp [hgt, hlt]⟩
      simp only [forgedParOut, authLosingConditionsAvoided, hall, Bool.and_false, Bool.false_and]

private theorem leaks_sub_epMgmt {St M C : Type} {g s₁ : GameState St M C} {Δ qep : ℕ}
    {P : Party} {fl : Bool} (hep : g.epMgmt Δ qep P fl = some s₁) {x : ℕ} (hx : x ∈ g.leaks) :
    x ∈ s₁.leaks := by
  unfold GameState.epMgmt GameState.leak at hep
  split at hep
  · split at hep <;> [cases hep; (cases hep; split <;> [exact List.mem_cons_of_mem _ hx; exact hx])]
  · split at hep <;> [cases hep; (cases hep; exact hx)]

private theorem epMgmt_monotone_leaks_tL {St M C : Type} {g s₁ : GameState St M C} {Δ qep : ℕ}
    {P : Party} {fl : Bool} (hep : g.epMgmt Δ qep P fl = some s₁)
    {lk cur : ℕ} (hmem : lk ∈ g.leaks) (htL : g.tL = some cur) (hle : lk ≤ cur) :
    lk ∈ s₁.leaks ∧ ∃ cur', s₁.tL = some cur' ∧ lk ≤ cur' := by
  unfold GameState.epMgmt GameState.leak at hep
  split at hep
  · split at hep
    · cases hep
    · injection hep with hs₁; subst hs₁; split
      · refine ⟨List.mem_cons_of_mem _ hmem, maxOpt g.tL (g.epoch P + 1), rfl, ?_⟩
        rw [htL]; simp [maxOpt]; omega
      · exact ⟨hmem, cur, htL, hle⟩
  · split at hep <;> [cases hep; (injection hep with hs₁; subst hs₁; exact ⟨hmem, cur, htL, hle⟩)]

private theorem liftH_run {ι : Type} {tspec : OracleSpec ι} {Γ T Sig SS RS M E HS α : Type}
    (x : _root_.CryptoGames.SM.Engine.HM tspec HS α)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

private theorem modify_run {m : Type → Type} [Monad m] {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

private theorem injectE_win_implies_safeInj
    {Γ T Sig SS RS M E CCoins HS : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec HS Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (qep : ℕ) (tL : Option ℕ) (P : Party) (c : Header T × E)
    (es0 es' : EState (VP Γ T Sig SS RS) M (Header T × E) HS)
    (out : Option (_root_.CryptoGames.SM.RecvResult M))
    (hz : (out, es') ∈ support (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
      ((injectE hk 3 qep (bucketAuthCfg 1 tL) (P, c)).run es0)))
    (hnw : es0.g.win = false) (hw : es'.g.win = true) :
    es'.abort = es0.abort ∧ es'.g = { es0.g with win := true } ∧ es0.g.safeInj 3 = true := by
  dsimp only [injectE] at hz; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hguard
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases Prod.mk.inj hz with ⟨_, rfl⟩; rw [hnw] at hw; cases hw
  · have hsafe : es0.g.safeInj 3 = true := by
      revert hguard; cases es0.g.safeInj 3 <;> simp
    simp only [liftH_run, StateT.run_bind, bind_assoc, pure_bind,
      simulateQ_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨⟨v, h_v⟩, _, hz⟩
    rcases v with _ | (_ | ⟨st', t', i', m'⟩)
    · simp only [abortE, modify_run, StateT.run_bind, StateT.run_pure, pure_bind,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rcases Prod.mk.inj hz with ⟨_, rfl⟩; dsimp only at hw; rw [hnw] at hw; cases hw
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rcases Prod.mk.inj hz with ⟨_, rfl⟩; dsimp only at hw; rw [hnw] at hw; cases hw
    · dsimp only at hz; split_ifs at hz with hqep htriv hfull
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj hz with ⟨_, rfl⟩; dsimp only at hw; rw [hnw] at hw; cases hw
      · simp only [commitE, liftH_run, abortE, StateT.run_bind,
          bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
        rcases hz with ⟨⟨u, _⟩, _, hz⟩
        cases u with
        | none =>
          simp only [modify_run, StateT.run_bind, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, rfl, hz⟩; dsimp only at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rcases Prod.mk.inj hz with ⟨_, rfl⟩; dsimp only at hw; rw [hnw] at hw; cases hw
        | some new' =>
          simp only [StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, rfl, hz⟩; dsimp only at hz
          simp only [modify_run, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          rcases Prod.mk.inj hz with ⟨_, rfl⟩
          dsimp only [GameState.accept, GameState.delete] at hw; rw [hnw] at hw; cases hw
      · simp only [modify_run, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj hz with ⟨_, rfl⟩; exact ⟨rfl, rfl, hsafe⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj hz with ⟨_, rfl⟩; dsimp only at hw; rw [hnw] at hw; cases hw

theorem stepLocForged_preserves_locDead
    {Γ T Sig SS RS M E CCoins K I : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec
      (LocalBucketAuthState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (hcommit : ∀ ctx P old new, hk.commit ctx P old new = pure (some new))
    (qep maxSkip : ℕ) (tL : Option ℕ)
    (qry : (unifSpec + _root_.CryptoGames.SM.spec
      (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
    (winEp : Option ℕ) (hdead : LocDeadForged tL es winEp) :
    ∀ z ∈ support (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
      ((implLocalBucketAuthGen hk 1 qep maxSkip tL true qry).run (es, winEp))),
      LocDeadForged tL z.2.1 z.2.2 := by
  intro ⟨out, es1, we1⟩ hz; dsimp only
  rcases hdead with hab | ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
  · rcases qry with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inl] at hz
      simp only [stateT_lift_run, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, hpair⟩
      rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, rfl⟩; exact Or.inl hab
    · simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hab] at hz
      rcases hz with ⟨_, rfl, rfl⟩; exact Or.inl hab
    · simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
      rcases hz with ⟨_, rfl, rfl⟩; exact Or.inl hab
    · simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hab] at hz
      rcases hz with ⟨_, rfl, rfl⟩; exact Or.inl hab
    · simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hab] at hz
      rcases hz with ⟨_, rfl, rfl⟩; exact Or.inl hab
    · simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, hab] at hz
      rcases hz with ⟨_, rfl, rfl⟩; exact Or.inl hab
  · rcases qry with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inl] at hz
      simp only [stateT_lift_run, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, hpair⟩
      rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, rfl⟩
      exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases hg : es.abort || es.g.win
      · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hz
        cases hep : es.g.epMgmt 3 qep P r.isSome with
        | none =>
          simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rcases Prod.mk.inj (Prod.mk.inj hz).2 with ⟨rfl, rfl⟩
          exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
        | some s₁ =>
          rcases epMgmt_monotone_leaks_tL hep hmem htL hle with ⟨hmem₁, cur', htL₁, hle₁⟩
          simp only [hep, stateT_lift_run, StateT.run_bind,
            bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
          rcases hz with ⟨⟨res, h'⟩, hvsend, hz2⟩
          cases res with
          | none =>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hz2
            rcases Prod.mk.inj (Prod.mk.inj hz2).2 with ⟨rfl, rfl⟩; exact Or.inl rfl
          | some pair =>
            have hs₁_st : s₁.st = es.g.st := by
              unfold GameState.epMgmt GameState.leak at hep
              split_ifs at hep <;> (injection hep with h1; subst h1; try split_ifs) <;> rfl
            rcases vSend_support_id_tcur _ hk s₁ P m r es.h h' pair.1 pair.2
              (by rw [hs₁_st]; exact (hepoch.1 P).1) hvsend with ⟨hid', htcur', hct'⟩
            have hepoch' := locEpochInv_send m hepoch hep hid' htcur' hct'
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hz2
            rcases Prod.mk.inj (Prod.mk.inj hz2).2 with ⟨rfl, rfl⟩
            refine Or.inr ⟨hepoch', fun tWin hwe => ?_, lk, cur',
              by simpa [GameState.record] using hmem₁, hgt,
              by simpa [GameState.record] using htL₁, hle₁⟩
            rcases hwin tWin hwe with ⟨lk0, hm0, hg0, hl0⟩
            exact ⟨lk0, by simpa [GameState.record] using leaks_sub_epMgmt hep hm0, hg0, hl0⟩
      · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj (Prod.mk.inj hz).2 with ⟨rfl, rfl⟩
        exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rcases Prod.mk.inj (Prod.mk.inj hz).2 with ⟨rfl, rfl⟩
      exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
      simp only [stateT_lift_run, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨⟨_, es'⟩, hdel, hpair⟩
      rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, rfl⟩
      dsimp only [deliverE] at hdel; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hdel
      split at hdel
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hdel
        rcases Prod.mk.inj hdel with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
      · cases hinT : es.g.inTransit P.other c with
        | none =>
          simp only [hinT, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hdel
          rcases Prod.mk.inj hdel with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
        | some r =>
          simp only [hinT, liftH_run, StateT.run_bind, bind_assoc, pure_bind,
            simulateQ_bind, mem_support_bind_iff] at hdel
          rcases hdel with ⟨⟨vout, h_v⟩, hvrecv, hdel2⟩
          rcases vout with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, modify_run, StateT.run_bind, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hdel2
            rcases Prod.mk.inj hdel2 with ⟨_, rfl⟩; exact Or.inl rfl
          · dsimp only at hdel2; split at hdel2 <;>
              (simp only [modify_run, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hdel2;
               rcases Prod.mk.inj hdel2 with ⟨_, rfl⟩;
               exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩)
          · have hr_mem := List.mem_of_find?_eq_some hinT
            have hr_pred := List.find?_some hinT; simp only [Bool.and_eq_true, decide_eq_true_eq] at hr_pred
            have hr_ep : r.pos.epoch = c.1.1 := (hepoch.2 r hr_mem).trans (by rw [hr_pred.2])
            rcases vRecv_support_id_tcur _ hk es.g P c (some r) es.h h_v st' t' i' m' hvrecv with
              ⟨_, hid', htcur'⟩
            have hepoch_acc := locEpochInv_accept hepoch hid' (by rw [hr_ep]; exact htcur')
            simp only [commitE, hcommit, liftH_run, modify_run, StateT.run_bind, StateT.run_pure,
              bind_assoc, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hdel2
            rcases Prod.mk.inj hdel2 with ⟨_, rfl⟩
            have hupd_eq : Function.update (es.g.accept P st' r.pos).st P st' = (es.g.accept P st' r.pos).st := by
              ext Q; by_cases hQ : Q = P <;> [ (subst hQ; simp [GameState.accept]); simp [Function.update_of_ne hQ] ]
            split_ifs
            · exact Or.inr ⟨⟨by simpa [hupd_eq] using hepoch_acc.1, hepoch_acc.2⟩,
                fun tWin hwe => by simpa [GameState.accept, GameState.delete] using hwin tWin hwe,
                lk, cur, by simpa [GameState.accept, GameState.delete] using hmem,
                hgt, by simpa [GameState.accept, GameState.delete] using htL, hle⟩
            · exact Or.inr ⟨⟨by simpa [hupd_eq] using hepoch_acc.1, hepoch_acc.2⟩,
                fun tWin hwe => by simpa [GameState.accept, GameState.delete] using hwin tWin hwe,
                lk, cur, by simpa [GameState.accept, GameState.delete] using hmem,
                hgt, by simpa [GameState.accept, GameState.delete] using htL, hle⟩
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hz
      simp only [stateT_lift_run, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨⟨iout, es'⟩, hes', hpair⟩
      rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, rfl⟩
      simp only [Bool.not_true, Bool.false_or]
      by_cases hnew : (!es.g.win && es1.g.win &&
          (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrLocalBucket es.h c.1)) = true
      · simp only [hnew, ↓reduceIte]; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hnew
        rcases injectE_win_implies_safeInj hk qep tL P c es es1 iout hes' hnew.1.1 hnew.1.2 with
          ⟨_, hg_eq, hsafe⟩
        have hmin_le : min (es.g.epoch .A) (es.g.epoch .B) ≤ es.g.epoch P := by
          cases P <;> [exact min_le_left _ _; exact min_le_right _ _]
        have hlt_win : lk < c.1.1 := by
          unfold GameState.safeInj at hsafe; rw [htL] at hsafe
          simp only [healedBy, decide_eq_true_eq] at hsafe
          have htcur_eq := (hepoch.1 P).2; omega
        unfold LocDeadForged; rw [hg_eq]
        refine Or.inr ⟨hepoch, fun tWin hwe => ?_, lk, cur, hmem, hgt, htL, hle⟩
        injection hwe with htWin; subst htWin; exact ⟨lk, hmem, hgt, hlt_win⟩
      · simp only [Bool.eq_false_iff.mpr hnew, Bool.false_eq_true, ↓reduceIte]
        dsimp only [injectE] at hes'; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hes'
        split at hes'
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes'
          rcases Prod.mk.inj hes' with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
        · simp only [liftH_run, StateT.run_bind, bind_assoc, pure_bind,
            simulateQ_bind, mem_support_bind_iff] at hes'
          rcases hes' with ⟨⟨vout, h_v⟩, hvrecv, hes2⟩
          rcases vout with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, modify_run, StateT.run_bind, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes2
            rcases Prod.mk.inj hes2 with ⟨_, rfl⟩; exact Or.inl rfl
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes2
            rcases Prod.mk.inj hes2 with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
          · rcases vRecv_support_id_tcur _ hk es.g P c none es.h h_v st' t' i' m' hvrecv with
              ⟨ht'_eq, hid', htcur'⟩
            dsimp only at hes2; split_ifs at hes2
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes2
              rcases Prod.mk.inj hes2 with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
            · have hepoch_acc := locEpochInv_accept (pos := ⟨P.other, t', i'⟩) hepoch hid'
                (by dsimp only; rw [ht'_eq]; exact htcur')
              simp only [commitE, hcommit, liftH_run, modify_run, StateT.run_bind, StateT.run_pure,
                bind_assoc, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes2
              rcases Prod.mk.inj hes2 with ⟨_, rfl⟩
              have hupd_eq : Function.update (es.g.accept P st' ⟨P.other, t', i'⟩).st P st' =
                  (es.g.accept P st' ⟨P.other, t', i'⟩).st := by
                ext Q; by_cases hQ : Q = P <;> [ (subst hQ; simp [GameState.accept]); simp [Function.update_of_ne hQ] ]
              exact Or.inr ⟨⟨by simpa [hupd_eq] using hepoch_acc.1, hepoch_acc.2⟩,
                fun tWin hwe => by simpa [GameState.accept, GameState.delete] using hwin tWin hwe,
                lk, cur, by simpa [GameState.accept, GameState.delete] using hmem,
                hgt, by simpa [GameState.accept, GameState.delete] using htL, hle⟩
            · simp only [modify_run, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hes2
              rcases Prod.mk.inj hes2 with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hes2
              rcases Prod.mk.inj hes2 with ⟨_, rfl⟩; exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩
    · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr] at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases hg : es.abort || es.g.win || !(es.g.corrAllowed P)
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, stateT_lift_run, StateT.run_bind,
          bind_assoc, pure_bind, simulateQ_bind,
          mem_support_bind_iff] at hz
        rcases hz with ⟨⟨res, h'⟩, _, hz2⟩
        cases res with
        | none =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz2
          rcases Prod.mk.inj (Prod.mk.inj hz2).2 with ⟨rfl, rfl⟩; exact Or.inl rfl
        | some stOut =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz2
          rcases Prod.mk.inj (Prod.mk.inj hz2).2 with ⟨rfl, rfl⟩
          refine Or.inr ⟨hepoch, fun tWin hwe => ?_, lk, maxOpt es.g.tL _,
            by simp [GameState.afterCorr, GameState.leak, hmem], hgt, rfl,
            by rw [htL]; simp [maxOpt]; omega⟩
          rcases hwin tWin hwe with ⟨lk0, hm0, hg0, hl0⟩
          exact ⟨lk0, by simp [GameState.afterCorr, GameState.leak, hm0], hg0, hl0⟩
      · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rcases Prod.mk.inj (Prod.mk.inj hz).2 with ⟨rfl, rfl⟩
        exact Or.inr ⟨hepoch, hwin, lk, cur, hmem, hgt, htL, hle⟩

theorem evalDist_locForged_eq_zero_of_dead
    {Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec
      (LocalBucketAuthState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (hcommit : ∀ ctx P old new, hk.commit ctx P old new = pure (some new))
    (qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (es : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
    (winEp : Option ℕ)
    (hdead : LocDeadForged tL es winEp) :
    𝒟[simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
        let (_, es', we') ← (simulateQ (implLocalBucketAuthGen hk 1 qep maxSkip tL true) oa).run
          (es, winEp)
        return forgedParOut 3 tL par es' we'] {true} = 0 := by
  suffices hgen : ∀ (oa' : SchemeAdversary Γ T Sig SS RS M CCoins E)
      (es0 : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
      (we0 : Option ℕ), LocDeadForged tL es0 we0 →
      true ∉ support (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
        let (_, es', we') ← (simulateQ (implLocalBucketAuthGen hk 1 qep maxSkip tL true) oa').run
          (es0, we0)
        return forgedParOut 3 tL par es' we') by
    have hnot := hgen oa es winEp hdead
    rw [← bind_pure (simulateQ _ _)]
    exact _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ pure fun b hb => by
      cases b <;> [simp; exact False.elim (hnot hb)]
  intro oa'
  induction oa' using OracleComp.inductionOn with
  | pure _ =>
    intro es0 we0 hdead0 hsup
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      forgedParOut_eq_false_of_locDead 3 tL par es0 we0 hdead0] at hsup
    exact Bool.false_ne_true hsup.symm
  | query_bind qry cont ih =>
    intro es0 we0 hdead0 hsup
    rw [simulateQ_query_bind] at hsup
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift] at hsup
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, mem_support_bind_iff] at hsup
    rcases hsup with ⟨⟨out, es1, we1⟩, hstep, hu⟩
    exact ih out es1 we1
      (stepLocForged_preserves_locDead hk hcommit qep maxSkip tL qry es0 we0 hdead0 _ hstep) hu

/-! ### 3. Phase-1 Per-Session Invariant (`ForgedSessInv`) & Step Preservation -/

abbrev SessHSt (Pt : Type) (ℓ : ℕ) :=
  HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
    (Plain ℓ) LibsignalCiphertextWithSalt32

abbrev SessRState (Pt : Type) (ℓ : ℕ) :=
  _root_.CryptoGames.FSAEAD.State
    (RatchetSenderState (BitVec 256))
    (RatchetReceiverState (BitVec 256) (BitVec 256))
    (Header Pt × LibsignalMsgPublicPart)
    (Plain ℓ)
    (ℕ × LibsignalCiphertextWithSalt32)

structure ForgedSessInvAt {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32))
    (sM sL : SessHSt Pt ℓ) (stR : SessRState Pt ℓ) : Prop where
  syncRML : SyncRML (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) k stR sM sL
  ss_eq : ssLoc = stR.senderState
  rs_eq : rsLoc = stR.receiverState
  not_ended : sM.1.ended = false
  chal_nil : sM.1.challengesInTransit = []
  ok_inTransit : InTransitOk (fun hp : Header Pt × LibsignalMsgPublicPart => hp.2.shortB) sM.1
  pub_inTransit : ∀ r ∈ sM.1.inTransit, lPubOf protoSignalCodec r.ct.2 = some r.ad.2
  bk_count : bk.fsCount = sM.1.lastSentIdx
  bk_corr : bk.sCorr = false
  bk_trans : bk.fsTrans = sM.1.inTransit.map (fun r => (r.idx, r.ad.1, r.ct))

@[expose] def ForgedSessInv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32))
    (sM sL : SessHSt Pt ℓ) : Prop :=
  ∃ stR, ForgedSessInvAt C ℓ encT idOf k ssLoc rsLoc bk sM sL stR

theorem forgedSessInv_init {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (b : Bool) :
    ForgedSessInv C ℓ encT idOf k
      ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k)
      ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k)
      {} (hInit b (.seed k)) (hInit b (.seed k)) := by
  have hsync := syncRML_init (AD := Header Pt × LibsignalMsgPublicPart)
    (M := Plain ℓ) (C := LibsignalCiphertextWithSalt32)
    (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps k b
  exact ⟨_, hsync, by rw [lFS_initSender_eq]; rfl, by rw [lFS_initReceiver_eq]; rfl,
    rfl, rfl, inTransitOk_hInit _ b (.seed k), fun r hr => by simp [hInit] at hr, rfl, rfl, rfl⟩

private theorem ct_beq_iff : ∀ (c1 c2 : ℕ × LibsignalCiphertextWithSalt32), (c1 == c2) = true ↔ c1 = c2
  | ⟨n1, s1, b1⟩, ⟨n2, s2, b2⟩ => by
    change (n1 == n2 && (s1 == s2 && b1 == b2)) = true ↔ _
    simp [Bool.and_eq_true, beq_iff_eq]

private theorem hdr_beq_iff {Pt : Type} [DecidableEq Pt] :
    ∀ (h1 h2 : Header Pt), (h1 == h2) = true ↔ h1 = h2
  | ⟨t1, o1⟩, ⟨t2, o2⟩ => by
    cases o1 <;> cases o2 <;>
      (change (t1 == t2 && _) = true ↔ _;
       dsimp only [BEq.beq, Option.instBEq, Option.instBEq.beq];
       simp [Bool.and_eq_true])

private theorem ct_instBEq_eq (c1 c2 : ℕ × LibsignalCiphertextWithSalt32) :
    @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32
      instBEqOfDecidableEq instBEqOfDecidableEq) c1 c2 =
    @BEq.beq _ instBEqOfDecidableEq c1 c2 := by
  rcases c1 with ⟨n1, x1⟩; rcases c2 with ⟨n2, x2⟩; simp [BEq.beq, Prod.mk.injEq]

theorem forgedSessInv_matched_iff {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) :
    bk.fsTrans.find? (fun x => x.2 == (h, e)) =
      match lPubOf protoSignalCodec e.2 with
      | none => none
      | some p =>
        (sM.1.inTransit.find? (fun r =>
          @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
          @BEq.beq _ instBEqOfDecidableEq r.ct e)).map (fun r => (r.idx, r.ad.1, r.ct)) := by
  rcases hinv with ⟨_, hinv⟩; rw [hinv.bk_trans]; have hmem_pub := hinv.pub_inTransit
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    revert hmem_pub; induction sM.1.inTransit with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro hmem_pub
      have hr_pub : lPubOf protoSignalCodec r.ct.2 = some r.ad.2 := hmem_pub r List.mem_cons_self
      have hct_false : (r.ct == e) = false := by
        cases hbeq : (r.ct == e) <;> [rfl; (rw [(ct_beq_iff r.ct e).mp hbeq, hpub] at hr_pub; cases hr_pub)]
      have hfalse : ((r.ad.1, r.ct) == (h, e)) = false := by
        change (r.ad.1 == h && r.ct == e) = false; rw [hct_false, Bool.and_false]
      simp only [List.map_cons, List.find?_cons, hfalse]
      exact ih fun r' hr' => hmem_pub r' (List.mem_cons_of_mem _ hr')
  | some p =>
    revert hmem_pub; induction sM.1.inTransit with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro hmem_pub
      have hr_pub : lPubOf protoSignalCodec r.ct.2 = some r.ad.2 := hmem_pub r List.mem_cons_self
      have hpred : ((r.ad.1, r.ct) == (h, e)) =
          (@BEq.beq _ instBEqOfDecidableEq r.ad (h, p) && @BEq.beq _ instBEqOfDecidableEq r.ct e) := by
        change (r.ad.1 == h && r.ct == e) = (decide (r.ad = (h, p)) && decide (r.ct = e))
        by_cases hce : r.ct = e
        · have had_p : r.ad.2 = p := by
            rw [hce, hpub] at hr_pub; injection hr_pub with hp_eq; exact hp_eq.symm
          rcases hr_ad : r.ad with ⟨rh, rp⟩; rw [hr_ad] at had_p; dsimp only at had_p; subst had_p
          by_cases hhe : rh = h <;>
            [ (subst hhe; simp [hce]);
              simp [hhe, Bool.eq_false_iff.mpr (mt (hdr_beq_iff rh h).mp hhe), hce] ]
        · simp [hce, Bool.eq_false_iff.mpr (mt (ct_beq_iff r.ct e).mp hce)]
      simp only [List.map_cons, List.find?_cons, hpred]
      cases (@BEq.beq _ instBEqOfDecidableEq r.ad (h, p) && @BEq.beq _ instBEqOfDecidableEq r.ct e) <;>
        [exact ih fun r' hr' => hmem_pub r' (List.mem_cons_of_mem _ hr'); rfl]

theorem forgedSessInv_transmit {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) (hshort : pm.1.shortB = true) :
    let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ssLoc h pm
    let cnt' := bk.fsCount + 1
    let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
      { bk with fsCount := cnt', fsTrans := (cnt', h, o.2) :: bk.fsTrans }
    ∃ sM' sL',
      (transmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) (hp 0 0 false) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run sM = pure (some o.2, sM') ∧
      (transmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) (hp 0 0 true) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run sL = pure (some o.2, sL') ∧
      ForgedSessInv C ℓ encT idOf k o.1 rsLoc bk' sM' sL' := by
  let ideal := lIdeal C protoSignalCodec ℓ encT
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  intro o cnt' bk'; rcases hinv with ⟨stR, hinv⟩
  have ho_eq : o = (fromAEADPRG ae G maxForwardJumps).send stR.senderState (h, pm.1) pm.2 := by
    rw [← hinv.ss_eq]; exact lFS_send_eq C protoSignalCodec ℓ encT idOf maxForwardJumps ssLoc h pm
  have hended : stR.ended = false := by rw [hinv.syncRML.syncRM.stR_eq]; exact hinv.not_ended
  have hR_eval : (transmitImpl (fromAEADPRG ae G maxForwardJumps) ((h, pm.1), pm.2)).run stR =
      pure (some o.2, { stR with
        senderState := o.1, lastSentIdx := stR.lastSentIdx + 1,
        inTransit := ⟨stR.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ :: stR.inTransit }) := by
    simp [transmitImpl, CryptoGames.FSAEAD.transmit, hended, ← ho_eq]
  rcases transmit_syncRML ideal ae G maxForwardJumps hinv.syncRML ((h, pm.1), pm.2) with
    ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
  rw [hR_eval] at hR
  rcases Prod.mk.inj (pure_eq_iff.mp hR).symm with ⟨hu, hstR'⟩; subst hu
  have hok' := inTransitOk_of_transmitH ideal ae G hinv.syncRML.syncRM.wf_seed
    hinv.ok_inTransit hshort hM
  have hstR'_mk := hsyncL'.syncRM.stR_eq; have hstR_mk := hinv.syncRML.syncRM.stR_eq
  have hinT' : sM'.1.inTransit = ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ :: sM.1.inTransit := by
    rw [← (show stR'.inTransit = sM'.1.inTransit by rw [hstR'_mk]; rfl), hstR',
      (show stR.inTransit = sM.1.inTransit by rw [hstR_mk]; rfl),
      (show stR.lastSentIdx = sM.1.lastSentIdx by rw [hstR_mk]; rfl)]
  have hpub_o : lPubOf protoSignalCodec o.2.2 = some pm.1 := by
    rcases hsyncL'.syncRM.wf_state.inTransit_valid
      ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ (by rw [hinT']; simp) with ⟨_, _, hct⟩
    dsimp only at hct; rw [congrArg Prod.snd hct]
    exact lPubOf_enc_short_proof C protoSignalCodec hrt ℓ hℓ encT idOf _ _ pm.1 pm.2 hshort
  refine ⟨sM', sL', hM, hL, ⟨stR', hsyncL', by rw [hstR'], by rw [hinv.rs_eq, hstR'],
    hsyncL'.not_ended, ?_, hok', ?_, ?_, hinv.bk_corr,
    by dsimp only [bk', cnt']; rw [hinT', List.map_cons, hinv.bk_trans, hinv.bk_count]⟩⟩
  · rw [← (show stR'.challengesInTransit = sM'.1.challengesInTransit by rw [hstR'_mk]; rfl), hstR',
      (show stR.challengesInTransit = sM.1.challengesInTransit by rw [hstR_mk]; rfl), hinv.chal_nil]
  · intro r hr; rw [hinT', List.mem_cons] at hr
    rcases hr with rfl | hr <;> [exact hpub_o; exact hinv.pub_inTransit r hr]
  · dsimp only [bk', cnt']; rw [hinv.bk_count,
      ← (show stR'.lastSentIdx = sM'.1.lastSentIdx by rw [hstR'_mk]; rfl), hstR',
      (show stR.lastSentIdx = sM.1.lastSentIdx by rw [hstR_mk]; rfl)]

theorem forgedSessInv_deliver {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {mEntry : ℕ × Header Pt × (ℕ × LibsignalCiphertextWithSalt32)}
    (hmatch : bk.fsTrans.find? (fun x => x.2 == (h, e)) = some mEntry) :
    ∃ p : LibsignalMsgPublicPart, lPubOf protoSignalCodec e.2 = some p ∧
      match (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e with
      | none =>
        ∃ sM' sL',
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sM = pure (some .rejected, sM') ∧
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sL = pure (some .rejected, sL') ∧
          ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM' sL'
      | some (rsLoc', idxOut, pmOut) =>
        mEntry.1 = idxOut ∧ ∃ sM' sL',
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sM = pure (some (.accepted idxOut (some pmOut.2)), sM') ∧
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sL = pure (some (.accepted idxOut (some pmOut.2)), sL') ∧
          pmOut.1 = p ∧
          ForgedSessInv C ℓ encT idOf k ssLoc rsLoc'
            { bk with fsTrans := bk.fsTrans.filter (·.1 != mEntry.1) } sM' sL' := by
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  have hae := lAeadR_correctOn_short_proof C hD protoSignalCodec hrt ℓ hℓ encT idOf
  have hiff := forgedSessInv_matched_iff C ℓ encT idOf hinv h e
  rcases hinv with ⟨stR, hinv⟩; rw [hmatch] at hiff
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none => rw [hpub] at hiff; cases hiff
  | some p =>
    refine ⟨p, rfl, ?_⟩; rw [hpub] at hiff; dsimp only at hiff
    cases hfind : sM.1.inTransit.find? (fun r => @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
        @BEq.beq _ instBEqOfDecidableEq r.ct e) with
    | none => rw [hfind] at hiff; cases hiff
    | some r =>
      rw [hfind] at hiff; dsimp only [Option.map] at hiff; injection hiff with hmEntry
      have hr_mem := List.mem_of_find?_eq_some hfind; have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true] at hr_pred; have hr_ct : r.ct = e := of_decide_eq_true hr_pred.2
      rcases hinv.syncRML.syncRM.wf_state.inTransit_valid r hr_mem with ⟨_, _, hct_valid⟩
      have hr_idx : r.idx = e.1 := (congrArg Prod.fst (hr_ct.symm.trans hct_valid)).symm
      have hfind_eq : (sM.1.inTransit.find? fun x =>
          @BEq.beq _ instBEqOfDecidableEq x.ad (h, p) &&
          @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32
            instBEqOfDecidableEq instBEqOfDecidableEq) x.ct (e.1, e.2)) = some r := by
        simp only [ct_instBEq_eq]; exact hfind
      have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
          ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
            (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
      have hstR_mk := hinv.syncRML.syncRM.stR_eq
      rcases deliver_syncRML_on ae G maxForwardJumps hae hinv.syncRML hinv.ok_inTransit ((h, p), e)
        with ⟨u, stR', sM', sL', hR, hM, hL, hsyncL', hok'⟩
      have hstR'_mk := hsyncL'.syncRM.stR_eq
      have hR_unf := hR; rw [hstR_mk] at hR_unf
      simp only [deliverImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run,
        CryptoGames.FSAEAD.deliver, mkRState, hinv.not_ended, Bool.false_eq_true, ↓reduceIte,
        hfind, hinv.chal_nil, List.contains_nil] at hR_unf
      cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
          (mkRState G k sM.1).receiverState (h, p) e with
      | none =>
        have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
            none := by rw [hstR_mk]; exact hrec
        rw [hrecv_lFS, hrec', Option.map_none]
        have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
        rw [hrec_unf] at hR_unf; dsimp only at hR_unf
        rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
        have hinT' : sM'.1.inTransit = sM.1.inTransit := by
          rw [← (show stR'.inTransit = sM'.1.inTransit by rw [hstR'_mk]; rfl), hstR']
        refine ⟨sM', sL', hM, hL, ⟨stR', hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
          by rw [hinv.rs_eq, hstR', hstR_mk]; rfl, hsyncL'.not_ended,
          by rw [← (show stR'.challengesInTransit = sM'.1.challengesInTransit by rw [hstR'_mk]; rfl), hstR'],
          hok', by rw [hinT']; exact hinv.pub_inTransit,
          by rw [hinv.bk_count, ← (show stR'.lastSentIdx = sM'.1.lastSentIdx by rw [hstR'_mk]; rfl), hstR'],
          hinv.bk_corr, by rw [hinv.bk_trans, hinT']⟩⟩
      | some rim =>
        rcases rim with ⟨rs', idxOut, msgOut⟩
        have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
            some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
        rw [hrecv_lFS, hrec', Option.map_some]
        have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
        rw [hrec_unf] at hR_unf; dsimp only at hR_unf
        rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
        dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
        have hM_check := hM
        rw [deliverH_run_of_wfSeed ae G maxForwardJumps (hp 0 0 false) (DG G)
          hinv.syncRML.syncRM.wf_seed hinv.syncRML.syncRM.wf_state.inTransit_valid
          hinv.syncRML.syncRM.wf_state.sent_le_keys (h, p) e.1 e.2] at hM_check
        simp only [hinv.not_ended, Bool.false_eq_true, ↓reduceIte, hfind_eq, hinv.chal_nil,
          List.contains_nil] at hM_check
        have hidx : e.1 = idxOut := by
          split_ifs at hM_check <;>
            (obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc; try rfl)
        have hmEntry1 : mEntry.1 = idxOut := by rw [hmEntry]; dsimp only; rw [hr_idx, hidx]
        have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != r.idx) := by
          have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
          rw [← h1, hstR']
        refine ⟨hmEntry1, sM', sL', hM, hL, rfl,
          ⟨stR', hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hstR'], hsyncL'.not_ended,
          ?_, hok', ?_, ?_, hinv.bk_corr,
          by dsimp only; rw [hmEntry1, ← hidx, ← hr_idx, hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
        · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
          rw [← h1, hstR']; simp
        · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
        · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
          dsimp only; rw [hinv.bk_count, ← h1, hstR']

theorem forgedSessInv_inject {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (hmatch_none : bk.fsTrans.find? (fun x => x.2 == (h, e)) = none)
    (p : LibsignalMsgPublicPart) (hpub : lPubOf protoSignalCodec e.2 = some p) :
    (∃ msg sL', bk.sCorr = false ∧ bk.fsCount < e.1 ∧
      (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run sL = pure (some (.accepted e.1 (some msg)), sL')) ∨
    match (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e with
    | none => ∃ sM' sL',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some .rejected, sM') ∧
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sL = pure (some .rejected, sL') ∧
        ForgedSessInv C ℓ encT idOf k ssLoc rsLoc bk sM' sL'
    | some (rsLoc', idxOut, pmOut) => ∃ sM' sL',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some (.accepted idxOut (some pmOut.2)), sM') ∧
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sL = pure (some (.accepted idxOut (some pmOut.2)), sL') ∧
        idxOut ≤ bk.fsCount ∧ pmOut.1 = p ∧
        ForgedSessInv C ℓ encT idOf k ssLoc rsLoc'
          { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) } sM' sL' := by
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  have hiff := forgedSessInv_matched_iff C ℓ encT idOf hinv h e
  rcases hinv with ⟨stR, hinv⟩; have hsyncL := hinv.syncRML
  rw [hmatch_none, hpub] at hiff; dsimp only at hiff
  have hfind_none : sM.1.inTransit.find? (fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ instBEqOfDecidableEq r.ct e) = none := by
    cases hf : sM.1.inTransit.find? _ with | none => rfl | some _ => rw [hf] at hiff; cases hiff
  have hany_impl : (sM.1.inTransit.any fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) && @BEq.beq _ instBEqOfDecidableEq r.ct e) = false :=
    List.any_eq_false.mpr (List.find?_eq_none.mp hfind_none)
  have hany_false : (sM.1.inTransit.any fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32 instBEqOfDecidableEq instBEqOfDecidableEq)
        r.ct (e.1, e.2)) = false := by simp only [ct_instBEq_eq]; exact hany_impl
  have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
      ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
        (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
  have hstR_mk := hsyncL.syncRM.stR_eq
  by_cases hlook_case : e.1 ∉ sM.1.skipped ∧
      ¬ (e.1 ≤ sM.1.receiverIdx ∨ maxForwardJumps < e.1 - sM.1.receiverIdx - 1) ∧
      sM.1.lastSentIdx < e.1
  · rcases hlook_case with ⟨hcont, hout, hlt⟩
    cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 with
    | some msg =>
      left
      rcases injectL_lookahead_some_accepted ae G maxForwardJumps hsyncL (h, p) e.1 e.2 msg
        hinv.not_ended hany_false hcont hout hlt hdec with ⟨sL', hL⟩
      exact ⟨msg, sL', hinv.bk_corr, by rw [hinv.bk_count]; exact hlt, hL⟩
    | none =>
      right
      rcases CryptoGames.FSAEAD.Thm5.Ends.inject_syncRML_of_lookahead_none ae G maxForwardJumps
        hsyncL (h, p) e.1 e.2 hinv.not_ended hany_false hcont hout hlt hdec with
        ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
      have hok' := inTransitOk_of_injectH_lookahead_none ae G maxForwardJumps (h, p) e.1 e.2
        hinv.ok_inTransit hinv.not_ended hany_false hcont hout hlt hsyncL.uncorr hM
      have hstR'_mk := hsyncL'.syncRM.stR_eq
      have hrec_none : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e = none := by
        rw [hstR_mk]
        erw [CryptoGames.FSAEAD.Thm5.Ends.receive_real_of_in_window ae G maxForwardJumps k
          sM.1.receiverIdx sM.1.skipped (h, p) e.1 e.2 hcont hout]; simp [hdec]
      rw [hrecv_lFS, hrec_none, Option.map_none]
      have hR_unf := hR; rw [hstR_mk] at hR_unf
      simp only [injectImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run, CryptoGames.FSAEAD.inject,
        mkRState, hinv.not_ended, hany_impl, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hR_unf
      have hrec_mk : (fromAEADPRG ae G maxForwardJumps).receive
          (mkRState G k sM.1).receiverState (h, p) e = none := by rw [← hstR_mk]; exact hrec_none
      dsimp only [ae, G, mkRState] at hrec_mk hR_unf; rw [hrec_mk] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit := by
        rw [← (show stR'.inTransit = sM'.1.inTransit by rw [hstR'_mk]; rfl), hstR']
      refine ⟨sM', sL', hM, hL, ⟨stR', hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
        by rw [hinv.rs_eq, hstR', hstR_mk]; rfl, hsyncL'.not_ended,
        by rw [← (show stR'.challengesInTransit = sM'.1.challengesInTransit by rw [hstR'_mk]; rfl), hstR']; exact hinv.chal_nil,
        hok', by rw [hinT']; exact hinv.pub_inTransit,
        by rw [hinv.bk_count, ← (show stR'.lastSentIdx = sM'.1.lastSentIdx by rw [hstR'_mk]; rfl), hstR'],
        hinv.bk_corr, by rw [hinv.bk_trans, hinT']⟩⟩
  · right
    rcases inject_syncRML_of_not_lookahead ae G maxForwardJumps hsyncL ((h, p), e)
      (by intro _ _ hc ho _; by_contra hgt; exact hlook_case ⟨hc, ho, Nat.lt_of_not_ge hgt⟩)
      with ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
    have hok' := inTransitOk_of_injectH_not_lookahead ae G maxForwardJumps hsyncL.syncRM
      hinv.ok_inTransit
      (by intro _ _ hc ho _; by_contra hgt; exact hlook_case ⟨hc, ho, Nat.lt_of_not_ge hgt⟩) hM
    have hstR'_mk := hsyncL'.syncRM.stR_eq; have hR_unf := hR; rw [hstR_mk] at hR_unf
    simp only [injectImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run, CryptoGames.FSAEAD.inject,
      mkRState, hinv.not_ended, hany_impl, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hR_unf
    cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
        (mkRState G k sM.1).receiverState (h, p) e with
    | none =>
      have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e = none := by
        rw [hstR_mk]; exact hrec
      rw [hrecv_lFS, hrec', Option.map_none]
      have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
      rw [hrec_unf] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit := by
        rw [← (show stR'.inTransit = sM'.1.inTransit by rw [hstR'_mk]; rfl), hstR']
      refine ⟨sM', sL', hM, hL, ⟨stR', hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
        by rw [hinv.rs_eq, hstR', hstR_mk]; rfl, hsyncL'.not_ended,
        by rw [← (show stR'.challengesInTransit = sM'.1.challengesInTransit by rw [hstR'_mk]; rfl), hstR']; exact hinv.chal_nil,
        hok', by rw [hinT']; exact hinv.pub_inTransit,
        by rw [hinv.bk_count, ← (show stR'.lastSentIdx = sM'.1.lastSentIdx by rw [hstR'_mk]; rfl), hstR'],
        hinv.bk_corr, by rw [hinv.bk_trans, hinT']⟩⟩
    | some rim =>
      rcases rim with ⟨rs', idxOut, msgOut⟩
      have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
          some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
      rw [hrecv_lFS, hrec', Option.map_some]
      have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
      rw [hrec_unf] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != idxOut) := by
        have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']
      have hidx_le : idxOut ≤ bk.fsCount := by
        rw [hinv.bk_count]; have hM_check := hM
        have hsk_comp : ∀ j ∈ sM.1.skipped, sM.1.lastSentIdx < j → sM.1.isCompromised j = true :=
          fun j hj hlt => isCompromised_of_wfState_lt ae G hsyncL.syncRM.wf_state
            (le_of_lt (hsyncL.syncRM.wf_state.skipped_bounds j hj).2) hlt
        rw [injectH_run_of_wfSeed_not_lookahead ae G maxForwardJumps false hsyncL.syncRM.wf_seed
          hsyncL.syncRM.wf_state.skipped_bounds hsyncL.syncRM.wf_state.rcv_le_keys hsk_comp
          (h, p) e.1 e.2 (by intro _ _ hc ho hlt; exact False.elim (hlook_case ⟨hc, ho, hlt⟩))]
          at hM_check
        simp only [hinv.not_ended, hany_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hM_check
        by_cases hcont : e.1 ∈ sM.1.skipped
        · simp only [hcont, ↓reduceIte] at hM_check
          cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 <;> simp only [hdec] at hM_check
          · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
          · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
            injection hacc with hacc; injection hacc with hi _; subst hi
            have hb := (hsyncL.syncRM.wf_state.skipped_bounds e.1 hcont).2
            have hr_le := hsyncL.syncRM.wf_state.rcv_le_sent_of_uncorr hsyncL.uncorr; omega
        · simp only [hcont, ↓reduceIte] at hM_check
          by_cases hout : e.1 ≤ sM.1.receiverIdx ∨ maxForwardJumps < e.1 - sM.1.receiverIdx - 1
          · simp only [hout, ↓reduceIte] at hM_check
            obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
          · simp only [hout, ↓reduceIte] at hM_check
            cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 <;> simp only [hdec] at hM_check
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _; subst hi
              by_contra hgt; exact hlook_case ⟨hcont, hout, Nat.lt_of_not_ge hgt⟩
      refine ⟨sM', sL', hM, hL, hidx_le, rfl,
        ⟨stR', hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hstR'], hsyncL'.not_ended,
        ?_, hok', ?_, ?_, hinv.bk_corr,
        by dsimp only; rw [hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
      · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR', hinv.chal_nil]; rfl
      · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
      · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
        dsimp only; rw [hinv.bk_count, ← h1, hstR']

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedAux
