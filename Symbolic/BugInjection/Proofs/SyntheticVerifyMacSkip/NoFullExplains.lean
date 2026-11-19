/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoFullMatch
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoFullExplains

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (flatEvents)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (cliCoins0)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend rngMsg39 acceptMsg40)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
  (AllBobDone bobDoneBaseKeys_of_allBobDone mem_bobDoneBaseKeys_of_mem_sessionBaseKeys)
open Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem not_matchedPrefix_vms_tail_gen {interp0 : ExternInterpretation}
    {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {b0 b1 rest : List MachineEvent}
    {bun pt wire tag8 : HwBytes} {rs0 : List MachineEvent} {tail1 : List MachineEvent}
    (hb0 : b0 = .recv bun :: rs0) (hrs0 : ∀ e ∈ rs0, eventKind e = .rng)
    (hb1 : b1 = .pt pt :: tail1) (htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send)
    (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hq_some : (parsePreKeyWire wire).isSome = true)
    (hmac_tag : (parsePreKeyWire wire).map (fun p => p.message.drop (p.message.length - 8)) =
      some tag8)
    (hmac_len : ∀ mk peerIk myIk w,
      (gamma interp0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk w)).length = 8)
    (hmac_ne : ∀ mk peerIk myIk w,
      gamma interp0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk w) ≠ tag8)
    (hdrop8 : ∀ {raw : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg},
      DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg →
      (gamma interp0 S g msg.mac).length = 8 →
      (gamma interp0 S g raw).drop ((gamma interp0 S g raw).length - 8) = gamma interp0 S g msg.mac)
    (hrest_ne : ∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak)
    (hacc : ∃ e ∈ rest, eventKind e = .accept)
    (hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv wire :: rest), eventKind e ≠ .leak)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix interp0 r S g ms
      ((b0 ++ b1) ++ (.recv wire :: rest))) : False := by
  let blk : List MachineEvent := .recv wire :: rest
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp [blk] at he; subst he; exact Or.inl rfl
  obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ :=
    matchedPrefix6_split hmp hhead (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp)
  have hbd₁ : AllBobDone (fun _ => False) (runTraceMoves r ms₁) := by
    rw [hb1] at hmp₁
    refine Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_send_tail
      htail1 (fun ms₀ hmp₀ => ?_) hmp₁
    rw [hb0] at hmp₀
    exact Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_ini_rs
      hrs0 (fun _ hnil =>
        Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_nil hnil)
      (by simpa using hmp₀)
  have hB : XplBlock6 interp0 r S g ms₁ δ (b0 ++ b1) blk := ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨_, _, hm⟩, _⟩ :=
    xpl6_oneMove hB hhead (by simp [blk]) hrest_ne
  let ms_pre := ms₁ ++ pre
  have hms_eq : ms = ms_pre ++ (m :: post) := by simp [hms, ms_pre, List.append_assoc]
  have htr_eq : (runMoves pre (runTraceMoves r ms₁)).1 = runTraceMoves r ms_pre :=
    (CompPrefixInvStruct.runTrace_append r ms₁ pre).symm
  have hbd_pre : AllBobDone (fun _ => False)
      (runTraceMoves r ms_pre) :=
    htr_eq ▸ Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_runMoves_of_movesFrom
      hpre_inv hbd₁
  rw [htr_eq] at hm
  have hnoleak_all : ∀ v ∈ runVis r ms, v.kind ≠ .leak :=
    CompSetupSecrecy.crit_noleak_of_forall2 hnoleak hmp.2.2
  have hvis_split : runVis r ms = runVis r ms_pre ++ (m.vis (runTraceMoves r ms_pre) ++
        (runMoves post (m.next (runTraceMoves r ms_pre))).2) := by
    rw [hms_eq,
      Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.runVis_append,
      runMoves_cons_snd]
  have hnoleak_m : ∀ v ∈ m.vis (runTraceMoves r ms_pre), v.kind ≠ .leak := fun v hv =>
    hnoleak_all v (by rw [hvis_split]; exact List.mem_append_right _ (List.mem_append_left _ hv))
  let tr := runTraceMoves r ms_pre
  obtain ⟨v₀, vs, hv₀, hrest_m, hvis⟩ := xpl_forall₂_cons_left hm
  obtain ⟨e_acc, he_acc, he_kind⟩ := hacc
  obtain ⟨v_acc, hv_acc_vs, hev_acc⟩ := xpl_forall₂_mem_left hrest_m e_acc he_acc
  have hv_acc : v_acc ∈ m.vis tr := by rw [hvis]; exact List.mem_cons_of_mem _ hv_acc_vs
  have hv_acc_kind : v_acc.kind = .accept := (xpl_kind_of_matches hev_acc).trans he_kind
  have hexp : exposures tr (m.next tr) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    exact hnoleak_m v (by rw [xpl_vis_eq]; exact List.mem_append_right _ hv) (xpl_exposures_kind hv)
  have hown_acc : v_acc ∈ xpl_ownVis m tr := by
    have h := hv_acc; rw [xpl_vis_eq, hexp, List.append_nil] at h; exact h
  have hown_vis : xpl_ownVis m tr = v₀ :: vs := by
    rw [← List.append_nil (xpl_ownVis m tr), ← hexp, ← xpl_vis_eq, hvis]
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hq_some
  cases m with
  | bobStart b a kh regA mh pqIdx spqrMsgIdx shown =>
    obtain ⟨w⟩ := CompSetupSecrecy.bobStart_accept_ok hv_acc hv_acc_kind
    have hpm := w.preKeyRecvMatches_of_vis hvis (hvis ▸ hnoleak_m) hv₀
    obtain ⟨p, hp, _, _, hmsg_eq, _⟩ := hpm
    rw [hq] at hp; injection hp with hp_eq; subst hp_eq
    have hdrop : q.message.drop (q.message.length - 8) = tag8 := by
      rw [hq, Option.map_some, Option.some.injEq] at hmac_tag; exact hmac_tag
    have hlen8 : (gamma interp0 S g w.msg.mac).length = 8 := by
      rw [w.hmac]; exact hmac_len _ _ _ _
    have hdrop_raw := hdrop8 w.hparse hlen8
    rw [← hmsg_eq, hdrop, w.hmac] at hdrop_raw
    exact hmac_ne _ _ _ _ hdrop_raw.symm
  | decrypt me si mi pq sp wrapped =>
    let tr' := (Move.decrypt me si mi pq sp wrapped).next tr
    dsimp only [xpl_ownVis] at hown_vis
    have hvk₀ : v₀.kind = .recv := hv₀.1.symm
    have hv₀_in : v₀ ∈ decVis tr tr' si mi wrapped := by rw [hown_vis]; exact List.mem_cons_self ..
    rcases hmsg : tr.getMessageSentAt mi with _ | raw
    · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
        List.mem_append, List.mem_map] at hv₀_in
      rcases hv₀_in with ⟨_, _, rfl⟩ | hacc_mem
      · cases hvk₀
      · rcases hp : receivedPlaintext tr tr' with _ | m_pt <;> simp [hp] at hacc_mem
        subst hacc_mem; cases hvk₀
    · unfold decVis at hown_vis; rw [hmsg] at hown_vis
      simp only [Option.map_some, Option.toList_some, List.cons_append, List.cons.injEq] at hown_vis
      obtain ⟨rfl, _⟩ := hown_vis
      cases wrapped with
      | false =>
        obtain ⟨_, _, hw_eq⟩ := hv₀.2; change wire = _ at hw_eq
        rw [hw_eq] at hhead_ne; exact absurd rfl hhead_ne
      | true =>
        obtain ⟨_, _, _, _, ⟨ek, hek_mem, _⟩, _⟩ := hv₀.2
        exact bobDoneBaseKeys_of_allBobDone hbd_pre ek
          (mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek_mem)
  | decryptSkipped me si mi k pq sp wrapped =>
    let tr' := (Move.decryptSkipped me si mi k pq sp wrapped).next tr
    dsimp only [xpl_ownVis] at hown_vis
    have hvk₀ : v₀.kind = .recv := hv₀.1.symm
    have hv₀_in : v₀ ∈ decVis tr tr' si mi wrapped := by rw [hown_vis]; exact List.mem_cons_self ..
    rcases hmsg : tr.getMessageSentAt mi with _ | raw
    · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
        List.mem_append, List.mem_map] at hv₀_in
      rcases hv₀_in with ⟨_, _, rfl⟩ | hacc_mem
      · cases hvk₀
      · rcases hp : receivedPlaintext tr tr' with _ | m_pt <;> simp [hp] at hacc_mem
        subst hacc_mem; cases hvk₀
    · unfold decVis at hown_vis; rw [hmsg] at hown_vis
      simp only [Option.map_some, Option.toList_some, List.cons_append, List.cons.injEq] at hown_vis
      obtain ⟨rfl, _⟩ := hown_vis
      cases wrapped with
      | false =>
        obtain ⟨_, _, hw_eq⟩ := hv₀.2; change wire = _ at hw_eq
        rw [hw_eq] at hhead_ne; exact absurd rfl hhead_ne
      | true =>
        obtain ⟨_, _, _, _, ⟨ek, hek_mem, _⟩, _⟩ := hv₀.2
        exact bobDoneBaseKeys_of_allBobDone hbd_pre ek
          (mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek_mem)
  | aliceStart =>
    rcases xpl_aliceVis_kind (List.mem_of_mem_take hown_acc) with h | h <;> (rw [hv_acc_kind] at h; cases h)
  | reject =>
    simp only [xpl_ownVis, List.mem_cons, List.mem_map] at hown_acc
    rcases hown_acc with rfl | ⟨_, _, rfl⟩ <;> cases hv_acc_kind
  | encrypt =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptAbort =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptFail =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | _ => simp [xpl_ownVis] at hown_acc

theorem coinSplit_rng_only :
    ∀ {c : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c] xs → ∀ e ∈ xs, eventKind e = .rng := by
  intro c xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | nil =>
      intro e he
      rw [List.append_nil, List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      rfl

theorem coinSplit_rng_send :
    ∀ {c w : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c, .send w] xs →
      ∀ e ∈ xs, eventKind e = .rng ∨ eventKind e = .send := by
  intro c w xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | keep _ hnil =>
      cases hnil with
      | nil =>
        intro e he
        rcases List.mem_append.mp he with hr | hs
        · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr; exact Or.inl rfl
        · simp only [List.mem_singleton] at hs; subst hs; exact Or.inr rfl

theorem coinSplit_rng_accept :
    ∀ {c acc : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c, .accept acc] xs →
      (∀ e ∈ xs, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) ∧
      (∃ e ∈ xs, eventKind e = .accept) := by
  intro c acc xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | keep _ hnil =>
      cases hnil with
      | nil =>
        refine ⟨fun e he => ?_, .accept acc, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
        rcases List.mem_append.mp he with hr | ha
        · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr
          exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
        · simp only [List.mem_singleton] at ha; subst ha
          exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩

theorem coinSplit_keep_inv {e : MachineEvent} {σ τ : List MachineEvent}
    (hne : ∀ b, e ≠ .rng b) (h : CoinSplit (e :: σ) τ) :
    ∃ τ', τ = e :: τ' ∧ CoinSplit σ τ' := by
  cases h with
  | keep _ h' => exact ⟨_, rfl, h'⟩
  | split _ _ _ => exact absurd rfl (hne _)

theorem coinSplit_rng_inv {c : HwBytes} {σ τ : List MachineEvent}
    (h : CoinSplit (.rng c :: σ) τ) :
    ∃ (pieces : List HwBytes) (τ' : List MachineEvent),
      τ = pieces.map MachineEvent.rng ++ τ' ∧ CoinSplit σ τ' := by
  cases h with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ h' => exact ⟨_, _, rfl, h'⟩

theorem no_coinSplit_matchedPrefix_vms_gen {interp0 : ExternInterpretation}
    {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move}
    {bun c0 pt c1 sw wire c2 acc : HwBytes} {τhw : List MachineEvent}
    (htail : ∀ {b0 b1 rest rs0 tail1 : List MachineEvent},
      b0 = .recv bun :: rs0 →
      (∀ e ∈ rs0, eventKind e = .rng) →
      b1 = .pt pt :: tail1 →
      (∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send) →
      (∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) →
      (∃ e ∈ rest, eventKind e = .accept) →
      (∀ e ∈ (b0 ++ b1) ++ (.recv wire :: rest), eventKind e ≠ .leak) →
      Symbolic.Swarm.CREF.MatchedPrefix interp0 r S g ms
        ((b0 ++ b1) ++ (.recv wire :: rest)) → False)
    (hcs : CoinSplit
      [.recv bun, .rng c0,
        .pt pt, .rng c1, .send sw,
        .recv wire, .rng c2, .accept acc] τhw) :
    ¬ DY.Libsignal.Composed.Refinement.MatchedPrefix interp0 r S who₀ g ms τhw := by
  intro hmp
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs
  obtain ⟨pieces0, τ2, rfl, hcs2⟩ := coinSplit_rng_inv hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs2
  obtain ⟨pieces1, τ4, rfl, hcs4⟩ := coinSplit_rng_inv hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs4
  obtain ⟨rest, rfl, hcs6⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs5
  let rs0 : List MachineEvent := pieces0.map .rng
  let b0 : List MachineEvent := .recv bun :: rs0
  let tail1 : List MachineEvent := pieces1.map .rng ++ [.send sw]
  let b1 : List MachineEvent := .pt pt :: tail1
  obtain ⟨hrest_ne, hacc⟩ := coinSplit_rng_accept hcs6
  have hrs0 : ∀ e ∈ rs0, eventKind e = .rng := by
    intro e he; rw [List.mem_map] at he; obtain ⟨_, _, rfl⟩ := he; rfl
  have htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send := by
    intro e he
    rcases List.mem_append.mp he with hr | hs
    · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr; exact Or.inl rfl
    · simp only [List.mem_singleton] at hs; subst hs; exact Or.inr rfl
  have hτ_eq :
      (MachineEvent.recv bun :: (pieces0.map .rng ++
        (.pt pt :: (pieces1.map .rng ++
          (.send sw :: (.recv wire :: rest)))))) =
      (b0 ++ b1) ++ (.recv wire :: rest) := by
    simp [b0, b1, rs0, tail1, List.append_assoc]
  have hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv wire :: rest), eventKind e ≠ .leak := by
    intro e he
    rcases List.mem_append.mp he with hb01 | hr2
    · rcases List.mem_append.mp hb01 with hb0' | hb1'
      · rcases List.mem_cons.mp hb0' with rfl | hrs
        · exact fun h => nomatch h
        · rw [hrs0 e hrs]; decide
      · rcases List.mem_cons.mp hb1' with rfl | ht1
        · exact fun h => nomatch h
        · rcases htail1 e ht1 with h | h <;> rw [h] <;> decide
    · rcases List.mem_cons.mp hr2 with rfl | hrest
      · exact fun h => nomatch h
      · exact (hrest_ne e hrest).2.2
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix interp0 r S g ms
      ((b0 ++ b1) ++ (.recv wire :: rest)) := by
    rw [← hτ_eq]
    exact ⟨hmp.1, hmp.2.1, hmp.2.2.2.2.2⟩
  exact htail rfl hrs0 rfl htail1 hrest_ne hacc hnoleak hmp_cref

theorem not_matchedPrefix_vms_tail {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {b0 b1 rest : List MachineEvent}
    {bun pt sw : HwBytes} {rs0 : List MachineEvent} {tail1 : List MachineEvent}
    (hb0 : b0 = .recv bun :: rs0) (hrs0 : ∀ e ∈ rs0, eventKind e = .rng)
    (hb1 : b1 = .pt pt :: tail1) (htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send)
    (hrest_ne : ∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak)
    (hacc : ∃ e ∈ rest, eventKind e = .accept)
    (hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv msg38_vms :: rest), eventKind e ≠ .leak)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      ((b0 ++ b1) ++ (.recv msg38_vms :: rest))) : False :=
  let _ := sw
  let ⟨hhead_ne, hq_some, hmac_o, _⟩ := msg38_vms_props
  not_matchedPrefix_vms_tail_gen hb0 hrs0 hb1 htail1 hhead_ne hq_some hmac_o
    (gamma_computeMac_length S g) (gamma_computeMac_ne_ones8 S g)
    (parseTrSignalMsg_gamma_drop8 (i := compI0) (S := S) (g := g))
    hrest_ne hacc hnoleak hmp

theorem no_coinSplit_matchedPrefix_vms
    {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move}
    {τhw : List MachineEvent}
    (hcs : CoinSplit (flatEvents cliEventsVMS) τhw) :
    ¬ DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who₀ g ms τhw := by
  change CoinSplit
    [.recv CompRX0SS38.bunBytes, .rng cliCoins0,
      .pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes,
      .recv msg38_vms, .rng rngMsg39, .accept acceptMsg40] τhw at hcs
  exact no_coinSplit_matchedPrefix_vms_gen
    (fun hb0 hrs0 hb1 htail1 hrest_ne hacc hnoleak hmp =>
      not_matchedPrefix_vms_tail (sw := CompRPlantWire.sentWireBytes)
        hb0 hrs0 hb1 htail1 hrest_ne hacc hnoleak hmp)
    hcs

end Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.NoFullExplains
