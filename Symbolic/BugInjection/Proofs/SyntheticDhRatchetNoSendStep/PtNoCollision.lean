/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtCoins
import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

/-!
# Plaintext Collision Absence on All `.send` Events of `DhRatchetNoSendStepCli`

Proves `not_nextEventCollides_send`: no `.send` run event in `DhRatchetNoSendStepCli.trace`
(lengths 19 and 21) can satisfy `NextEventCollides` after an explained prefix under `cliCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.PtNoCollision

open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement (sha256CompressFunction)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains
   BytesMatchEntry MemoCollisionOn
   ptEntryAt plaintextTerms prefixTerms randTerm runTrace setupTrace setupRandomsAt
   gamma gamma' gDhPk gDh gKdf0 gSym0 gKemEncap gKemSS
   concretizeDhPk concretizeDh concretizeKdf concretizeSym
   concretizeKemEncap concretizeKemSS
   node opaqueNode assumedInjective)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides PrefixExplainingGhosts)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compLookupPub_length compLookupDh_length compKyberEncaps_length)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_dhPk ms_pack_dh ms_pack_kdf ms_pack_sym ms_pack_trunc ms_pack_kemEncap ms_pack_kemSS)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (length_hmacWith_32)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
  (runSteps_le randAt_of_le_of_lt randAt_setupTrace_mem_setupRandomsAt prefixTerms_termRandAt)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtCoins
  (GoodSendLen matchesEvents_coinDrawn_infix)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhRatchetHooks0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
  (dhRatchetI0_publicKey dhRatchetI0_agreement dhRatchetI0_aesEncrypt dhRatchetI0_kyberEncaps
   dhRatchetAesPerm_length)

private def hasInfix (needle : HwBytes) : HwBytes → Bool
  | [] => needle.isEmpty
  | x :: xs => needle.isPrefixOf (x :: xs) || hasInfix needle xs

private theorem isPrefixOf_of_isPrefix :
    ∀ {a b : HwBytes}, a <+: b → a.isPrefixOf b = true
  | [], _, _ => rfl
  | x :: xs, _, ⟨t, rfl⟩ => by
    simp only [List.cons_append, List.isPrefixOf, beq_self_eq_true, Bool.true_and]
    exact isPrefixOf_of_isPrefix ⟨t, rfl⟩

private theorem hasInfix_append_left {a : HwBytes} :
    ∀ (s : HwBytes) {b : HwBytes}, hasInfix a b = true → hasInfix a (s ++ b) = true
  | [], _, h => h
  | x :: xs, _, h => by
    simp only [List.cons_append, hasInfix, Bool.or_eq_true]
    exact Or.inr (hasInfix_append_left xs h)

private theorem hasInfix_of_isPrefix {a b : HwBytes} (h : a <+: b) : hasInfix a b = true := by
  cases b with
  | nil =>
    obtain ⟨_, ht⟩ := h
    cases List.append_eq_nil_iff.mp ht |>.1
    rfl
  | cons x xs =>
    simp only [hasInfix, Bool.or_eq_true]
    exact Or.inl (isPrefixOf_of_isPrefix h)

private theorem hasInfix_of_isInfix {a c : HwBytes} (h : a <:+: c) : hasInfix a c = true := by
  obtain ⟨s, t, rfl⟩ := h
  rw [List.append_assoc]
  exact hasInfix_append_left s (hasInfix_of_isPrefix ⟨t, rfl⟩)

private def dhRatchetSendInputsValid : Bool :=
  let tr := Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace
  tr.all fun e =>
    match e with
    | .env _ => true
    | .run ev =>
      match ev.cmd with
      | .send _ =>
        decide (GoodSendLen ev.input.length) &&
        tr.all fun e2 =>
          match e2 with
          | .env _ => true
          | .run rEv => !(hasInfix ev.input rEv.coins)
      | _ => true

private theorem dhRatchetSendInputsValid_eq_true : dhRatchetSendInputsValid = true := by
  decide +kernel

private theorem dhRatchet_send_input_facts
    {evs₁ : List CliEvent} {ev : RunEvent} {evs₂ : List CliEvent}
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace =
      evs₁ ++ .run ev :: evs₂)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    GoodSendLen ev.input.length ∧
      ∀ rEv, .run rEv ∈ evs₁ → ¬ (ev.input <:+: rEv.coins) := by
  obtain ⟨peer, hcmd⟩ := hsend
  have hev_mem :
      CliEvent.run ev ∈ Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hv := List.all_eq_true.mp dhRatchetSendInputsValid_eq_true (.run ev) hev_mem
  dsimp only at hv
  rw [hcmd] at hv
  dsimp only at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨hlen_b, hcoins_b⟩ := hv
  refine ⟨of_decide_eq_true hlen_b, fun rEv hrEv hinf => ?_⟩
  have hrEv_mem :
      CliEvent.run rEv ∈ Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace := by
    rw [hsplit]
    exact List.mem_append_left _ hrEv
  have hc := List.all_eq_true.mp hcoins_b (.run rEv) hrEv_mem
  dsimp only at hc
  rw [hasInfix_of_isInfix hinf] at hc
  cases hc

private theorem setupRandomsAt_size_32_or_64 {r : ProtocolSetup} {p : Nat × Nat}
    (hne : r.alice ≠ r.bob) (hp : p ∈ setupRandomsAt r) : p.2 = 32 ∨ p.2 = 64 := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hne] at hp
  rcases List.mem_append.mp hp with hfixed | hopk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · split at hopk
    · simp only [List.mem_singleton] at hopk
      rcases hopk with rfl
      exact Or.inl rfl
    · cases hopk

private theorem nonRandom_assumedInjective_dhRatchetI0
    (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes)
    (hinj : assumedInjective u = true)
    (hss32 : ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
      u = x.pack → (gamma dhRatchetI0 S g x.entropy).length = 32)
    (hlen : GoodSendLen (gamma dhRatchetI0 S g u).length) :
    ∃ rnd : DY.Random.Random DY.Bytes, u.view? DY.Random.Random = some rnd ∧ rnd.size ≠ 0 := by
  obtain ⟨hgt8, hmod16, hne32, _, hne1568⟩ := hlen
  rcases (assumedInjective_eq_true_iff u).mp hinj with
    hrnd | hdhPk | hdh | hkdf | hsym | htrunc | hencap | hss
  · exact hrnd
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdhPk
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dhPk dhRatchetI0 S g x]
      dsimp only [gDhPk, concretizeDhPk, node]
      rw [dhRatchetI0_publicKey, Option.getD_some]
      exact compLookupPub_length _
    exact False.elim (hne32 hg)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdh
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dh dhRatchetI0 S g x]
      dsimp only [gDh, concretizeDh, node]
      rw [dhRatchetI0_agreement, Option.getD_some]
      exact compLookupDh_length _ _
    exact False.elim (hne32 hg)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkdf
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kdf dhRatchetI0 S g x]
      exact length_hmacWith_32 (sha256CompressFunction dhRatchetI0) _ _
    exact False.elim (hne32 hg)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsym
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length % 16 = 0 := by
      unfold gamma
      rw [ms_pack_sym dhRatchetI0 S g x]
      dsimp only [gSym0, concretizeSym, node]
      rw [dhRatchetI0_aesEncrypt, Option.getD_some, dhRatchetAesPerm_length]
      omega
    exact False.elim (hmod16 hg)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htrunc
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length ≤ 8 := by
      have htake : gamma dhRatchetI0 S g x.pack = (gamma dhRatchetI0 S g x.input).take 8 := by
        unfold gamma
        rw [ms_pack_trunc dhRatchetI0 S g x]
        rfl
      rw [htake]
      exact List.length_take_le 8 _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hencap
    rcases pack_of_view_eq_some hx with rfl
    unfold gamma at hgt8 hne1568
    rw [ms_pack_kemEncap dhRatchetI0 S g x] at hgt8 hne1568
    dsimp only [gKemEncap, concretizeKemEncap] at hgt8 hne1568
    split at hgt8
    · rename_i h32
      simp only [h32, ↓reduceIte, node, dhRatchetI0_kyberEncaps, Option.getD_some,
        List.length_take, compKyberEncaps_length] at hne1568
      exact False.elim (hne1568 (by decide))
    · dsimp only [opaqueNode] at hgt8
      cases hgt8
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hss
    rcases pack_of_view_eq_some hx with rfl
    have he32 : (gamma' dhRatchetI0 S g x.entropy).bytes.length = 32 := hss32 x rfl
    have hg : (gamma dhRatchetI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kemSS dhRatchetI0 S g x]
      dsimp only [gKemSS, concretizeKemSS]
      simp only [he32, ↓reduceIte, node, dhRatchetI0_kyberEncaps, Option.getD_some,
        List.length_drop, compKyberEncaps_length]
    exact False.elim (hne32 hg)

theorem not_nextEventCollides_send
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : cliCompFitsPinned (dhRatchetI0, dhRatchetHooks0) r)
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace =
      evs₁ ++ .run ev :: evs₂)
    (hex : Explains dhRatchetI0 r S g ss vis evs₁)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    ¬ NextEventCollides dhRatchetI0 r S g ss vis evs₁ ev := by
  obtain ⟨hlen_good, hno_infix⟩ := dhRatchet_send_input_facts hsplit hsend
  obtain ⟨peer, hcmd⟩ := hsend
  unfold NextEventCollides
  rw [hcmd]
  rintro ⟨heme, hghosts⟩
  let tr := runTrace r ss
  have hgpt : gamma dhRatchetI0 S g (randTerm tr.length 32) = ev.input := by
    unfold BytesMatchEntry ptEntryAt at heme
    dsimp only [List.map] at heme
    exact List.head_eq_of_cons_eq heme.2
  have hg_mem : g ∈ PrefixExplainingGhosts dhRatchetI0 r S g ss evs₁ :=
    ⟨rfl, vis, hex⟩
  have hmcol := hghosts g hg_mem
  unfold MemoCollisionOn ptEntryAt at hmcol
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hmcol
  obtain ⟨x₁, hx₁_new, x₂, hx₂_terms, hsh_ne, _, hx₁_pts_imp, _, hbytes_eq⟩ := hmcol
  have ⟨hmemo_pt, hgam_pt_σ⟩ := gamma'_randTerm_32 dhRatchetI0 S g tr.length
  rw [hmemo_pt] at hx₁_new
  rcases List.mem_singleton.mp hx₁_new with rfl
  have hx₁_in_pts :
      randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨hx₂_not_pts, hx₂_inj, _⟩ := hx₁_pts_imp hx₁_in_pts
  have hb_sigma : g.σ tr.length 32 = ev.input := hgam_pt_σ.symm.trans hgpt
  have hx₂_bytes : x₂.2.2 = ev.input := hbytes_eq.symm.trans hb_sigma
  have hx₂_in_pre :
      x₂ ∈ (prefixTerms r tr vis).flatMap (fun t => (gamma' dhRatchetI0 S g t).memo) := by
    rcases List.mem_append.mp hx₂_terms with hpre | hnew
    · exact hpre
    · rw [hmemo_pt] at hnew
      rcases List.mem_singleton.mp hnew with rfl
      exact absurd rfl hsh_ne
  obtain ⟨t₀, ht₀, hx₂_memo⟩ := List.mem_flatMap.mp hx₂_in_pre
  rcases x₂ with ⟨u, sh, v⟩
  dsimp only at hx₂_not_pts hx₂_inj hx₂_bytes
  cases hx₂_bytes
  obtain ⟨hgam_u, hss32⟩ := memo_entry_inv dhRatchetI0 S g t₀ u sh ev.input hx₂_memo
  have hlen_u : GoodSendLen (gamma dhRatchetI0 S g u).length := hgam_u ▸ hlen_good
  obtain ⟨rnd, hview, hsz_ne⟩ :=
    nonRandom_assumedInjective_dhRatchetI0 S g u hx₂_inj hss32 hlen_u
  have hpack_u : u = rnd.pack := pack_of_view_eq_some hview
  obtain ⟨hgam_rnd, hrnd_eq⟩ := gamma_randTerm_of_ne_zero dhRatchetI0 S g rnd hsz_ne
  have hb_eq_σ : ev.input = g.σ rnd.timestamp rnd.size := by
    rw [hgam_u, hpack_u, hgam_rnd]
  have hu_eq_rand : u = randTerm rnd.timestamp rnd.size := hpack_u.trans hrnd_eq
  have hwf := hfit.1.1.1
  have hNe : r.alice ≠ r.bob := hwf.1
  have hrnd : RandAt tr rnd.timestamp rnd.size :=
    prefixTerms_termRandAt hex ht₀ u sh ev.input rnd hx₂_memo hview
  by_cases hsetup : rnd.timestamp < (setupTrace r).length
  · have hrnd_s : RandAt (setupTrace r) rnd.timestamp rnd.size :=
      randAt_of_le_of_lt (runSteps_le ss _) hsetup hrnd
    have hsetup_mem := randAt_setupTrace_mem_setupRandomsAt hNe hrnd_s
    have hfresh_eq : g.σ rnd.timestamp rnd.size = r.fresh rnd.timestamp rnd.size :=
      hex.1.1 (rnd.timestamp, rnd.size) hsetup_mem
    have hfresh_b : ev.input = r.fresh rnd.timestamp rnd.size :=
      hb_eq_σ.trans hfresh_eq
    have hfresh_len : (r.fresh rnd.timestamp rnd.size).length = rnd.size :=
      hwf.2.1 (rnd.timestamp, rnd.size) hsetup_mem
    have hlen_eq : ev.input.length = rnd.size := by
      rw [hfresh_b, hfresh_len]
    rcases setupRandomsAt_size_32_or_64 hNe hsetup_mem with h32 | h64
    · exact hlen_good.2.2.1 (hlen_eq.trans h32)
    · exact hlen_good.2.2.2.1 (hlen_eq.trans h64)
  · rcases matchesEvents_coinDrawn_infix hsz_ne hex.2.2.2 (Nat.not_lt.mp hsetup) hrnd with
      hpt_mem | ⟨v_rng, hv_mem, hv_kind, hsz32, hv_term⟩ |
        ⟨rEv, hrEv_mem, p, hp_infix, v_rng, _, _, hv_lay, hv_terms, hbme⟩
    · exact hx₂_not_pts (List.mem_append_left _ (hu_eq_rand ▸ hpt_mem))
    · have hlen32 : (g.σ rnd.timestamp rnd.size).length = rnd.size :=
        hex.2.1.1 v_rng hv_mem hv_kind rnd.timestamp rnd.size hsz_ne hv_term
      have hlen_eq : ev.input.length = 32 := by
        rw [hb_eq_σ, hlen32, hsz32]
      exact hlen_good.2.2.1 hlen_eq
    · unfold BytesMatchEntry at hbme
      rw [hv_lay, hv_terms] at hbme
      dsimp only [List.map] at hbme
      have hp_eq : gamma dhRatchetI0 S g (randTerm rnd.timestamp rnd.size) = p :=
        List.head_eq_of_cons_eq hbme.2
      have hb_eq_p : ev.input = p := by
        rw [hgam_u, hu_eq_rand, hp_eq]
      exact hno_infix rEv hrEv_mem (hb_eq_p ▸ hp_infix)

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.PtNoCollision
