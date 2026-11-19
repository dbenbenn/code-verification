/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtCoins
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

/-!
# Plaintext Collision Absence on All `.send` Events of `rcprTrace`

Proves `not_nextEventCollides_send`: no `.send` run event in `rcprTrace`
can satisfy `NextEventCollides` after an explained prefix under `rcprCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.PtNoCollision

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement
  (aesCbcEncryptSymbol sha256CompressFunction ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry Explains
   BytesMatchEntry MemoCollisionOn
   ptEntryAt plaintextTerms prefixTerms randTerm runTrace setupTrace setupRandomsAt
   gamma gamma' gDhPk gDh gKdf0 gSym0 gKemEncap gKemSS
   concretizeDhPk concretizeDh concretizeKdf concretizeSym concretizeKemEncap concretizeKemSS
   node opaqueNode assumedInjective)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides PrefixExplainingGhosts)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_dhPk ms_pack_dh ms_pack_kdf ms_pack_sym ms_pack_kemEncap ms_pack_kemSS)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
  (length_hmacWith_32 le_length_aesCbcEncrypt)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
  (runSteps_le randAt_of_le_of_lt randAt_setupTrace_mem_setupRandomsAt prefixTerms_termRandAt)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtCoins
  (matchesEvents_coinDrawn_infix)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8
  (Trunc8RowOK prefixTerms_trunc8OK)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned
   rcprAesBlock rcprKyberEncaps rcprKyberEncaps_length)

/-! ## 1. `.send`-Input Length and Coin-Infix Absence on `rcprTrace` -/

private def hasInfix (needle : HwBytes) : HwBytes → Bool
  | [] => needle.isEmpty
  | x :: xs => needle.isPrefixOf (x :: xs) || hasInfix needle xs

private theorem isPrefixOf_of_isPrefix :
    ∀ {a b : HwBytes}, a <+: b → a.isPrefixOf b = true
  | [], _, _ => rfl
  | _ :: _, _, ⟨t, rfl⟩ => by
    simp only [List.cons_append, List.isPrefixOf, beq_self_eq_true, Bool.true_and]
    exact isPrefixOf_of_isPrefix ⟨t, rfl⟩

private theorem hasInfix_append_left {a : HwBytes} :
    ∀ (s : HwBytes) {b : HwBytes}, hasInfix a b = true → hasInfix a (s ++ b) = true
  | [], _, h => h
  | _ :: xs, _, h => by
    simp only [List.cons_append, hasInfix, Bool.or_eq_true]
    exact Or.inr (hasInfix_append_left xs h)

private theorem hasInfix_of_isPrefix {a b : HwBytes} (h : a <+: b) : hasInfix a b = true := by
  cases b with
  | nil =>
    obtain ⟨_, ht⟩ := h
    cases (List.append_eq_nil_iff.mp ht).1
    rfl
  | cons _ _ =>
    simp only [hasInfix, Bool.or_eq_true]
    exact Or.inl (isPrefixOf_of_isPrefix h)

private theorem hasInfix_of_isInfix {a c : HwBytes} (h : a <:+: c) : hasInfix a c = true := by
  obtain ⟨s, t, rfl⟩ := h
  rw [List.append_assoc]
  exact hasInfix_append_left s (hasInfix_of_isPrefix ⟨t, rfl⟩)

private def rcprSendInputsValid : Bool :=
  rcprTrace.all fun e =>
    match e with
    | .env _ => true
    | .run ev =>
      match ev.cmd with
      | .send _ =>
        decide (0 < ev.input.length ∧ ev.input.length < 8) &&
        rcprTrace.all fun e2 =>
          match e2 with
          | .env _ => true
          | .run rEv => !(hasInfix ev.input rEv.coins)
      | _ => true

private theorem rcprSendInputsValid_eq_true : rcprSendInputsValid = true := by
  decide +kernel

private theorem rcpr_send_input_facts
    {evs₁ : List CliEvent} {ev : RunEvent} {evs₂ : List CliEvent}
    (hsplit : rcprTrace = evs₁ ++ .run ev :: evs₂)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    (0 < ev.input.length ∧ ev.input.length < 8) ∧
      ∀ rEv, .run rEv ∈ evs₁ → ¬ (ev.input <:+: rEv.coins) := by
  obtain ⟨peer, hcmd⟩ := hsend
  have hev_mem : CliEvent.run ev ∈ rcprTrace := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hv := List.all_eq_true.mp rcprSendInputsValid_eq_true (.run ev) hev_mem
  dsimp only at hv
  rw [hcmd] at hv
  dsimp only at hv
  rw [Bool.and_eq_true] at hv
  obtain ⟨hlen_b, hcoins_b⟩ := hv
  refine ⟨of_decide_eq_true hlen_b, fun rEv hrEv hinf => ?_⟩
  have hrEv_mem : CliEvent.run rEv ∈ rcprTrace := by
    rw [hsplit]
    exact List.mem_append_left _ hrEv
  have hc := List.all_eq_true.mp hcoins_b (.run rEv) hrEv_mem
  dsimp only at hc
  rw [hasInfix_of_isInfix hinf] at hc
  cases hc

/-! ## 2. `assumedInjective` Output Length Elimination & `not_nextEventCollides_send` -/

private theorem setupRandomsAt_size_ge_32 {r : ProtocolSetup} {p : Nat × Nat}
    (hNe : r.alice ≠ r.bob) (hp : p ∈ setupRandomsAt r) : 32 ≤ p.2 := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe] at hp
  rcases List.mem_append.mp hp with hfixed | hopk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · split at hopk
    · simp only [List.mem_singleton] at hopk
      rcases hopk with rfl
      decide
    · cases hopk

private theorem nonRandom_assumedInjective_generic
    (interp : ExternInterpretation)
    (hlaws : ExternCryptoLawsHold interp)
    (haes_len : ∀ text k iv, 16 ≤ ((interp aesCbcEncryptSymbol [text, k, iv]).getD []).length)
    (hkyber_len : ∀ pk rand, ((interp kyberEncapsSymbol [pk, rand]).getD []).length = 1600)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (u sh : DY.Bytes)
    (hinj : assumedInjective u = true)
    (hnot_known : ¬ u.AttackerKnows tr)
    (hss32 : ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
      u = x.pack → (gamma interp S g x.entropy).length = 32)
    (htrunc8 : Trunc8RowOK tr (u, sh, gamma interp S g u))
    (hlen_pos : 0 < (gamma interp S g u).length)
    (hlen_lt8 : (gamma interp S g u).length < 8) :
    ∃ rnd : DY.Random.Random DY.Bytes, u.view? DY.Random.Random = some rnd ∧ rnd.size ≠ 0 := by
  rcases (assumedInjective_eq_true_iff u).mp hinj with
    hrnd | hdhPk | hdh | hkdf | hsym | htrunc | hencap | hss
  · exact hrnd
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdhPk
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma interp S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dhPk interp S g x]
      dsimp only [gDhPk, concretizeDhPk, node]
      exact hlaws.x25519_public_key_length _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdh
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma interp S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dh interp S g x]
      dsimp only [gDh, concretizeDh, node]
      exact hlaws.x25519_agreement_length _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkdf
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma interp S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kdf interp S g x]
      exact length_hmacWith_32 (sha256CompressFunction interp) _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsym
    rcases pack_of_view_eq_some hx with rfl
    have hg : 16 ≤ (gamma interp S g x.pack).length := by
      unfold gamma
      rw [ms_pack_sym interp S g x]
      dsimp only [gSym0, concretizeSym, node]
      exact haes_len _ _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htrunc
    rcases pack_of_view_eq_some hx with rfl
    rcases htrunc8 x rfl with hkn | hge8
    · exact absurd hkn hnot_known
    · dsimp only at hge8
      omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hencap
    rcases pack_of_view_eq_some hx with rfl
    unfold gamma at hlen_pos hlen_lt8
    rw [ms_pack_kemEncap interp S g x] at hlen_pos hlen_lt8
    dsimp only [gKemEncap, concretizeKemEncap] at hlen_pos hlen_lt8
    split at hlen_pos
    · rename_i h32
      simp only [h32, ↓reduceIte, node, List.length_take, hkyber_len] at hlen_lt8
      omega
    · dsimp only [opaqueNode] at hlen_pos
      cases hlen_pos
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hss
    rcases pack_of_view_eq_some hx with rfl
    have he32 : (gamma' interp S g x.entropy).bytes.length = 32 := hss32 x rfl
    have hg : (gamma interp S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kemSS interp S g x]
      dsimp only [gKemSS, concretizeKemSS]
      simp only [he32, ↓reduceIte, node, List.length_drop, hkyber_len]
    omega

private theorem not_nextEventCollides_send_generic
    (interp : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hwf : ProtocolSetupWF r)
    (hlaws : ExternCryptoLawsHold interp)
    (haes_len : ∀ text k iv, 16 ≤ ((interp aesCbcEncryptSymbol [text, k, iv]).getD []).length)
    (hkyber_len : ∀ pk rand, ((interp kyberEncapsSymbol [pk, rand]).getD []).length = 1600)
    (hsplit : rcprTrace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains interp r S g ss vis evs₁)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  obtain ⟨⟨hlen_pos, hlen_lt8⟩, hno_infix⟩ := rcpr_send_input_facts hsplit hsend
  obtain ⟨peer, hcmd⟩ := hsend
  unfold NextEventCollides
  rw [hcmd]
  rintro ⟨heme, hghosts⟩
  let tr := runTrace r ss
  have hgpt : gamma interp S g (randTerm tr.length 32) = ev.input := by
    unfold BytesMatchEntry ptEntryAt at heme
    dsimp only [List.map] at heme
    exact List.head_eq_of_cons_eq heme.2
  have hg_mem : g ∈ PrefixExplainingGhosts interp r S g ss evs₁ :=
    ⟨rfl, vis, hex⟩
  have hmcol := hghosts g hg_mem
  unfold MemoCollisionOn ptEntryAt at hmcol
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hmcol
  obtain ⟨x₁, hx₁_new, x₂, hx₂_terms, hsh_ne, _, hx₁_pts_imp, _, hbytes_eq⟩ := hmcol
  have ⟨hmemo_pt, hgam_pt_σ⟩ := gamma'_randTerm_32 interp S g tr.length
  rw [hmemo_pt] at hx₁_new
  rcases List.mem_singleton.mp hx₁_new with rfl
  have hx₁_in_pts :
      randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨hx₂_not_pts, hx₂_inj, hx₂_not_known⟩ := hx₁_pts_imp hx₁_in_pts
  have hb_sigma : g.σ tr.length 32 = ev.input := hgam_pt_σ.symm.trans hgpt
  have hx₂_bytes : x₂.2.2 = ev.input := hbytes_eq.symm.trans hb_sigma
  have hx₂_in_pre :
      x₂ ∈ (prefixTerms r tr vis).flatMap (fun t => (gamma' interp S g t).memo) := by
    rcases List.mem_append.mp hx₂_terms with hpre | hnew
    · exact hpre
    · rw [hmemo_pt] at hnew
      rcases List.mem_singleton.mp hnew with rfl
      exact absurd rfl hsh_ne
  obtain ⟨t₀, ht₀, hx₂_memo⟩ := List.mem_flatMap.mp hx₂_in_pre
  rcases x₂ with ⟨u, sh, v⟩
  dsimp only at hx₂_not_pts hx₂_inj hx₂_not_known hx₂_bytes
  cases hx₂_bytes
  obtain ⟨hgam_u, hss32⟩ := memo_entry_inv interp S g t₀ u sh ev.input hx₂_memo
  have htrunc_row : Trunc8RowOK tr (u, sh, gamma interp S g u) := by
    rw [← hgam_u]
    exact prefixTerms_trunc8OK hex ht₀ (u, sh, ev.input) hx₂_memo
  have hlen_u_pos : 0 < (gamma interp S g u).length := hgam_u ▸ hlen_pos
  have hlen_u_lt8 : (gamma interp S g u).length < 8 := hgam_u ▸ hlen_lt8
  obtain ⟨rnd, hview, hsz_ne⟩ :=
    nonRandom_assumedInjective_generic interp hlaws haes_len hkyber_len S g tr u sh
      hx₂_inj hx₂_not_known hss32 htrunc_row hlen_u_pos hlen_u_lt8
  have hpack_u : u = rnd.pack := pack_of_view_eq_some hview
  obtain ⟨hgam_rnd, hrnd_eq⟩ := gamma_randTerm_of_ne_zero interp S g rnd hsz_ne
  have hb_eq_σ : ev.input = g.σ rnd.timestamp rnd.size := by
    rw [hgam_u, hpack_u, hgam_rnd]
  have hu_eq_rand : u = randTerm rnd.timestamp rnd.size := hpack_u.trans hrnd_eq
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
    have hge32 : 32 ≤ rnd.size := setupRandomsAt_size_ge_32 hNe hsetup_mem
    have hlen_eq : ev.input.length = rnd.size := by
      rw [hfresh_b, hfresh_len]
    omega
  · rcases matchesEvents_coinDrawn_infix hsz_ne hex.2.2.2 (Nat.not_lt.mp hsetup) hrnd with
      hpt_mem | ⟨v_rng, hv_mem, hv_kind, hsz32, hv_term⟩ |
        ⟨rEv, hrEv_mem, p, hp_infix, v_rng, _, _, hv_lay, hv_terms, hbme⟩
    · exact hx₂_not_pts (List.mem_append_left _ (hu_eq_rand ▸ hpt_mem))
    · have hlen32 : (g.σ rnd.timestamp rnd.size).length = rnd.size :=
        hex.2.1.1 v_rng hv_mem hv_kind rnd.timestamp rnd.size hsz_ne hv_term
      have hlen_eq : ev.input.length = rnd.size := by
        rw [hb_eq_σ, hlen32]
      omega
    · unfold BytesMatchEntry at hbme
      rw [hv_lay, hv_terms] at hbme
      dsimp only [List.map] at hbme
      have hp_eq : gamma interp S g (randTerm rnd.timestamp rnd.size) = p :=
        List.head_eq_of_cons_eq hbme.2
      have hb_eq_p : ev.input = p := by
        rw [hgam_u, hu_eq_rand, hp_eq]
      exact hno_infix rEv hrEv_mem (hb_eq_p ▸ hp_infix)

theorem not_nextEventCollides_send
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hsplit : rcprTrace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains rcprI0 r S g ss vis evs₁)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    ¬ NextEventCollides rcprI0 r S g ss vis evs₁ ev := by
  refine not_nextEventCollides_send_generic rcprI0 r S g ss vis evs₁ ev evs₂
    hfit.1.1.1 hfit.2.1.1 ?_ ?_ hsplit hex hsend
  · intro text k iv
    change 16 ≤ (CryptoGames.LibsignalSession.aesCbcEncrypt rcprAesBlock
      (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text).length
    exact le_length_aesCbcEncrypt rcprAesBlock
      (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text
  · intro _ rand
    change (rcprKyberEncaps rand).length = 1600
    exact rcprKyberEncaps_length rand

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.PtNoCollision
