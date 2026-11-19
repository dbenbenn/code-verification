/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Gamma
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.CleanStepView
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Prefix `Explains` & Acceptance Helpers (`RecvNoCollision/CleanExplains.lean`)

Establishes on the 5-step canonical clean schedule `(gClean r cls, ssClean cls k, visClean r cls k)`:
1. `ghostWF_visClean`: `GhostWF (gClean r cls) (visClean r cls m)` for `m ≤ 5`.
2. `cleanPreKeyRep_mem_2` & `m1Clean_mem_recvRepresentationsOn_4`: canonical representation
   membership at Call 2 (`preKeyRepresentationsOn`) and Call 4 (`recvRepresentationsOn`).
3. `explains_ssClean_le5` & `explains_ssClean`: `Explains rcprI0 r S (gClean r cls)
   (ssClean cls k) (visClean r cls k) (rcprTrace.take k)` for `k ≤ 5` (and `k ≤ 4`).
4. `accepts_ssClean_4`: `ModelAcceptsTermAfterAttackerSends` on `m1Clean cls` at Call 4 (`ev 4`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision

open scoped DY.Libsignal.Composed
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds PreKeyFields
   OpkNamed gamma slice ecKey pubBytes secretBytes preKeyWire parsePreKeyWire
   setupTrace setupPublic runTrace runSteps stepView rngEntry kyberCoinEntries randTerm
   GhostAndSemMatchSetup GhostWF BytesMatchEntry DrawsMatch OutputsMatch
   ReadsFaithfully PathFaithfulAt RunMatches MatchesEventsAt Explains
   recvRepresentationsOn preKeyRepresentationsOn getMessageSentAt_attackerKnows
   runWrapped inputKind nextBundleIds)
open DY.Libsignal.Composed.Refinement.Cli (ModelAcceptsTermAfterAttackerSends)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikB spkB pqskB spkNonce pqNonce dhsA t4 t5 bh1 o1 stA0)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprHooks0 rcprCompFitsPinned rcprTrace rcprPubOfIdx rcprPubOfIdx_length)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (ev rcprTrace_take_succ ev0_cmd_and_exit ev0_bundle_slices ev0_coins_facts
   ev1_to_ev2 ev2_pt_eq_ev1 ev3_to_ev4 ev4_pt_eq_ev3 ev1_party_cmd ev2_party_cmd
   ev3_party_cmd ev4_party_cmd send_coins_ge_64 ev1_runWrapped ev3_runWrapped
   ev2_input_len_lt_2pow63 ev2_coins_ge_32 ev4_coins_ge_32 ev2_has_preKey ev2_full_fields
   ev4_whisper nextBundleIds_non_init ValidCoinLens r_names_of_fit setupTrace_eq_t4
   pt0Clean coins0Clean key0Clean m0Clean trClean2 stB2Clean pt1Clean coins1Clean key1Clean
   m1Clean trClean3 trClean4 s0Clean s1Clean s2Clean s3Clean s4Clean cleanCallSteps
   cleanCallSteps_length ssClean ssClean_succ s0_next_ok s1_next_ok s2_next_ok s3_next_ok
   s4_next_ok runSteps_ssClean modelRunWF_ssClean pqAddrBytes gClean gClean_sigma_22
   gClean_sigma_23 gClean_sigma_24 gClean_sigma_31 gClean_sigma_32 gClean_sigma_38
   gClean_sigma_47 gClean_sigma_48 gClean_sigma_54 gClean_addr_m0 gClean_addr_m1
   gamma_dhPk_spkB gamma_dhPk_dhsA gamma_dhPk_dhsB1)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
  (gamma_randTerm_ne_zero encMsg_mem_recvRepresentationsOn encMsg_faithfulInner)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.ev

private theorem ssClean_succ_of_get {cls : Nat → Nat} {k : Nat} {s : Step}
    (hk : k < 5) (hs : (cleanCallSteps cls)[k]? = some s) :
    ssClean cls (k + 1) = ssClean cls k ++ [s] := by
  obtain ⟨s', hs', heq⟩ := ssClean_succ cls hk
  rw [hs] at hs'
  injection hs' with hs'
  subst hs'
  exact heq

/-! ## 1. `GhostWF` on `(gClean r cls, visClean r cls m)` (`m ≤ 5`) -/

private def VisStepWF (g : Ghost) (vs : List VisEntry) : Prop :=
  (∀ v ∈ vs, v.kind = .rng → ∀ ts n, n ≠ 0 → randTerm ts n ∈ v.terms → (g.σ ts n).length = n) ∧
  (∀ v ∈ vs, v.kind = .send →
    (v.layout = .preKeySend →
      ∀ ek ct msg pm, v.terms = [ek, ct, msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = pqAddrBytes) ∧
    (v.layout = .whisper →
      ∀ msg pm, v.terms = [msg] → parseTrSignalMsg msg = some pm →
        g.addr pm.wire = []))

private theorem visStepWF_append {g : Ghost} {xs ys : List VisEntry}
    (hx : VisStepWF g xs) (hy : VisStepWF g ys) : VisStepWF g (xs ++ ys) :=
  ⟨fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.1 v h, hy.1 v h],
   fun v hv => by rcases List.mem_append.mp hv with h | h; exacts [hx.2 v h, hy.2 v h]⟩

private theorem randTerm_inj {ts ts' n n' : Nat}
    (heq : randTerm ts n = randTerm ts' n') : ts = ts' ∧ n = n' := by
  have h := Symbolic.DYBridge.DY.BytesView.pack_inj.mp heq
  exact ⟨congrArg DY.Random.Random.timestamp h, congrArg DY.Random.Random.size h⟩

private theorem take_len_eq {α : Type} {xs : List α} {n : Nat} (h : n ≤ xs.length) :
    (xs.take n).length = n :=
  List.length_take_of_le h

private theorem no_rng_or_send_single {g : Ghost} (v₀ : VisEntry)
    (h1 : v₀.kind ≠ .rng) (h2 : v₀.kind ≠ .send) :
    VisStepWF g [v₀] :=
  ⟨fun v hv hk => by simp only [List.mem_singleton] at hv; subst hv; exact absurd hk h1,
   fun v hv hk => by simp only [List.mem_singleton] at hv; subst hv; exact absurd hk h2⟩

private theorem visStepWF_cleanStep {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls) :
    ∀ k < 5, ∀ s, (cleanCallSteps cls)[k]? = some s →
      VisStepWF (gClean r cls)
        (stepView s (runTrace r (ssClean cls k)) (runWrapped (ev k))) := by
  intro k hk s hs
  have hrs := runSteps_ssClean cls
  match k with
  | 0 =>
    injection hs with hs0; subst hs0
    have htr0 : runTrace r (ssClean cls 0) = t4 := by
      unfold runTrace; rw [setupTrace_eq_t4 hfit, hrs.1]
    rw [htr0, stepView_s0]
    have hc0 := ev0_coins_facts.1
    refine ⟨?_, fun v hv hk => by
      simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
        List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl <;> cases hk⟩
    intro v hv hkind ts n _ hmem
    simp only [kyberCoinEntries, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | ⟨j, _, rfl⟩ | rfl
    · cases hkind
    · simp only [rngEntry, List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
      rw [gClean_sigma_22]; simp only [slice, List.drop_zero]; exact take_len_eq (by omega)
    · simp only [List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
      rw [gClean_sigma_23]; exact ev0_coins_facts.2.2.2.1
    · simp only [rngEntry, List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
      rw [gClean_sigma_24]; dsimp only [slice]
      exact take_len_eq (by rw [List.length_drop, hc0])
  | 1 =>
    injection hs with hs1; subst hs1
    have htr1 : runTrace r (ssClean cls 1) = t5 := by
      unfold runTrace; rw [setupTrace_eq_t4 hfit, hrs.2.1]
    rw [htr1, ev1_runWrapped, stepView_s1]
    have hcl_cases := hv 0 (by decide)
    have hcoins1 : 64 ≤ (ev 1).coins.length := send_coins_ge_64 (s := 0) (by decide)
    refine visStepWF_append
      (no_rng_or_send_single ⟨.pt, [randTerm 31 32], .single, none⟩ (by decide) (by decide))
      (visStepWF_append ?_ ?_)
    · by_cases hcl0 : cls 0 = 0
      · simp [hcl0, VisStepWF]
      · simp only [bne_iff_ne.mpr hcl0, ↓reduceIte]
        refine ⟨?_, fun v hv hk => by simp [rngEntry] at hv; subst hv; cases hk⟩
        intro v hv _ ts n _ hmem
        simp only [List.mem_singleton] at hv; subst hv
        simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_32]; exact take_len_eq (by rcases hcl_cases with h | h | h <;> omega)
    · refine ⟨(fun v hv hk => by simp at hv; subst hv; cases hk), fun v hv _ => ?_⟩
      simp only [List.mem_singleton] at hv; subst hv
      refine ⟨fun _ ek ct msg pm hterms hparse => ?_, fun hl => by cases hl⟩
      simp only [List.cons.injEq, and_true] at hterms; rcases hterms with ⟨_, _, rfl⟩
      rw [m0Clean, parse_encMsg] at hparse; injection hparse with hpm; subst hpm
      exact gClean_addr_m0 r cls
  | 2 =>
    injection hs with hs2; subst hs2
    have htr2 : runTrace r (ssClean cls 2) = trClean2 cls := by
      unfold runTrace; rw [setupTrace_eq_t4 hfit, hrs.2.2.1]
    rw [htr2, stepView_s2]; have hcoins2 := ev2_coins_ge_32
    refine ⟨?_, fun v hv hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | rfl <;> cases hk⟩
    intro v hv hkind ts n _ hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · cases hkind
    · simp only [rngEntry, List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
      rw [gClean_sigma_38]; exact take_len_eq (by omega)
    · cases hkind
  | 3 =>
    injection hs with hs3; subst hs3
    have htr3 : runTrace r (ssClean cls 3) = trClean3 cls := by
      unfold runTrace; rw [setupTrace_eq_t4 hfit, hrs.2.2.2.1]
    rw [htr3, ev3_runWrapped, stepView_s3]
    have hcl_cases := hv 1 (by decide)
    have hcoins3 : 64 ≤ (ev 3).coins.length := send_coins_ge_64 (s := 1) (by decide)
    refine visStepWF_append
      (no_rng_or_send_single ⟨.pt, [randTerm 47 32], .single, none⟩ (by decide) (by decide))
      (visStepWF_append ?_ ?_)
    · by_cases hcl1 : cls 1 = 0
      · simp [hcl1, VisStepWF]
      · simp only [bne_iff_ne.mpr hcl1, ↓reduceIte]
        refine ⟨?_, fun v hv hk => by simp [rngEntry] at hv; subst hv; cases hk⟩
        intro v hv _ ts n _ hmem
        simp only [List.mem_singleton] at hv; subst hv
        simp only [rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
        rw [gClean_sigma_48]; exact take_len_eq (by rcases hcl_cases with h | h | h <;> omega)
    · refine ⟨(fun v hv hk => by simp at hv; subst hv; cases hk), fun v hv _ => ?_⟩
      simp only [List.mem_singleton] at hv; subst hv
      refine ⟨(fun hl => by cases hl), fun _ msg pm hterms hparse => ?_⟩
      simp only [List.cons.injEq, and_true] at hterms; subst hterms
      rw [m1Clean, parse_encMsg] at hparse; injection hparse with hpm; subst hpm
      exact gClean_addr_m1 r cls
  | 4 =>
    injection hs with hs4; subst hs4
    have htr4 : runTrace r (ssClean cls 4) = trClean4 cls := by
      unfold runTrace; rw [setupTrace_eq_t4 hfit, hrs.2.2.2.2.1]
    rw [htr4, ev4_whisper.1, stepView_s4]; have hcoins4 := ev4_coins_ge_32
    refine ⟨?_, fun v hv hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, rngEntry] at hv
      rcases hv with rfl | rfl | rfl <;> cases hk⟩
    intro v hv hkind ts n _ hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · cases hkind
    · simp only [rngEntry, List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := randTerm_inj hmem
      rw [gClean_sigma_54]; exact take_len_eq (by omega)
    · cases hkind
  | n + 5 => omega

theorem ghostWF_visClean {r : ProtocolSetup} {cls : Nat → Nat} (m : Nat)
    (hm : m ≤ 5) (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls) :
    GhostWF (gClean r cls) (visClean r cls m) := by
  have haddr : ∀ t, (gClean r cls).addr t = [] ∨ (gClean r cls).addr t = pqAddrBytes := by
    intro t; unfold gClean; dsimp only; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hsteps : ∀ j ≤ 5, VisStepWF (gClean r cls) (visClean r cls j) := by
    intro j hj
    induction j with
    | zero => exact ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩
    | succ k ih =>
      have hk : k < 5 := by omega
      obtain ⟨s, hs, _⟩ := ssClean_succ cls hk
      rw [visClean_succ hk hs]
      exact visStepWF_append (ih (by omega)) (visStepWF_cleanStep hfit hv k hk s hs)
  obtain ⟨hrng, hsend⟩ := hsteps m hm
  exact ⟨hrng, haddr, hsend⟩

/-! ## 2. Clean Representation Membership & `DrawsMatch` Helpers -/

private theorem gamma_randTerm_pos {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts n : Nat} (hn : n ≠ 0) :
    gamma rcprI0 S g (randTerm ts n) = g.σ ts n :=
  gamma_randTerm_ne_zero rcprI0 S g hn

private theorem ikA_pub_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    pubBytes rcprI0 (secretBytes r 0) = rcprPubOfIdx ⟨0, by decide⟩ := by
  rw [hfit.1.1.2.2.2.2.2.2.1]
  decide +kernel

private theorem dhsA_rk_len {r : ProtocolSetup} (S : OpaqueSymbolSemantics) (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    (gamma rcprI0 S (gClean r cls) (dhPk dhsA)).length = 32 := by
  rw [gamma_dhPk_dhsA hfit]
  exact rcprPubOfIdx_length _

private theorem dhsB1_rk_len {r : ProtocolSetup} (S : OpaqueSymbolSemantics) (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    (gamma rcprI0 S (gClean r cls) (dhPk (stB2Clean cls).dhs)).length = 32 := by
  change (gamma rcprI0 S (gClean r cls) (dhPk Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.dhsB1Clean)).length = 32
  rw [gamma_dhPk_dhsB1 hfit]
  exact rcprPubOfIdx_length _

private theorem tryFrom_of_parsePreKeyWire {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at hp
  rcases b with _ | ⟨t, _ | ⟨vb, rest⟩⟩
  · cases hp
  · dsimp only at hp
    split at hp <;> cases hp
  · dsimp only at hp
    split at hp
    · unfold DY.Libsignal.Composed.Refinement.parsePreKey at hp
      dsimp only at hp
      split at hp
      · cases hp
      · split at hp
        · cases hp
        · split at hp
          · split at hp
            · split at hp
              · next inner htry =>
                injection hp with hp'; subst hp'; exact htry
              · cases hp
            · cases hp
          · cases hp
    · cases hp

theorem cleanPreKeyRep_mem_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) :
    ⟨o1.ek, o1.ct, m0Clean cls⟩ ∈
      preKeyRepresentationsOn rcprI0 r S (gClean r cls)
        (runTrace r (ssClean cls 2)) (ev 2).input ∧
    OpkNamed r (ev 2).input false := by
  have hrun2 : runTrace r (ssClean cls 2) = trClean2 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.1]
  rw [hrun2]
  obtain ⟨hs25, hs26, hs37⟩ := trClean2_sent_eqs cls
  obtain ⟨p₂, hp₂⟩ := ev2_has_preKey
  have hfull := ev2_full_fields hp₂
  have hev2_in : (ev 2).input = preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)) := by
    have hcomb := ev1_to_ev2.symm.trans hev1_out
    injection hcomb with hpair; exact (Prod.mk.inj hpair).2
  obtain ⟨_, hp₂_ct, hp₂_bk, hp₂_msg⟩ :=
    parsePreKeyWire_preKeyWire_inv hev2_in ev2_input_len_lt_2pow63 hp₂
  have hopk : OpkNamed r (ev 2).input false := ⟨p₂, hp₂, hfull.2.2.1⟩
  have hbk_take : p₂.baseKey.take 33 = ecKey (gamma rcprI0 S (gClean r cls) o1.ek) := by
    have hlen33 : p₂.baseKey.length = 33 := by rw [hfull.2.2.2.2.2.1]; decide
    rw [List.take_of_length_le (Nat.le_of_eq hlen33), hp₂_bk]
  have hik_take : p₂.identityKey.take 33 = ecKey (pubBytes rcprI0 (secretBytes r 0)) := by
    rw [hfull.2.2.2.2.2.2.1, ikA_pub_eq hfit]
    have hlen33 : (ecKey (rcprPubOfIdx ⟨0, by decide⟩)).length = 33 := by decide
    exact List.take_of_length_le (Nat.le_of_eq hlen33)
  have hspkId : p₂.signedPreKeyId = r.spkId := by rw [hfull.2.1, hfit.1.1.2.2.2.2.1]; rfl
  have hkpkId : p₂.kyberPreKeyId = some r.kpkId := by rw [hfull.2.2.2.1, hfit.1.1.2.2.2.2.2.1]; rfl
  have hfaith : DY.Libsignal.Composed.Refinement.FaithfulInner rcprI0 S (gClean r cls) (m0Clean cls) p₂ :=
    encMsg_faithfulInner hp₂_msg.symm (dhsA_rk_len S cls hfit) (tryFrom_of_parsePreKeyWire hp₂)
  have hver : p₂.version = 4 := by
    have hp' := hp₂; rw [hev2_in] at hp'
    simp only [parsePreKeyWire, preKeyWire, ↓reduceIte, DY.Libsignal.Composed.Refinement.parsePreKey] at hp'
    split at hp'
    · cases hp'
    · split at hp'
      · cases hp'
      · split at hp'
        · split at hp'
          · split at hp'
            · injection hp' with hp'; subst hp'; dsimp only; decide
            · cases hp'
          · cases hp'
        · cases hp'
  refine ⟨⟨getMessageSentAt_attackerKnows hs25, getMessageSentAt_attackerKnows hs26,
    getMessageSentAt_attackerKnows hs37,
    ⟨p₂, hp₂, hbk_take, hp₂_ct, hp₂_msg, hver, hspkId, hkpkId, hik_take, false, hopk⟩,
    p₂, hp₂, hfaith⟩, hopk⟩

theorem m1Clean_mem_recvRepresentationsOn_4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hev3_out : (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    m1Clean cls ∈
      recvRepresentationsOn rcprI0 S (gClean r cls)
        (runTrace r (ssClean cls 4)) ((ev 4).input.drop 1) := by
  have hrun4 : runTrace r (ssClean cls 4) = trClean4 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.2.1]
  rw [hrun4]
  have hin4 : (ev 4).input = wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls) := by
    have hcomb := ev3_to_ev4.symm.trans hev3_out
    injection hcomb with hpair
    exact (Prod.mk.inj hpair).2
  have hdrop : (ev 4).input.drop 1 = gamma rcprI0 S (gClean r cls) (m1Clean cls) := by
    rw [hin4]; rfl
  exact encMsg_mem_recvRepresentationsOn
    (getMessageSentAt_attackerKnows (trClean4_sent_53 cls))
    hdrop.symm (dhsB1_rk_len S cls hfit)

private theorem forall2_append {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h1 : List.Forall₂ R xs₁ ys₁) (h2 : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h1 with
  | nil => exact h2
  | cons hr _ ih => exact .cons hr ih

private theorem kyber_pieces_flatten :
    ∀ n ≤ 32, ∀ (b : HwBytes), b.length = 192 →
      ((List.range n).map fun j => slice b (32 + 4 * j) 4).flatten = slice b 32 (4 * n)
  | 0, _, _, _ => by simp [slice]
  | n + 1, hn, b, hlen => by
    rw [List.range_succ, List.map_append, List.flatten_append,
      kyber_pieces_flatten n (by omega) b hlen]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, slice]
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, List.take_add, List.drop_drop]

private theorem kyber_pieces_forall2 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) :
    ∀ n ≤ 32,
      List.Forall₂
        (fun p v => BytesMatchEntry rcprI0 r S (gClean r cls) .rng p v)
        ((List.range n).map fun j => slice (ev 0).coins (32 + 4 * j) 4)
        ((List.range n).map fun j => ⟨.rng, [randTerm 23 32], .kyberCoin j, none⟩)
  | 0, _ => .nil
  | n + 1, hn => by
    obtain ⟨hlen192, _, _, hent_len, _, hent_at⟩ := ev0_coins_facts
    rw [List.range_succ, List.map_append, List.map_append]
    refine forall2_append (kyber_pieces_forall2 r S cls n (by omega)) ?_
    refine List.Forall₂.cons ?_ .nil
    refine ⟨rfl, ?_, randTerm 23 32, rfl, ?_, ?_⟩
    · simp only [slice, List.length_take, List.length_drop, hlen192]; omega
    · rw [gamma_randTerm_pos (by decide), gClean_sigma_23]; exact hent_len
    · rw [gamma_randTerm_pos (by decide), gClean_sigma_23, hent_at n (by omega)]
      dsimp only [slice]
      cases (ev 0).coins.drop (32 + 4 * n) <;> rfl

private theorem drawsMatch_ev0 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) :
    DrawsMatch rcprI0 r S (gClean r cls)
      (rngEntry (randTerm 22 32) ::
        (kyberCoinEntries (randTerm 23 32) ++
          [{ rngEntry (randTerm 24 32) with anchor := some 27 }]))
      (ev 0).coins := by
  have hlen192 := ev0_coins_facts.1
  let kpcs := (List.range 32).map fun j => slice (ev 0).coins (32 + 4 * j) 4
  refine ⟨slice (ev 0).coins 0 32 :: (kpcs ++ [slice (ev 0).coins 160 32]), ?_, ?_, ?_⟩
  · intro p hp
    dsimp only [kpcs] at hp
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | ⟨j, hj, rfl⟩ | rfl
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
    · intro heq; have := congrArg List.length heq
      simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega
  · simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil]
    rw [kyber_pieces_flatten 32 (Nat.le_refl 32) (ev 0).coins hlen192]
    have hcat : slice (ev 0).coins 0 32 ++ (slice (ev 0).coins 32 128 ++ slice (ev 0).coins 160 32) =
        (ev 0).coins := by
      simp only [slice, List.drop_zero]
      rw [← List.append_assoc]
      have h1 : (ev 0).coins.take 32 ++ ((ev 0).coins.drop 32).take 128 =
          (ev 0).coins.take 160 := by
        simpa using (List.take_add (i := 32) (j := 128) (l := (ev 0).coins)).symm
      rw [h1]
      have h2 : (ev 0).coins.take 160 ++ ((ev 0).coins.drop 160).take 32 =
          (ev 0).coins.take 192 := by
        simpa using (List.take_add (i := 160) (j := 32) (l := (ev 0).coins)).symm
      rw [h2, List.take_of_length_le (Nat.le_of_eq hlen192)]
    rw [hcat]
  · refine List.Forall₂.cons ?_ (forall2_append (kyber_pieces_forall2 r S cls 32 (Nat.le_refl 32))
      (List.Forall₂.cons ?_ .nil))
    · refine ⟨rfl, ?_⟩
      simp only [rngEntry, List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
        gClean_sigma_22]
    · refine ⟨rfl, ?_⟩
      simp only [rngEntry, List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
        gClean_sigma_24]

private theorem drawsMatch_single_pos (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts n : Nat} {coins : HwBytes}
    (hn : n ≠ 0) (hlen : n ≤ coins.length)
    (hsig : (gClean r cls).σ ts n = coins.take n) :
    DrawsMatch rcprI0 r S (gClean r cls) [rngEntry (randTerm ts n)] coins := by
  refine ⟨[coins.take n], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
    intro heq; have := congrArg List.length heq
    simp only [List.length_take, List.length_nil] at this; omega
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]; exact List.take_prefix n coins
  · simp only [rngEntry, List.map_cons, List.map_nil, gamma_randTerm_pos hn, hsig]

private theorem drawsMatch_single32 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts : Nat} {coins : HwBytes}
    (hlen : 32 ≤ coins.length) (hsig : (gClean r cls).σ ts 32 = coins.take 32) :
    DrawsMatch rcprI0 r S (gClean r cls) [rngEntry (randTerm ts 32)] coins :=
  drawsMatch_single_pos r S cls (by decide) hlen hsig

private theorem drawsMatch_enc (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts cl : Nat} {coins : HwBytes}
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64) (hlen : 64 ≤ coins.length)
    (hsig : (gClean r cls).σ ts cl = coins.take cl) :
    DrawsMatch rcprI0 r S (gClean r cls)
      (if cl != 0 then [rngEntry (randTerm ts cl)] else []) coins := by
  rcases hcl with rfl | rfl | rfl
  · exact ⟨[], by simp, List.nil_prefix, .nil⟩
  · exact drawsMatch_single_pos r S cls (by decide) (by omega) hsig
  · exact drawsMatch_single_pos r S cls (by decide) hlen hsig

/-! ## 3. Per-Call `RunMatches` & Right-Append `CleanStepsMatch` -/

private inductive CleanStepsMatch (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    Option BundlePreKeyIds → Option BundlePreKeyIds → ExecTrace →
      List Step → List CliEvent → List VisEntry → Prop
  | nil (ids : Option BundlePreKeyIds) (tr : ExecTrace) :
      CleanStepsMatch r S g ids ids tr [] [] []
  | cons {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {s : Step} {ss : List Step} {e : RunEvent} {evs : List CliEvent}
      {v vs : List VisEntry} :
      mid = nextBundleIds ids e →
      RunMatches rcprI0 r S g tr s e v ids →
      CleanStepsMatch r S g mid outIds (s.next tr) ss evs vs →
      CleanStepsMatch r S g ids outIds tr (s :: ss) (.run e :: evs) (v ++ vs)

private theorem CleanStepsMatch.snoc {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    {s : Step} {e : RunEvent} {v : List VisEntry}
    (hm : CleanStepsMatch r S g ids mid tr ss evs vis)
    (hnext : outIds = nextBundleIds mid e)
    (hrm : RunMatches rcprI0 r S g (runSteps ss tr) s e v mid) :
    CleanStepsMatch r S g ids outIds tr (ss ++ [s]) (evs ++ [.run e]) (vis ++ v) := by
  induction hm with
  | nil =>
    rw [List.nil_append, List.nil_append, List.nil_append, ← List.append_nil v]
    exact CleanStepsMatch.cons hnext hrm (.nil outIds _)
  | cons hmid hrm0 hrest ih =>
    rw [List.cons_append, List.cons_append, List.append_assoc]
    exact CleanStepsMatch.cons hmid hrm0 (ih hnext hrm)

private theorem CleanStepsMatch.toMatchesEventsAt {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ids outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : CleanStepsMatch r S g ids outIds tr ss evs vis) :
    MatchesEventsAt rcprI0 r S g ids tr ss evs vis := by
  induction hm with
  | nil => exact .nil (by simp)
  | cons hmid hrm _ ih =>
    subst hmid
    exact .run1 (pre := []) (by simp) hrm ih

private def cleanInitIds (m : Nat) : Option BundlePreKeyIds :=
  if m = 0 then none else some (none, 7#32, 9#32)

private theorem runMatches_clean_0 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hghost : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)) :
    RunMatches rcprI0 r S (gClean r cls) (setupTrace r) s0Clean (ev 0)
      (stepView s0Clean (setupTrace r) (runWrapped (ev 0))) none := by
  obtain ⟨hp0, hcmd0, hex0, _⟩ := ev0_cmd_and_exit
  obtain ⟨hlen_in, hbyte4, _, hsl46, hsl79, hsl147, hsl1716, _⟩ := ev0_bundle_slices
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  rw [setupTrace_eq_t4 hfit]
  refine ⟨rfl, by rw [hp0]; rfl, by rw [hcmd0]; trivial, hnames.2.symm,
    s0_next_ok.2, ⟨[], hex0⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
      kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB))],
      .bundle, none⟩,
    rngEntry (randTerm 22 32) ::
      (kyberCoinEntries (randTerm 23 32) ++
        [{ rngEntry (randTerm 24 32) with anchor := some 27 }]),
    [], ?_, ?_, drawsMatch_ev0 r S cls, ?_, trivial, fun _ _ => trivial⟩
  · rw [stepView_s0, List.append_nil]
  · refine ⟨by unfold inputKind; rw [hcmd0], ⟨hlen_in, ?_, ?_, ?_, ?_⟩, hbyte4⟩
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.spkPub
      rw [hsl46, gamma_dhPk_spkB hfit]
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.spkSig
      have hg5 := hghost.2.1 r.spkSigTerm (by simp)
      dsimp only [ProtocolSetup.spkSigTerm] at hg5
      rw [hsl79, ← hfit.1.1.2.2.2.2.2.2.2.2.2.1, ← hg5,
          Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]; rfl
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkPub
      have hg6 := hghost.2.1 r.pqpkPubTerm (by simp)
      dsimp only [ProtocolSetup.pqpkPubTerm] at hg6
      rw [hsl147, ← hfit.1.1.2.2.2.2.2.2.2.2.2.2.1, ← hg6,
          Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe]; rfl
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkSig
      have hg7 := hghost.2.1 r.pqpkSigTerm (by simp)
      dsimp only [ProtocolSetup.pqpkSigTerm] at hg7
      rw [hsl1716, ← hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.1, ← hg7,
          Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]; rfl
  · unfold OutputsMatch; rw [hex0, hcmd0]; rfl

private theorem runMatches_clean_1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls)
    (hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) :
    RunMatches rcprI0 r S (gClean r cls) (runTrace r (ssClean cls 1)) (s1Clean cls) (ev 1)
      (stepView (s1Clean cls) (runTrace r (ssClean cls 1)) (runWrapped (ev 1)))
      (some (none, 7#32, 9#32)) := by
  have hrun1 : runTrace r (ssClean cls 1) = t5 := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.1]
  obtain ⟨hp1, hcmd1⟩ := ev1_party_cmd
  rw [hrun1]
  refine ⟨rfl, by rw [hp1]; rfl, by rw [hcmd1]; trivial, trivial,
    (s1_next_ok cls).2, ⟨_, hev1_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [randTerm 31 32], .single, none⟩,
    if cls 0 != 0 then [rngEntry (randTerm 32 (cls 0))] else [],
    [⟨.send, [o1.ek, o1.ct, m0Clean cls], .preKeySend, none⟩],
    by rw [ev1_runWrapped]; exact stepView_s1 cls, ?_,
    drawsMatch_enc r S cls (hv 0 (by decide)) (send_coins_ge_64 (s := 0) (by decide))
      (gClean_sigma_32 r cls (cls 0)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd1], ?_⟩
    simp only [List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
      gClean_sigma_31]
  · unfold OutputsMatch
    rw [hev1_out, hcmd1]
    exact ⟨_, rfl, rfl, none, 7#32, 9#32, rfl, rfl⟩

private theorem runMatches_clean_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hex2 : Explains rcprI0 r S (gClean r cls) (ssClean cls 2)
      (visClean r cls 2) (rcprTrace.take 2)) :
    RunMatches rcprI0 r S (gClean r cls) (runTrace r (ssClean cls 2)) s2Clean (ev 2)
      (stepView s2Clean (runTrace r (ssClean cls 2)) (runWrapped (ev 2)))
      (some (none, 7#32, 9#32)) := by
  have hrun2 : runTrace r (ssClean cls 2) = trClean2 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.1]
  obtain ⟨hp2, hcmd2⟩ := ev2_party_cmd
  obtain ⟨hrep2, hopk2⟩ := cleanPreKeyRep_mem_2 hfit hev1_out
  have hno_recv : (rcprTrace.take 2).all
      Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux.noRecvEvent = true := by
    rw [rcprTrace_take_succ (by decide : 1 < 5), rcprTrace_take_succ (by decide : 0 < 5)]
    change ([.run (ev 0), .run (ev 1)] : List CliEvent).all _ = true
    simp [Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux.noRecvEvent,
      ev0_cmd_and_exit.2.1, ev1_party_cmd.2]
  have hbks_nil : DY.Libsignal.Composed.Refinement.bobDoneBaseKeys
      (runTrace r (ssClean cls 2)) = [] :=
    Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux.bobDoneBaseKeys_eq_nil_of_no_recv
      hfit.1.1.1 hex2 hno_recv
  refine ⟨rfl, by rw [hp2]; rfl, by rw [hcmd2]; trivial, (r_names_of_fit hfit).1.symm,
    by rw [hrun2]; exact (s2_next_ok cls).2, ⟨_, ev2_pt_eq_ev1⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [o1.ek, o1.ct, m0Clean cls], .preKeyRecv, none⟩,
    [rngEntry (randTerm 38 32)],
    [⟨.accept, [pt0Clean], .single, some 40⟩],
    by rw [hrun2]; exact stepView_s2 cls (runWrapped (ev 2)),
    ⟨by unfold inputKind; rw [hcmd2], hrep2.2.2.2.1, hopk2⟩,
    drawsMatch_single32 r S cls ev2_coins_ge_32 (gClean_sigma_38 r cls 32),
    ?_, hrep2, ?_⟩
  · unfold OutputsMatch
    rw [ev2_pt_eq_ev1, hcmd2]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt0Clean rnd
    rw [gamma_rand]
    simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_31]
  · unfold PathFaithfulAt
    intro p _
    dsimp only [s2Clean]
    rw [hbks_nil]
    rintro ⟨_, ⟨⟩, _⟩

private theorem runMatches_clean_3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls)
    (hev3_out : (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    RunMatches rcprI0 r S (gClean r cls) (runTrace r (ssClean cls 3)) (s3Clean cls) (ev 3)
      (stepView (s3Clean cls) (runTrace r (ssClean cls 3)) (runWrapped (ev 3)))
      (some (none, 7#32, 9#32)) := by
  have hrun3 : runTrace r (ssClean cls 3) = trClean3 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.1]
  obtain ⟨hp3, hcmd3⟩ := ev3_party_cmd
  rw [hrun3]
  refine ⟨rfl, by rw [hp3]; rfl, by rw [hcmd3]; trivial, trivial,
    (s3_next_ok cls).2, ⟨_, hev3_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [randTerm 47 32], .single, none⟩,
    if cls 1 != 0 then [rngEntry (randTerm 48 (cls 1))] else [],
    [⟨.send, [m1Clean cls], .whisper, none⟩],
    by rw [ev3_runWrapped]; exact stepView_s3 cls, ?_,
    drawsMatch_enc r S cls (hv 1 (by decide)) (send_coins_ge_64 (s := 1) (by decide))
      (gClean_sigma_48 r cls (cls 1)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd3], ?_⟩
    simp only [List.map_cons, List.map_nil, gamma_randTerm_pos (by decide : 32 ≠ 0),
      gClean_sigma_47]
  · unfold OutputsMatch
    rw [hev3_out, hcmd3]
    exact ⟨_, rfl, rfl, _, rfl, rfl⟩

private theorem runMatches_clean_4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hev3_out : (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    RunMatches rcprI0 r S (gClean r cls) (runTrace r (ssClean cls 4)) s4Clean (ev 4)
      (stepView s4Clean (runTrace r (ssClean cls 4)) (runWrapped (ev 4)))
      (some (none, 7#32, 9#32)) := by
  have hrun4 : runTrace r (ssClean cls 4) = trClean4 cls := by
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.2.1]
  obtain ⟨hp4, hcmd4⟩ := ev4_party_cmd
  have hmem4 := m1Clean_mem_recvRepresentationsOn_4 hfit hev3_out
  have hin4 : (ev 4).input = wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls) := by
    have hcomb := ev3_to_ev4.symm.trans hev3_out
    injection hcomb with hpair
    exact (Prod.mk.inj hpair).2
  refine ⟨rfl, by rw [hp4]; rfl, by rw [hcmd4]; trivial, trivial,
    by rw [hrun4]; exact (s4_next_ok cls).2, ⟨_, ev4_pt_eq_ev3⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [m1Clean cls], .whisper, none⟩,
    [rngEntry (randTerm 54 32)],
    [⟨.accept, [pt1Clean], .single, none⟩],
    by rw [hrun4, ev4_whisper.1]; exact stepView_s4 cls,
    ⟨by unfold inputKind; rw [hcmd4], _, rfl, hin4⟩,
    drawsMatch_single32 r S cls ev4_coins_ge_32 (gClean_sigma_54 r cls 32),
    ?_, ?_, ?_⟩
  · unfold OutputsMatch
    rw [ev4_pt_eq_ev3, hcmd4]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt1Clean rnd
    rw [gamma_rand]
    simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_47]
  · unfold ReadsFaithfully
    rw [hin4]
    simpa [hin4] using hmem4
  · intro p hp_pk
    rw [ev4_whisper.2.1] at hp_pk
    cases hp_pk

/-! ## 4. Main `Explains` & `ModelAcceptsTermAfterAttackerSends` Theorems -/

private theorem cleanStepsMatch_upto {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls)
    (hghost : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)) :
    ∀ k ≤ 5,
      (2 ≤ k → (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
        (ecKey (pubBytes rcprI0 (secretBytes r 0)))
        (gamma rcprI0 S (gClean r cls) o1.ek)
        (gamma rcprI0 S (gClean r cls) o1.ct)
        (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) →
      (4 ≤ k → (ev 3).exit = some (0,
        wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) →
      CleanStepsMatch r S (gClean r cls) none (cleanInitIds k) (setupTrace r)
        (ssClean cls k) (rcprTrace.take k) (visClean r cls k)
  | 0, _, _, _ => .nil none (setupTrace r)
  | j + 1, hle, hm0, hm1 => by
    have hj5 : j < 5 := by omega
    have hm_prev := cleanStepsMatch_upto hfit hv hghost j (by omega)
      (fun h => hm0 (by omega)) (fun h => hm1 (by omega))
    obtain ⟨s, hs, _⟩ := ssClean_succ cls hj5
    rw [ssClean_succ_of_get hj5 hs, rcprTrace_take_succ hj5, visClean_succ hj5 hs]
    match j with
    | 0 =>
      injection hs with hs0; subst hs0
      exact hm_prev.snoc ev0_bundle_slices.2.2.1.symm (runMatches_clean_0 hfit hghost)
    | 1 =>
      injection hs with hs1; subst hs1
      have hids : cleanInitIds 2 = nextBundleIds (cleanInitIds 1) (ev 1) := by
        rw [show cleanInitIds 1 = some (none, 7#32, 9#32) from rfl,
            nextBundleIds_non_init (by decide) (by decide)]; rfl
      exact hm_prev.snoc hids (runMatches_clean_1 hfit hv (hm0 (by omega)))
    | 2 =>
      injection hs with hs2; subst hs2
      have hids : cleanInitIds 3 = nextBundleIds (cleanInitIds 2) (ev 2) := by
        rw [show cleanInitIds 2 = some (none, 7#32, 9#32) from rfl,
            nextBundleIds_non_init (by decide) (by decide)]; rfl
      have hex2 : Explains rcprI0 r S (gClean r cls) (ssClean cls 2)
          (visClean r cls 2) (rcprTrace.take 2) :=
        ⟨hghost, ghostWF_visClean 2 (by decide) hfit hv,
          modelRunWF_ssClean hfit hv 2, hm_prev.toMatchesEventsAt⟩
      exact hm_prev.snoc hids (runMatches_clean_2 hfit (hm0 (by omega)) hex2)
    | 3 =>
      injection hs with hs3; subst hs3
      have hids : cleanInitIds 4 = nextBundleIds (cleanInitIds 3) (ev 3) := by
        rw [show cleanInitIds 3 = some (none, 7#32, 9#32) from rfl,
            nextBundleIds_non_init (by decide) (by decide)]; rfl
      exact hm_prev.snoc hids (runMatches_clean_3 hfit hv (hm1 (by omega)))
    | 4 =>
      injection hs with hs4; subst hs4
      have hids : cleanInitIds 5 = nextBundleIds (cleanInitIds 4) (ev 4) := by
        rw [show cleanInitIds 4 = some (none, 7#32, 9#32) from rfl,
            nextBundleIds_non_init (by decide) (by decide)]; rfl
      exact hm_prev.snoc hids (runMatches_clean_4 hfit (hm1 (by omega)))
    | n + 5 => omega

theorem explains_ssClean_le5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {k : Nat} (hk : k ≤ 5)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (hv : ValidCoinLens cls)
    (hghost : GhostAndSemMatchSetup rcprI0 r S (gClean r cls))
    (hm0 : 2 ≤ k → (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek) (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hm1 : 4 ≤ k → (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    Explains rcprI0 r S (gClean r cls) (ssClean cls k) (visClean r cls k)
      (rcprTrace.take k) :=
  ⟨hghost, ghostWF_visClean k hk hfit hv, modelRunWF_ssClean hfit hv k,
    (cleanStepsMatch_upto hfit hv hghost k hk hm0 hm1).toMatchesEventsAt⟩

theorem explains_ssClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {k : Nat} (hk : k ≤ 4)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (hv : ValidCoinLens cls)
    (hghost : GhostAndSemMatchSetup rcprI0 r S (gClean r cls))
    (hm0 : 2 ≤ k → (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek) (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hm1 : 4 ≤ k → (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    Explains rcprI0 r S (gClean r cls) (ssClean cls k) (visClean r cls k)
      (rcprTrace.take k) :=
  explains_ssClean_le5 (Nat.le_succ_of_le hk) hfit hv hghost hm0 hm1

theorem accepts_ssClean_4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (hv : ValidCoinLens cls)
    (hghost : GhostAndSemMatchSetup rcprI0 r S (gClean r cls))
    (hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek) (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hev3_out : (ev 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    ModelAcceptsTermAfterAttackerSends rcprI0 r S (gClean r cls)
      (ssClean cls 4) (rcprTrace.take 4) (ev 4) (m1Clean cls) := by
  refine ⟨[], s4Clean, 53, gClean r cls, visClean r cls 5,
    by simp, rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
  · rw [List.map_nil, List.append_nil]; unfold runTrace
    rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.2.1]; exact trClean4_sent_53 cls
  · rw [List.map_nil, List.append_nil,
        ← ssClean_succ_of_get (by decide : 4 < 5) (s := s4Clean) rfl,
        ← rcprTrace_take_succ (by decide : 4 < 5)]
    exact explains_ssClean_le5 (Nat.le_refl 5) hfit hv hghost
      (fun _ => hev1_out) (fun _ => hev3_out)

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision
