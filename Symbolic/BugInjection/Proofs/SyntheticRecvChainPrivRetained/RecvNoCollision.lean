/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.MemoCheck
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.CleanExplains
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Receive Collision Absence on All `.recv` Events of `RecvChainPrivRetainedCli`

Proves `not_nextEventCollides_recv` across all splits `rcprTrace = evs₁ ++ .run ev :: evs₂` with
`ev.cmd = .recv peer`:
- Indices `0`, `1`, `3` contradict `ev.cmd = .recv peer`, indices `5`, `6` are `.env (.leak ...)`,
  and index `7` (`rcprStopEv`) has `exit = some (1, [])`, discharged by `nextEventCollides_AutoFalse`.
- Index `2` (Bob PreKey `.recv`) and index `4` (Alice Whisper `.recv`): combines clean-prefix
  extraction (`Calls0to4Prefix.extract_clean_prefix`), clean prefix explanation
  (`CleanExplains.explains_ssClean`), `CleanStepView.not_readCollisionCli_ssClean_le4`, and the
  trial-free memoization checks (`MemoCheck.not_bobStartCollides_of_pinned`,
  `MemoCheck.not_reselectCollisionOn_of_pinned`, `MemoCheck.not_recvCollisionOn_of_pinned`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag kyberEncapsSymbol)
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds PreKeyFields
   GhostAndSemMatchSetup GhostWF MatchesEvents MatchesEventsAt RunMatches
   BytesMatchEntry DrawsMatch OutputsMatch ReadsFaithfully PathFaithfulAt
   Explains preKeyWire parsePreKeyWire parsePreKey decodePreKey ecKey kyberKey pubBytes secretBytes
   setupTrace runTrace runSteps stepView rngEntry randTerm gamma runWrapped inputKind
   preKeyRepresentationsOn recvRepresentationsOn PreKeyRecvMatches OpkNamed
   honestSaltsOf getMessageSentAt_attackerKnows)
open DY.Libsignal.Composed.Refinement.Cli
  (NextEventCollides ModelAcceptsTermAfterAttackerSends)
open Symbolic.BugInjection (hexBytes)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (pqskB t4_length o1 stA0 dhsA)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
  (noRecvEvent not_knownBaseKeyOn_of_no_recv)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (nextEventCollides_AutoFalse not_preKeyStartCollidesOrRejects_of_clean
   not_nextEventCollides_accepted_prekey not_nextEventCollides_accepted_whisper)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprLeakKey1 rcprSpqrState1 rcprStopEv rcprTrace
   rcprI0 rcprHooks0 rcprCompFitsPinned rcprPubOfIdx rcprPubOfIdx_length)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws (rcprI0_kyberEncaps)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (hexDigit hexBytes_ofList cliTrace rcprTrace_take5
   ev0Coins_eq ev0KyberEnt ev0KyberEnt_eq ev0_coins_facts ev0_cmd_and_exit
   ev1_party_cmd ev1_to_ev2 ev3_party_cmd ev3_to_ev4 ev4_pt_eq_ev3 ev2_party_cmd ev4_party_cmd
   ev2Coins_eq ev2_has_preKey ev2_full_fields ev2_input_len_lt_2pow63
   not_kyberMismatch_ev2 ev4_whisper ev4_coins_ge_32
   ValidCoinLens cleanCallSteps ssClean ssClean_succ s4Clean s4_next_ok
   runSteps_ssClean modelRunWF_ssClean setupTrace_eq_t4
   pt0Clean coins0Clean key0Clean m0Clean trClean2 dhsB1Clean stB2Clean
   pt1Clean coins1Clean key1Clean m1Clean trClean4
   pqAddrBytes gClean gClean_sigma_lt22 gClean_sigma_22 gClean_sigma_23 gClean_sigma_24
   gClean_sigma_31 gClean_sigma_32 gClean_sigma_38 gClean_sigma_47 gClean_sigma_48 gClean_sigma_54
   gClean_addr_m0 gClean_addr_m1 setupRandomsAt_of_fit
   gamma_kemPk_pqskB_gClean gamma_dhPk_ek gamma_dhPk_dhsA gamma_dhPk_dhsB1
   extract_clean_prefix)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
  (dagBytes dhsB1Id aliceBobAddrBytes sendPtTs sendPtBytes sendC32Id sendC64Id sendWmacId)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
  (SetupAndCall0Pinned r_secret3_eq r_secret4_eq r_secret5_eq)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.SendTrials
  (PrefixPinned cleanSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.MemoCheck
  (not_bobStartCollides_of_pinned not_reselectCollisionOn_of_pinned not_recvCollisionOn_of_pinned)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
  (gamma_randTerm_ne_zero encMsg_mem_recvRepresentationsOn encMsg_faithfulInner)

private abbrev traceEv := Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.ev

/-! ## 1. Fast Hex Evaluations for Calls 1–4 -/

section FastHex
attribute [local irreducible] Symbolic.BugInjection.hexBytes

private def ev1InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 1).input)
private theorem ev1In_eq : (traceEv 1).input = ev1InFast := by
  rw [show (traceEv 1).input = hexBytes (nfe_str_of_hex (traceEv 1).input) from rfl,
      show (nfe_str_of_hex (traceEv 1).input) = String.ofList (nfe_chars_of_hex (traceEv 1).input) from rfl,
      hexBytes_ofList]; rfl

private def ev1CoinsFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 1).coins)
private theorem ev1Coins_eq : (traceEv 1).coins = ev1CoinsFast := by
  rw [show (traceEv 1).coins = hexBytes (nfe_str_of_hex (traceEv 1).coins) from rfl,
      show (nfe_str_of_hex (traceEv 1).coins) = String.ofList (nfe_chars_of_hex (traceEv 1).coins) from rfl,
      hexBytes_ofList]; rfl

private def ev2InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 2).input)
private theorem ev2In_eq : (traceEv 2).input = ev2InFast := by
  rw [show (traceEv 2).input = hexBytes (nfe_str_of_hex (traceEv 2).input) from rfl,
      show (nfe_str_of_hex (traceEv 2).input) = String.ofList (nfe_chars_of_hex (traceEv 2).input) from rfl,
      hexBytes_ofList]; rfl

private def ev3InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 3).input)
private theorem ev3In_eq : (traceEv 3).input = ev3InFast := by
  rw [show (traceEv 3).input = hexBytes (nfe_str_of_hex (traceEv 3).input) from rfl,
      show (nfe_str_of_hex (traceEv 3).input) = String.ofList (nfe_chars_of_hex (traceEv 3).input) from rfl,
      hexBytes_ofList]; rfl

private def ev3CoinsFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 3).coins)
private theorem ev3Coins_eq : (traceEv 3).coins = ev3CoinsFast := by
  rw [show (traceEv 3).coins = hexBytes (nfe_str_of_hex (traceEv 3).coins) from rfl,
      show (nfe_str_of_hex (traceEv 3).coins) = String.ofList (nfe_chars_of_hex (traceEv 3).coins) from rfl,
      hexBytes_ofList]; rfl

private def ev4InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (traceEv 4).input)
private theorem ev4In_eq : (traceEv 4).input = ev4InFast := by
  rw [show (traceEv 4).input = hexBytes (nfe_str_of_hex (traceEv 4).input) from rfl,
      show (nfe_str_of_hex (traceEv 4).input) = String.ofList (nfe_chars_of_hex (traceEv 4).input) from rfl,
      hexBytes_ofList]; rfl

end FastHex

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.ev

private theorem ev2_msg_eq_dagBytes {p : PreKeyFields}
    (hp : parsePreKeyWire (traceEv 2).input = some p) :
    p.message = dagBytes (sendWmacId 0) := by
  have hc : (parsePreKeyWire ev2InFast).map (·.message) = some (dagBytes (sendWmacId 0)) := by
    decide +kernel
  rw [← ev2In_eq, hp, Option.map_some] at hc
  exact Option.some.inj hc

private theorem ev4_drop1_eq_dagBytes :
    (traceEv 4).input.drop 1 = dagBytes (sendWmacId 1) := by
  rw [ev4In_eq]
  decide +kernel

private theorem parsePreKeyWire_cons_and_tryFrom {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    (∃ body, b = wirePrekeyTag :: body) ∧
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at hp
  cases b with
  | nil => cases hp
  | cons tag body =>
    dsimp only at hp
    split at hp
    · next htag =>
      subst htag
      refine ⟨⟨body, rfl⟩, ?_⟩
      unfold parsePreKey at hp
      cases body with
      | nil => cases hp
      | cons vb rest =>
        dsimp only at hp
        split at hp
        · cases hp
        · cases hdec : decodePreKey rest with
          | none => rw [hdec] at hp; cases hp
          | some m =>
            rw [hdec] at hp
            dsimp only at hp
            rcases h1 : m.baseKey with _ | bk <;> rcases h2 : m.identityKey with _ | ik <;>
              rcases h3 : m.message with _ | msg <;> rcases h4 : m.signedPreKeyId with _ | sid <;>
              simp [h1, h2, h3, h4] at hp
            rcases hp with ⟨_, hp⟩
            cases htr : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
            | error _ => rw [htr] at hp; cases hp
            | ok inner => rw [htr] at hp; injection hp with hp'; subst hp'; exact htr
    · cases hp

/-! ## 2. `SetupAndCall0Pinned` and `PrefixPinned` on `(gClean r cls, visClean r cls _)` -/

private theorem setupAndCall0Pinned_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g) :
    SetupAndCall0Pinned S (gClean r cls) := by
  have hrandAt := setupRandomsAt_of_fit hfit
  have hs0 : secretBytes r 0 = r.fresh 0 32 := by unfold secretBytes; rw [hrandAt]; rfl
  have hs1 : secretBytes r 1 = r.fresh 5 32 := by unfold secretBytes; rw [hrandAt]; rfl
  have hs2 : secretBytes r 2 = r.fresh 10 32 := by unfold secretBytes; rw [hrandAt]; rfl
  have hs3 : secretBytes r 3 = r.fresh 11 64 := by unfold secretBytes; rw [hrandAt]; rfl
  have hs4 : secretBytes r 4 = r.fresh 16 64 := by unfold secretBytes; rw [hrandAt]; rfl
  have hs5 : secretBytes r 5 = r.fresh 17 64 := by unfold secretBytes; rw [hrandAt]; rfl
  have hpqpk : gamma rcprI0 S (gClean r cls) (kemPk pqskB) = rcprSetup.kyberPk :=
    gamma_kemPk_pqskB_gClean cls hfit hCompat
  have hek_def : o1.ek = dhPk (rnd 22 32) := by
    dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t4_length]; rfl
  have hct_def : o1.ct = (kemEncap (kemPk pqskB) (rnd 23 32)).1 := by
    dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t4_length]; rfl
  refine
    { sig0 := ?_, sig5 := ?_, sig10 := ?_, sig11 := ?_, sig16 := ?_, sig17 := ?_,
      sig22 := ?_, sig23 := ?_, sig24 := ?_, pqpk := ?_, ek0 := ?_, ct0 := ?_ }
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs0, hfit.1.1.2.2.2.2.2.2.1]; decide +kernel
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs1, hfit.1.1.2.2.2.2.2.2.2.1]; decide +kernel
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs2, hfit.1.1.2.2.2.2.2.2.2.2.1]; decide +kernel
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs3, r_secret3_eq hfit]; decide +kernel
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs4, r_secret4_eq hfit]; decide +kernel
  · rw [gClean_sigma_lt22 r cls (by decide), ← hs5, r_secret5_eq hfit]; decide +kernel
  · rw [gClean_sigma_22, ev0Coins_eq]; decide +kernel
  · rw [gClean_sigma_23, ev0KyberEnt_eq]; decide +kernel
  · rw [gClean_sigma_24, ev0Coins_eq]; decide +kernel
  · change gamma rcprI0 S (gClean r cls) (kemPk pqskB) = dagBytes 71
    rw [hpqpk]; decide +kernel
  · rw [hek_def, gamma_dhPk_ek r S cls]; decide +kernel
  · rw [hct_def, Symbolic.Swarm.CREF.TR.gamma_kemEncap_fst]
    have hr23 : gamma rcprI0 S (gClean r cls) (rnd 23 32) = ev0KyberEnt := by
      exact (gamma_randTerm_ne_zero rcprI0 S (gClean r cls) (by decide : 32 ≠ 0)).trans
        (gClean_sigma_23 r cls 32)
    rw [hr23]
    simp only [ev0_coins_facts.2.2.2.1, ↓reduceIte, rcprI0_kyberEncaps, Option.getD_some]
    exact ev0_coins_facts.2.2.2.2.1.trans (by decide +kernel)

private theorem m0Clean_gamma_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {p : PreKeyFields}
    (hp : parsePreKeyWire (traceEv 2).input = some p)
    (hm0 : (traceEv 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) :
    gamma rcprI0 S (gClean r cls) (m0Clean cls) = p.message := by
  have hb : (traceEv 2).input = preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)) := by
    have h12 := ev1_to_ev2.symm.trans hm0
    injection h12 with hpair
    exact (Prod.mk.inj hpair).2
  exact (parsePreKeyWire_preKeyWire_inv hb ev2_input_len_lt_2pow63 hp).2.2.2.symm

private theorem m1Clean_gamma_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hm1 : (traceEv 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    (traceEv 4).input = wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls) := by
  have h34 := ev3_to_ev4.symm.trans hm1
  injection h34 with hpair
  exact (Prod.mk.inj hpair).2

private theorem prefixPinned_gClean_1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cls : Nat → Nat} {p : PreKeyFields}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hp : parsePreKeyWire (traceEv 2).input = some p)
    (hm0 : (traceEv 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) :
    PrefixPinned cls S (gClean r cls) (visClean r cls 2) 1 := by
  obtain ⟨hv_pts, hv_sends⟩ := visClean_2_terms cls hfit
  refine
    { base := setupAndCall0Pinned_gClean cls hfit hCompat
      dhsB1 := fun h => by cases h
      send_pt := ?_
      send_c32 := ?_
      send_c64 := ?_
      send_msg := ?_
      send_addr := ?_
      vis_pts := hv_pts
      vis_sends := ?_ }
  · intro j hj; obtain rfl : j = 0 := by omega
    change (gClean r cls).σ 31 32 = sendPtBytes 0
    rw [gClean_sigma_31, ev1In_eq]; decide +kernel
  · intro j hj _; obtain rfl : j = 0 := by omega
    change (gClean r cls).σ 32 32 = dagBytes (sendC32Id 0)
    rw [gClean_sigma_32, ev1Coins_eq]; decide +kernel
  · intro j hj _; obtain rfl : j = 0 := by omega
    change (gClean r cls).σ 32 64 = dagBytes (sendC64Id 0)
    rw [gClean_sigma_32, ev1Coins_eq]; decide +kernel
  · intro j hj; obtain rfl : j = 0 := by omega
    change gamma rcprI0 S (gClean r cls) (m0Clean cls) = dagBytes (sendWmacId 0)
    exact (m0Clean_gamma_eq hp hm0).trans (ev2_msg_eq_dagBytes hp)
  · intro j hj msg hparse; obtain rfl : j = 0 := by omega
    rw [show cleanSendMsg cls 0 = m0Clean cls from rfl, m0Clean,
        parse_encMsg stA0 (coins0Clean cls) (key0Clean cls) pt0Clean] at hparse
    injection hparse with hmsg; subst hmsg
    simp only [↓reduceIte]
    exact (gClean_addr_m0 r cls).trans (by decide +kernel : pqAddrBytes = aliceBobAddrBytes)
  · intro t ht
    rw [hv_sends] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, by decide, rfl⟩)

private theorem prefixPinned_gClean_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cls : Nat → Nat} {p : PreKeyFields}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hp : parsePreKeyWire (traceEv 2).input = some p)
    (hm0 : (traceEv 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hm1 : (traceEv 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    PrefixPinned cls S (gClean r cls) (visClean r cls 4) 2 := by
  obtain ⟨hv_pts, hv_sends⟩ := visClean_4_terms cls hfit
  refine
    { base := setupAndCall0Pinned_gClean cls hfit hCompat
      dhsB1 := fun _ => by rw [gClean_sigma_38, ev2Coins_eq]; decide +kernel
      send_pt := ?_
      send_c32 := ?_
      send_c64 := ?_
      send_msg := ?_
      send_addr := ?_
      vis_pts := hv_pts
      vis_sends := ?_ }
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · change (gClean r cls).σ 31 32 = sendPtBytes 0
      rw [gClean_sigma_31, ev1In_eq]; decide +kernel
    · change (gClean r cls).σ 47 32 = sendPtBytes 1
      rw [gClean_sigma_47, ev3In_eq]; decide +kernel
  · intro j hj _
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · change (gClean r cls).σ 32 32 = dagBytes (sendC32Id 0)
      rw [gClean_sigma_32, ev1Coins_eq]; decide +kernel
    · change (gClean r cls).σ 48 32 = dagBytes (sendC32Id 1)
      rw [gClean_sigma_48, ev3Coins_eq]; decide +kernel
  · intro j hj _
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · change (gClean r cls).σ 32 64 = dagBytes (sendC64Id 0)
      rw [gClean_sigma_32, ev1Coins_eq]; decide +kernel
    · change (gClean r cls).σ 48 64 = dagBytes (sendC64Id 1)
      rw [gClean_sigma_48, ev3Coins_eq]; decide +kernel
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · change gamma rcprI0 S (gClean r cls) (m0Clean cls) = dagBytes (sendWmacId 0)
      exact (m0Clean_gamma_eq hp hm0).trans (ev2_msg_eq_dagBytes hp)
    · change gamma rcprI0 S (gClean r cls) (m1Clean cls) = dagBytes (sendWmacId 1)
      have he4 := m1Clean_gamma_eq hm1
      have hd : (traceEv 4).input.drop 1 = gamma rcprI0 S (gClean r cls) (m1Clean cls) := by
        rw [he4]; rfl
      exact hd.symm.trans ev4_drop1_eq_dagBytes
  · intro j hj msg hparse
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [show cleanSendMsg cls 0 = m0Clean cls from rfl, m0Clean,
          parse_encMsg stA0 (coins0Clean cls) (key0Clean cls) pt0Clean] at hparse
      injection hparse with hmsg; subst hmsg
      simp only [↓reduceIte]
      exact (gClean_addr_m0 r cls).trans (by decide +kernel : pqAddrBytes = aliceBobAddrBytes)
    · rw [show cleanSendMsg cls 1 = m1Clean cls from rfl, m1Clean,
          parse_encMsg (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean] at hparse
      injection hparse with hmsg; subst hmsg
      simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
      exact gClean_addr_m1 r cls
  · intro t ht
    rw [hv_sends] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, by decide, rfl⟩)
    · exact Or.inr (Or.inr ⟨1, by decide, rfl⟩)

/-! ## 3. Call 2 (`bobStart`) Representation & Non-Collision -/

private theorem preKeyRep_ev2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cls : Nat → Nat} {p : PreKeyFields}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hp : parsePreKeyWire (traceEv 2).input = some p)
    (hm0 : (traceEv 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) :
    ⟨o1.ek, o1.ct, m0Clean cls⟩ ∈
      preKeyRepresentationsOn rcprI0 r S (gClean r cls) (runTrace r (ssClean cls 2)) (traceEv 2).input := by
  have htr2 : runTrace r (ssClean cls 2) = trClean2 cls := by
    unfold runTrace
    rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.1]
  rw [htr2]
  obtain ⟨hek_sent, hct_sent, hmsg_sent⟩ := trClean2_sent_eqs cls
  have hak_ek := getMessageSentAt_attackerKnows hek_sent
  have hak_ct := getMessageSentAt_attackerKnows hct_sent
  have hak_msg := getMessageSentAt_attackerKnows hmsg_sent
  have hb : (traceEv 2).input = preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls)) := by
    have h12 := ev1_to_ev2.symm.trans hm0
    injection h12 with hpair
    exact (Prod.mk.inj hpair).2
  obtain ⟨hpId, hpCt, hpBk, hpMsg⟩ :=
    parsePreKeyWire_preKeyWire_inv hb ev2_input_len_lt_2pow63 hp
  have hff := ev2_full_fields hp
  have hbase := setupAndCall0Pinned_gClean cls hfit hCompat
  have hek_len : (gamma rcprI0 S (gClean r cls) o1.ek).length = 32 := by
    rw [hbase.ek0]; decide +kernel
  have hbk_take : p.baseKey.take 33 = ecKey (gamma rcprI0 S (gClean r cls) o1.ek) := by
    rw [hpBk]
    exact List.take_of_length_le (by simp [ecKey, hek_len])
  have hik_take : p.identityKey.take 33 = ecKey (pubBytes rcprI0 (secretBytes r 0)) := by
    have hik_eq : p.identityKey = ecKey (pubBytes rcprI0 (secretBytes r 0)) := by
      have hs0 := hfit.1.1.2.2.2.2.2.2.1
      rw [hff.2.2.2.2.2.2.1, hs0]
      decide +kernel
    rw [hik_eq]
    refine List.take_of_length_le ?_
    have hl : (pubBytes rcprI0 (secretBytes r 0)).length = 32 :=
      hfit.2.1.1.x25519_public_key_length _
    simp [ecKey, hl]
  have hr_spkId : r.spkId = 7 := hfit.1.1.2.2.2.2.1
  have hr_kpkId : r.kpkId = 9 := hfit.1.1.2.2.2.2.2.1
  have hrk_len : (gamma rcprI0 S (gClean r cls) (dhPk stA0.dhs)).length = 32 := by
    change (gamma rcprI0 S (gClean r cls) (dhPk dhsA)).length = 32
    rw [gamma_dhPk_dhsA hfit]
    exact rcprPubOfIdx_length _
  have htry := (parsePreKeyWire_cons_and_tryFrom hp).2
  have hfi := encMsg_faithfulInner hpMsg.symm hrk_len htry
  refine ⟨hak_ek, hak_ct, hak_msg, ?_, p, hp, hfi⟩
  refine ⟨p, hp, hbk_take, hpCt, hpMsg, ?_, ?_, ?_, hik_take, false, p, hp, hpId⟩
  · have hc : (parsePreKeyWire ev2InFast).map (·.version) = some 4 := by decide +kernel
    rw [← ev2In_eq, hp, Option.map_some] at hc
    exact Option.some.inj hc
  · rw [hff.2.1, hr_spkId]
  · rw [hff.2.2.2.1, hr_kpkId]

private theorem not_nextEventCollides_ev2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 2)) :
    ¬ NextEventCollides rcprI0 r S g ss vis (rcprTrace.take 2) (traceEv 2) := by
  obtain ⟨p2, hp2⟩ := ev2_has_preKey
  obtain ⟨⟨body2, hin2⟩, _⟩ := parsePreKeyWire_cons_and_tryFrom hp2
  obtain ⟨cls, hv, hghost, hm0_fn, _⟩ := extract_clean_prefix hfit (by decide) hex
  have hm0 := hm0_fn (by decide)
  have hex_clean := explains_ssClean (k := 2) (by decide) hfit hv hghost
    (fun _ => hm0) (fun h => by omega)
  have hp2_wire : parsePreKeyWire (wirePrekeyTag :: body2) = some p2 := hin2 ▸ hp2
  have hNotKnown : ¬ DY.Libsignal.Composed.Refinement.KnownBaseKeyOn rcprI0 S g
      (runTrace r ss) p2 :=
    not_knownBaseKeyOn_of_no_recv hfit.1.1.1 hex
      (by decide +kernel : (rcprTrace.take 2).all noRecvEvent = true)
  have hNoRead := not_readCollisionCli_ssClean_le4 rcprI0 r S (gClean r cls) cls
    (k := 2) (by decide) (rcprTrace.take 2)
  have hrep2 : ⟨o1.ek, o1.ct, m0Clean cls⟩ ∈
      preKeyRepresentationsOn rcprI0 r S (gClean r cls)
        (runTrace r (ssClean cls 2)) (wirePrekeyTag :: body2) :=
    hin2 ▸ preKeyRep_ev2 hfit hex.1 hp2 hm0
  have hpinned1 := prefixPinned_gClean_1 hfit hex.1 hp2 hm0
  have hNoBob := not_bobStartCollides_of_pinned r S (gClean r cls) (visClean r cls 2)
    cls p2 hfit hv hpinned1 (ev2_full_fields hp2).2.2.1
  exact not_nextEventCollides_accepted_prekey ev2_party_cmd.2 hin2 hp2_wire hNotKnown
    (not_preKeyStartCollidesOrRejects_of_clean (not_kyberMismatch_ev2 hfit hp2)
      hex_clean hNoRead hrep2 hNoBob)

/-! ## 4. Call 4 (`messageDecrypt`) 1-Step Clean Extension & Non-Collision -/

private theorem runSteps_append :
    ∀ (xs ys : List Step) (tr : ExecTrace),
      runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr)
  | [], _ys, _tr => rfl
  | s :: xs, ys, tr => runSteps_append xs ys (s.next tr)

private theorem matchesEventsAt_snoc_anyIds {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    {s : Step} {e : RunEvent} {v : List VisEntry}
    (hm : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hrm : ∀ ids, RunMatches interp r S g (runSteps ss tr) s e v ids) :
    MatchesEventsAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.run e]) (vis ++ v) := by
  induction hm with
  | @nil ids₀ tr₀ ss₀ hinv =>
    rw [List.nil_append, List.nil_append, ← List.append_nil v]
    exact .run1 hinv (hrm ids₀) (.nil (by simp))
  | @run1 ids₀ tr₀ pre s₀ ss₀ ev₀ evs₀ v₀ vs₀ hinv hrm₀ _ ih =>
    have hassoc_s : (pre ++ s₀ :: ss₀) ++ [s] = pre ++ s₀ :: (ss₀ ++ [s]) := by
      simp [List.append_assoc]
    have hassoc_v : (v₀ ++ vs₀) ++ v = v₀ ++ (vs₀ ++ v) := List.append_assoc v₀ vs₀ v
    have hrs : runSteps ss₀ (s₀.next (runSteps pre tr₀)) = runSteps (pre ++ s₀ :: ss₀) tr₀ := by
      rw [runSteps_append]; rfl
    rw [hassoc_s, List.cons_append, hassoc_v]
    exact .run1 hinv hrm₀ (ih (hrs ▸ hrm))
  | @run0 ids₀ tr₀ pre ss₀ ev₀ evs₀ vs₀ hinv hrej _ ih =>
    have hassoc_s : (pre ++ ss₀) ++ [s] = pre ++ (ss₀ ++ [s]) := List.append_assoc pre ss₀ [s]
    have hrs : runSteps ss₀ (runSteps pre tr₀) = runSteps (pre ++ ss₀) tr₀ :=
      (runSteps_append pre ss₀ tr₀).symm
    rw [hassoc_s, List.cons_append]
    exact .run0 hinv hrej (ih (hrs ▸ hrm))
  | @env ids₀ tr₀ pre s₀ ss₀ ev₀ evs₀ v₀ vs₀ hinv henv _ ih =>
    have hassoc_s : (pre ++ s₀ :: ss₀) ++ [s] = pre ++ s₀ :: (ss₀ ++ [s]) := by
      simp [List.append_assoc]
    have hassoc_v : (v₀ ++ vs₀) ++ v = v₀ ++ (vs₀ ++ v) := List.append_assoc v₀ vs₀ v
    have hrs : runSteps ss₀ (s₀.next (runSteps pre tr₀)) = runSteps (pre ++ s₀ :: ss₀) tr₀ := by
      rw [runSteps_append]; rfl
    rw [hassoc_s, List.cons_append, hassoc_v]
    exact .env hinv henv (ih (hrs ▸ hrm))

private theorem randTerm_inj {ts₁ n₁ ts₂ n₂ : Nat}
    (h : randTerm ts₁ n₁ = randTerm ts₂ n₂) : ts₁ = ts₂ ∧ n₁ = n₂ := by
  have hp := Symbolic.DYBridge.DY.BytesView.pack_inj.mp
    (h : (({ timestamp := ts₁, size := n₁ } : DY.Random.Random Bytes).pack) =
         (({ timestamp := ts₂, size := n₂ } : DY.Random.Random Bytes).pack))
  exact ⟨congrArg DY.Random.Random.timestamp hp, congrArg DY.Random.Random.size hp⟩

private theorem recvRep_ev4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {body4 : HwBytes}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hin4 : (traceEv 4).input = wireWhisperTag :: body4)
    (hm1 : (traceEv 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) :
    m1Clean cls ∈
      recvRepresentationsOn rcprI0 S (gClean r cls) (runTrace r (ssClean cls 4)) body4 := by
  have htr4 : runTrace r (ssClean cls 4) = trClean4 cls := by
    unfold runTrace
    rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.2.1]
  rw [htr4]
  have hak := getMessageSentAt_attackerKnows (trClean4_sent_53 cls)
  have hbody : gamma rcprI0 S (gClean r cls) (m1Clean cls) = body4 := by
    have he4 := hin4.symm.trans (m1Clean_gamma_eq hm1)
    exact (List.cons.inj he4).2.symm
  have hrk_len : (gamma rcprI0 S (gClean r cls) (dhPk (stB2Clean cls).dhs)).length = 32 := by
    change (gamma rcprI0 S (gClean r cls) (dhPk dhsB1Clean)).length = 32
    rw [gamma_dhPk_dhsB1 hfit]
    exact rcprPubOfIdx_length _
  exact encMsg_mem_recvRepresentationsOn hak hbody hrk_len

private theorem modelAccepts_ev4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {body4 : HwBytes}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls)
    (hin4 : (traceEv 4).input = wireWhisperTag :: body4)
    (hm1 : (traceEv 3).exit = some (0,
      wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls)))
    (hex4 : Explains rcprI0 r S (gClean r cls) (ssClean cls 4) (visClean r cls 4)
      (rcprTrace.take 4))
    (ht4 : m1Clean cls ∈
      recvRepresentationsOn rcprI0 S (gClean r cls) (runTrace r (ssClean cls 4)) body4) :
    ModelAcceptsTermAfterAttackerSends rcprI0 r S (gClean r cls) (ssClean cls 4)
      (rcprTrace.take 4) (traceEv 4) (m1Clean cls) := by
  have htr4 : runTrace r (ssClean cls 4) = trClean4 cls := by
    unfold runTrace
    rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.2.1]
  have hss5 : ssClean cls 4 ++ [s4Clean] = ssClean cls 5 := by
    obtain ⟨s, hs, heq⟩ := ssClean_succ cls (by decide : 4 < 5)
    have hs4 : (cleanCallSteps cls)[4]? = some s4Clean := rfl
    rw [hs4] at hs; injection hs with hs; subst hs; exact heq.symm
  have hvis5 : visClean r cls 5 = visClean r cls 4 ++ stepView s4Clean (trClean4 cls) false := by
    rw [visClean_succ (by decide : 4 < 5) (s := s4Clean) rfl, htr4, ev4_whisper.1]
  refine ⟨[], s4Clean, 53, gClean r cls, visClean r cls 5, by simp, rfl, rfl,
    fun _ _ => rfl, ?_, ?_⟩
  · simp only [List.map_nil, List.append_nil, htr4]
    exact trClean4_sent_53 cls
  · simp only [List.map_nil, List.append_nil, hss5]
    refine ⟨hex4.1, ?_, modelRunWF_ssClean hfit hv 5, ?_⟩
    · obtain ⟨hg1, hg2, hg3⟩ := hex4.2.1
      rw [hvis5, stepView_s4 cls]
      refine ⟨?_, hg2, ?_⟩
      · intro v hv_mem hkind ts n hn hterm
        rcases List.mem_append.mp hv_mem with hv4 | hv_new
        · exact hg1 v hv4 hkind ts n hn hterm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_new
          rcases hv_new with rfl | rfl | rfl
          · cases hkind
          · simp only [rngEntry, List.mem_singleton] at hterm
            obtain ⟨rfl, rfl⟩ := randTerm_inj hterm
            rw [gClean_sigma_54]
            exact List.length_take_of_le ev4_coins_ge_32
          · cases hkind
      · intro v hv_mem hsend
        rcases List.mem_append.mp hv_mem with hv4 | hv_new
        · exact hg3 v hv4 hsend
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_new
          rcases hv_new with rfl | rfl | rfl <;> simp [rngEntry] at hsend
    · rw [hvis5, ← hss5]
      refine matchesEventsAt_snoc_anyIds hex4.2.2.2 fun ids => ?_
      have hrs4 : runSteps (ssClean cls 4) (setupTrace r) = trClean4 cls := htr4
      rw [hrs4]
      refine ⟨rfl, ?_, ?_, trivial, (s4_next_ok cls).2, ⟨(traceEv 3).input, ev4_pt_eq_ev3⟩, ?_, ?_⟩
      · rw [ev4_party_cmd.1]; rfl
      · rw [ev4_party_cmd.2]; trivial
      · rw [ev4_whisper.1]
      · refine ⟨⟨.recv, [m1Clean cls], .whisper, none⟩,
          [rngEntry (randTerm 54 32)],
          [⟨.accept, [pt1Clean], .single, none⟩],
          stepView_s4 cls, ?_, ?_, ?_, ?_, ?_⟩
        · have hik : inputKind (traceEv 4) = .recv := by unfold inputKind; rw [ev4_party_cmd.2]
          rw [hik]
          exact ⟨rfl, m1Clean cls, rfl, m1Clean_gamma_eq hm1⟩
        · refine ⟨[(traceEv 4).coins.take 32], ?_, ?_, ?_⟩
          · intro p hp
            rw [List.mem_singleton] at hp; subst hp
            have hlen : ((traceEv 4).coins.take 32).length = 32 :=
              List.length_take_of_le ev4_coins_ge_32
            intro hnil; rw [hnil] at hlen; cases hlen
          · simpa using List.take_prefix 32 (traceEv 4).coins
          · refine List.Forall₂.cons ?_ List.Forall₂.nil
            refine ⟨rfl, ?_⟩
            dsimp only [rngEntry, List.map]
            rw [gamma_randTerm_ne_zero rcprI0 S (gClean r cls) (by decide : 32 ≠ 0),
                gClean_sigma_54]
        · unfold OutputsMatch
          rw [ev4_pt_eq_ev3, ev4_party_cmd.2]
          refine ⟨⟨.accept, [pt1Clean], .single, none⟩, rfl, rfl, ?_⟩
          dsimp only [List.map]
          change [gamma rcprI0 S (gClean r cls) (randTerm 47 32)] = [(traceEv 3).input]
          rw [gamma_randTerm_ne_zero rcprI0 S (gClean r cls) (by decide : 32 ≠ 0),
              gClean_sigma_47]
        · unfold ReadsFaithfully
          rw [hin4, ← htr4]
          exact ht4
        · intro p hp
          rw [ev4_whisper.2.1] at hp
          cases hp

private theorem not_nextEventCollides_ev4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 4)) :
    ¬ NextEventCollides rcprI0 r S g ss vis (rcprTrace.take 4) (traceEv 4) := by
  obtain ⟨p2, hp2⟩ := ev2_has_preKey
  obtain ⟨_, _, body4, _, hin4, _, _, _⟩ := ev4_whisper
  obtain ⟨cls, hv, hghost, hm0_fn, hm1_fn⟩ := extract_clean_prefix hfit (by decide) hex
  have hm0 := hm0_fn (by decide)
  have hm1 := hm1_fn (by decide)
  have hex_clean := explains_ssClean (k := 4) (by decide) hfit hv hghost
    (fun _ => hm0) (fun _ => hm1)
  have hNoRead := not_readCollisionCli_ssClean_le4 rcprI0 r S (gClean r cls) cls
    (k := 4) (by decide) (rcprTrace.take 4)
  have ht4 := recvRep_ev4 hfit hin4 hm1
  have hAcc := modelAccepts_ev4 hfit hv hin4 hm1 hex_clean ht4
  have hpinned2 := prefixPinned_gClean_2 hfit hex.1 hp2 hm0 hm1
  have hNoRecv := not_recvCollisionOn_of_pinned r S (gClean r cls) (visClean r cls 4)
    cls hfit hv hpinned2
  have hNoResel := not_reselectCollisionOn_of_pinned r S (gClean r cls) (visClean r cls 4)
    cls hfit hv hpinned2
  exact not_nextEventCollides_accepted_whisper ev4_party_cmd.2 hin4
    hex_clean hNoRead ht4 hAcc hNoRecv hNoResel

/-! ## 5. Top-Level `.recv` Non-Collision Across `rcprTrace` -/

private theorem rcprTrace_eq_list :
    rcprTrace =
      [ .run (traceEv 0), .run (traceEv 1), .run (traceEv 2), .run (traceEv 3), .run (traceEv 4),
        .env (.leak "alice" rcprLeakKey1),
        .env (.leak "alice" rcprSpqrState1),
        .run rcprStopEv ] := by
  change cliTrace.take 5 ++ _ = _
  rw [show cliTrace.take 5 = rcprTrace.take 5 from rfl, rcprTrace_take5]
  rfl

theorem not_nextEventCollides_recv (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) (evs₁ : List CliEvent) (ev : RunEvent)
    (evs₂ : List CliEvent) (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (_hnfe : ∀ g' ss' vis', ¬ Explains rcprI0 r S g' ss' vis' rcprTrace)
    (hsplit : rcprTrace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains rcprI0 r S g ss vis evs₁)
    (hrecv : ∃ peer, ev.cmd = .recv peer) :
    ¬ NextEventCollides rcprI0 r S g ss vis evs₁ ev := by
  have hlist := rcprTrace_eq_list.symm.trans hsplit
  rcases evs₁ with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | ⟨e4, _ | ⟨e5, _ | ⟨e6, _ | ⟨e7, rest⟩⟩⟩⟩⟩⟩⟩⟩
  · simp only [List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨rfl, _⟩
    obtain ⟨peer, hcmd⟩ := hrecv
    rw [ev0_cmd_and_exit.2.1] at hcmd
    cases hcmd
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨rfl, rfl, _⟩
    obtain ⟨peer, hcmd⟩ := hrecv
    rw [ev1_party_cmd.2] at hcmd
    cases hcmd
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨rfl, rfl, rfl, _⟩
    have ht2 : [.run (traceEv 0), .run (traceEv 1)] = rcprTrace.take 2 := by
      have h5 := rcprTrace_take5
      have h2 := congrArg (List.take 2) h5
      rw [List.take_take, Nat.min_eq_left (by decide)] at h2
      exact h2.symm
    rw [ht2] at hex ⊢
    exact not_nextEventCollides_ev2 hfit hex
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨rfl, rfl, rfl, rfl, _⟩
    obtain ⟨peer, hcmd⟩ := hrecv
    rw [ev3_party_cmd.2] at hcmd
    cases hcmd
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
    have ht4 : [.run (traceEv 0), .run (traceEv 1), .run (traceEv 2), .run (traceEv 3)] = rcprTrace.take 4 := by
      have h5 := rcprTrace_take5
      have h4 := congrArg (List.take 4) h5
      rw [List.take_take, Nat.min_eq_left (by decide)] at h4
      exact h4.symm
    rw [ht4] at hex ⊢
    exact not_nextEventCollides_ev4 hfit hex
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlist
    rcases hlist with ⟨_, _, _, _, _, hbad, _⟩
    cases hbad
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlist
    rcases hlist with ⟨_, _, _, _, _, _, hbad, _⟩
    cases hbad
  · simp only [List.cons_append, List.nil_append, List.cons.injEq, CliEvent.run.injEq] at hlist
    rcases hlist with ⟨_, _, _, _, _, _, _, rfl, _⟩
    exact nextEventCollides_AutoFalse rfl
  · have hlen := congrArg List.length hlist
    simp only [List.length_cons, List.length_nil, List.length_append] at hlen
    omega

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision
