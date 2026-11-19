/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import Symbolic.Proofs.SpecLemmas.ModelProofDefs
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean-Prefix Outer Step Agreement (`CleanPrefixB.lean`)

1. `PkiUnchanged` on `t4Opk` (threshold `26`, pinning `ikA`, `ikB`, `spkB`, `pqskB`, `opkB`).
2. `NoPartyState`, `NoNewPartyState`, `HSSidBound`, `SessionAliceDone`, and `ActiveAliceSt`.
3. `alice_init_agree` (Calls 0 & 3), `alice_send_agree` (Calls 1 & 4), and `bob_call2_preserve`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixB

open scoped DY.Libsignal.Composed
open DY (Bytes Participant Traceful ExecTrace ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState KeyKind BundleHandles AliceHandshakeOut)
open DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo isCurrentSnapshot u32Max)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds PreKeyFields
   gamma clamp slice ecKey kyberKey pubBytes secretBytes preKeyWire parsePreKeyWire
   setupTrace runSteps stepView encSendEntry pendingPreKey lastSent
   rngEntry kyberCoinEntries received randTerm
   GhostAndSemMatchSetup GhostWF DrawsMatch OutputsMatch RunMatches nextBundleIds stepIn)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves TRStEntry RndE NetE TRStE PQStE PQEvE CEvE TREvE at?_append_cases
   proj_inj_eq at?_le_some)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState bks_lt_length_of_at? bks_getEventAt_of_le
   isCurrentSnapshot_false_of_later aliceStartState aliceStartTrOfOut
   length_aliceStartTrOfOut getEventAt_pq_aliceStartTrOfOut)
open Symbolic.Swarm.CREF.TR (Runs gamma_rand gamma_dhPk)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg encSig parse_encMsg aliceOutOpk aliceSt StP EvP EvC StT EvT
   registerIdentityTr genSignedPrekeyTr genPQPrekeyTr genOneTimePrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t1 t2 t3 t4 t4Opk t7Opk t1_length t2_length t3_length t4_length t4Opk_length t7Opk_length
   ikA ikB spkB pqskB opkB oOpk dhsAOpk stA0Opk)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned keepOpkPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (ev ev0_cmd_and_exit ev3_cmd_and_exit ev3_in_eq_ev0 ev0_bundle_base
   ev0KyberEnt ev0_coins_base ev3KyberEnt ev3_coins_base
   ev1_facts ev4_facts ev1_to_ev2 ev4_to_ev5 p2 p5 serializeAddresses_alice_bob_eq)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (ValidCoinLens t4_entry_facts setupTrace_eq_t4Opk encTrGen encTrGen_length encTrGen_le append_len
   at?_append_of_lt at?_append_self_proj at?_append_at le_append_of_le at?_mono
   pt0Clean coins0Clean key0Clean stA1Clean m0Clean
   o2Clean dhsA2Clean stA2_0Clean pt1Clean coins1Clean key1Clean stA2_1Clean m1Clean)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis
  (encSendList encTrGen_stepView_ok)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
  (r_facts_of_fit setupRandomsAt_of_fit gClean gClean_addr
   gClean_sigma_lt26 gClean_sigma_26 gClean_sigma_27 gClean_sigma_28
   gClean_sigma_35 gClean_sigma_36 gClean_sigma_52 gClean_sigma_53 gClean_sigma_54
   gClean_sigma_61 gClean_sigma_62 ghostAndSemMatchSetup_gClean
   ev0_bundle_opk_spk gamma_dhPk_ts gamma_randTerm_pos)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA
  (StateBytesAgree stateBytesAgree_aliceStartOpk stateBytesAgree_encrypt
   PeeledCall preCond_of_stepIn sendCallOf stepCoinLen)

attribute [local irreducible] WitnessParse.ev

/-! ## 1. `PkiUnchanged` on `t4Opk` (Threshold `26`) -/

abbrev PQStEntry :=
  DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState PQXDHState)
abbrev PQEvEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent
abbrev CEvEntry := DY.ProtocolEvent.ExecEntryT ComposedEvent

theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

def PkiUnchanged (tr : ExecTrace) : Prop :=
  t4Opk ≤ tr ∧
  (∀ i p kst, 26 ≤ i → (tr.at? i : Option PQStEntry) ≠ some ⟨⟨p, kst⟩⟩) ∧
  (∀ i p pk vk c, 26 ≤ i → (tr.at? i : Option PQEvEntry) ≠ some ⟨.IdentityRegistered p pk vk c⟩)

theorem pkiUnchanged_t4Opk : PkiUnchanged t4Opk := by
  refine ⟨DY.Trace.le_refl t4Opk, ?_, ?_⟩
  · intro i p kst hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry) t4Opk i
    rw [hat, t4Opk_length] at hlt; simp at hlt; omega
  · intro i p pk vk c hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry) t4Opk i
    rw [hat, t4Opk_length] at hlt; simp at hlt; omega

private theorem pkiUnchanged_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : PkiUnchanged tr) (e : E)
    (hnoneSt : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQStEntry) = none)
    (hnoneEv : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntry) = none) :
    PkiUnchanged (tr.append e) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr e), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · rw [hnoneSt] at hproj; cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · rw [hnoneEv] at hproj; cases hproj

private theorem pkiUnchanged_append_pqEv {tr : ExecTrace} (h : PkiUnchanged tr)
    (ev0 : PQXDHEvent) (hnreg : ∀ p pk vk c, ev0 ≠ .IdentityRegistered p pk vk c) :
    PkiUnchanged (tr.append (PQEvE ev0)) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr _), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · simp only [PQEvE, proj_inj_eq, Option.some.injEq] at hproj
      injection hproj with hev; exact hnreg p pk vk c hev

private theorem preserves_pki_genRand (n : Nat) :
    Preserves PkiUnchanged (DY.Random.genRand n : Traceful Bytes) :=
  fun tr h => (Runs.genRand tr n).2.symm ▸ pkiUnchanged_append_non h (RndE n) rfl rfl

private theorem preserves_pki_sendMessage (m : Bytes) :
    Preserves PkiUnchanged (DY.Network.sendMessage m) :=
  fun tr h => (Runs.sendMessage tr m).2.symm ▸ pkiUnchanged_append_non h (NetE m) rfl rfl

private theorem preserves_pki_storeTR (p : Participant) (st : TRState) :
    Preserves PkiUnchanged (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr h => by rw [storeLocalState_tr_snd_eq]; exact pkiUnchanged_append_non h (TRStE p st) rfl rfl

private theorem preserves_pki_logC (ev0 : ComposedEvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev0) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (CEvE ev0) rfl rfl

private theorem preserves_pki_logTR (ev0 : TREvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev0) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (TREvE ev0) rfl rfl

private theorem preserves_pki_logPQ (ev0 : PQXDHEvent)
    (hnreg : ∀ p pk vk c, ev0 ≠ .IdentityRegistered p pk vk c) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev0) :=
  fun tr h => (Runs.logEvent tr ev0).2.symm ▸ pkiUnchanged_append_pqEv h ev0 hnreg

private theorem preserves_pki_getKey (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_pki_lookupIdentity (p : Participant) (h : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_pki_logSkippedKeys (s : SessionInfo)
    (pk : Bytes) (rIdx src : Nat) (ck : Bytes) (n : UInt32) (k : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_pki_logTR _) fun _ => ih _ _

private theorem preserves_pki_ensureReceiverChain (st : TRState) (pk : Bytes) :
    Preserves PkiUnchanged (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · exact Preserves.bind
      (by rw [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
          exact Preserves.bind (Preserves.guardP _) fun _ =>
            Preserves.bind (preserves_pki_genRand 32) fun _ => Preserves.pure _)
      fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_pki_logMKAndStore (me : Participant)
    (s : SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (r par : Nat) (st : TRState) :
    Preserves PkiUnchanged
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_pki_logTR _) fun _ => preserves_pki_storeTR me st

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

local macro "pki_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_pki_genRand
  | with_reducible apply preserves_pki_storeTR | with_reducible apply preserves_pki_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_pki_getKey | with_reducible apply preserves_pki_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt
  | with_reducible apply preserves_pki_ensureReceiverChain
  | with_reducible apply preserves_pki_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_pki_logMKAndStore
  | (apply preserves_pki_logPQ; intros; rintro ⟨⟩)
  | with_reducible apply preserves_pki_logC
  | with_reducible apply preserves_pki_logTR | split | with_reducible intro))

theorem pkiUnchanged_runSteps_network :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) → PkiUnchanged tr → PkiUnchanged (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : PkiUnchanged ((Step.network m).next tr) := by
      rw [next_network]; exact pkiUnchanged_append_non h (NetE m) rfl rfl
    exact pkiUnchanged_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem pkiUnchanged_step_party {s : Step} {tr : ExecTrace}
    (hcls : s.cls = .party) (hpki : PkiUnchanged tr) : PkiUnchanged (s.next tr) := by
  cases s with
  | aliceStart a b idIdx regB bh =>
    have hact : Preserves PkiUnchanged (DY.Libsignal.Composed.aliceStart a b idIdx regB bh) := by
      unfold DY.Libsignal.Composed.aliceStart DY.Libsignal.PQXDH.aliceHandshake; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | bobStart b a kh regA mh pqIdx spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqr) := by
      rw [DY.Libsignal.Composed.bobStart_eq_inline]; unfold DY.Libsignal.PQXDH.bobHandshake; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageEncrypt me stateIdx cl pq =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageEncryptAbort me stateIdx =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr) := by
      rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; pki_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr hpki
  | _ => simp [Step.cls] at hcls

private theorem t4Opk_pqSt_cases {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (t4Opk.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) ∨
    (p = "bob" ∧ kst = { kind := .oneTimePrekey, sk := opkB }) := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQStEntry) = none →
      ((tr0.append e).at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ →
      (tr0.at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  dsimp only [t4Opk, genOneTimePrekeyTr] at hat
  replace hat := peel_non rfl hat
  rcases at?_append_cases hat with ⟨_, hat4⟩ | ⟨_, hprojOpk⟩
  · replace hat4 := peel_non rfl (peel_non rfl hat4)
    rw [ht4] at hat4; dsimp only [genPQPrekeyTr] at hat4
    replace hat4 := peel_non rfl (peel_non rfl hat4)
    rcases at?_append_cases hat4 with ⟨_, hat3⟩ | ⟨_, hproj4⟩
    · replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
      rw [ht3] at hat3; dsimp only [genSignedPrekeyTr] at hat3
      replace hat3 := peel_non rfl (peel_non rfl hat3)
      rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
      · replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
        rw [ht2] at hat2; dsimp only [registerIdentityTr] at hat2
        rcases at?_append_cases hat2 with ⟨_, hat2'⟩ | ⟨_, hproj2⟩
        · iterate 4 replace hat2' := peel_non rfl hat2'
          rw [ht1] at hat2'; dsimp only [registerIdentityTr] at hat2'
          rcases at?_append_cases hat2' with ⟨_, hat1'⟩ | ⟨_, hproj1⟩
          · iterate 4 replace hat1' := peel_non rfl hat1'
            have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry)
              (DY.Trace.nil : ExecTrace) i
            rw [hat1', Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
          · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1; cases hproj1
            exact Or.inl ⟨rfl, rfl⟩
        · rw [t1_length] at hproj2; cases hproj2
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rw [t2_length] at hproj3; cases hproj3
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · rw [t3_length] at hproj4; cases hproj4
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rw [t4_length] at hprojOpk; cases hprojOpk
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

private theorem t4Opk_pqReg_cases {i : Nat} {p : Participant} {pk vk : Bytes} {c : Bool}
    (hat : (t4Opk.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntry) = none →
      ((tr0.append e).at? j : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩ →
      (tr0.at? j : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  dsimp only [t4Opk, genOneTimePrekeyTr] at hat
  replace hat := peel_non rfl (peel_non rfl hat)
  rcases at?_append_cases hat with ⟨_, hat4⟩ | ⟨_, hprojOpk⟩
  · replace hat4 := peel_non rfl hat4
    rw [ht4] at hat4; dsimp only [genPQPrekeyTr] at hat4
    replace hat4 := peel_non rfl (peel_non rfl (peel_non rfl hat4))
    rcases at?_append_cases hat4 with ⟨_, hat3⟩ | ⟨_, hproj4⟩
    · replace hat3 := peel_non rfl (peel_non rfl hat3)
      rw [ht3] at hat3; dsimp only [genSignedPrekeyTr] at hat3
      replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
      rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
      · replace hat2 := peel_non rfl (peel_non rfl hat2)
        rw [ht2] at hat2; dsimp only [registerIdentityTr] at hat2
        replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
        rcases at?_append_cases hat2 with ⟨_, hat1⟩ | ⟨_, hproj2⟩
        · replace hat1 := peel_non rfl hat1
          rw [ht1] at hat1; dsimp only [registerIdentityTr] at hat1
          replace hat1 := peel_non rfl (peel_non rfl (peel_non rfl hat1))
          rcases at?_append_cases hat1 with ⟨_, hat0⟩ | ⟨_, hproj1⟩
          · replace hat0 := peel_non rfl hat0
            have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry)
              (DY.Trace.nil : ExecTrace) i
            rw [hat0, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
          · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1; cases hproj1
            exact Or.inl ⟨rfl, rfl, rfl⟩
        · rw [t1_length] at hproj2; cases hproj2
          exact Or.inr ⟨rfl, rfl, rfl⟩
      · cases hproj3
    · cases hproj4
  · cases hprojOpk

theorem pki_pin_st {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (tr.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) ∨
    (p = "bob" ∧ kst = { kind := .oneTimePrekey, sk := opkB }) := by
  by_cases hlt : i < 26
  · rw [at?_of_le_lt hpki.1 (by rwa [t4Opk_length])] at hat; exact t4Opk_pqSt_cases hat
  · exact False.elim (hpki.2.1 i p kst (by omega) hat)

theorem pki_pin_reg {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {pk vk : Bytes} {c : Bool}
    (hat : (tr.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  by_cases hlt : i < 26
  · rw [at?_of_le_lt hpki.1 (by rwa [t4Opk_length])] at hat; exact t4Opk_pqReg_cases hat
  · exact False.elim (hpki.2.2 i p pk vk c (by omega) hat)

/-! ## 2. `NoPartyState`, `NoNewPartyState`, `HSSidBound`, `SessionAliceDone`, `ActiveAliceSt` -/

def NoPartyState (party : Participant) (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noPartyState_t4Opk (party : Participant) : NoPartyState party t4Opk := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  intro i st hat
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none →
      ((tr0.append e).at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ →
      (tr0.at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  dsimp only [t4Opk, genOneTimePrekeyTr] at hat
  iterate 4 replace hat := peel_non rfl hat
  rw [ht4] at hat; dsimp only [genPQPrekeyTr] at hat
  iterate 6 replace hat := peel_non rfl hat
  rw [ht3] at hat; dsimp only [genSignedPrekeyTr] at hat
  iterate 6 replace hat := peel_non rfl hat
  rw [ht2] at hat; dsimp only [registerIdentityTr] at hat
  iterate 5 replace hat := peel_non rfl hat
  rw [ht1] at hat; dsimp only [registerIdentityTr] at hat
  iterate 5 replace hat := peel_non rfl hat
  have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) (DY.Trace.nil : ExecTrace) i
  rw [hat, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt

def NoNewPartyState (party : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ j st, tr₀.length ≤ j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noNewPartyState_refl (party : Participant) (tr : ExecTrace) :
    NoNewPartyState party tr tr :=
  ⟨DY.Trace.le_refl tr, fun _ _ hj hat => absurd (bks_lt_length_of_at? hat) (by omega)⟩

theorem noNewPartyState_trans {party : Participant} {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewPartyState party tr₀ tr₁) (h12 : NoNewPartyState party tr₁ tr₂) :
    NoNewPartyState party tr₀ tr₂ := by
  refine ⟨DY.Trace.le_trans _ _ _ h01.1 h12.1, fun j st hj hat => ?_⟩
  by_cases hlt : j < tr₁.length
  · rw [at?_of_le_lt h12.1 hlt] at hat; exact h01.2 j st hj hat
  · exact h12.2 j st (Nat.le_of_not_lt hlt) hat

theorem noPartyState_of_noNew {party : Participant} {tr tr' : ExecTrace}
    (hnew : NoNewPartyState party tr tr') (h0 : NoPartyState party tr) :
    NoPartyState party tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat; exact h0 i st hat
  · exact hnew.2 i st (Nat.le_of_not_lt hlt) hat

theorem noNewPartyState_append_other {E : Type} [ExecTraceTypes.Has E]
    {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    NoNewPartyState party tr₀ (tr.append e) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr e, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · rw [hnone] at hproj; cases hproj

theorem noNewPartyState_append_trSt_ne {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (p : Participant) (hp : p ≠ party) (st₀ : TRState) :
    NoNewPartyState party tr₀ (tr.append (TRStE p st₀)) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr _, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · simp only [TRStE, proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1; injection h1 with hp_eq _; exact hp hp_eq

private theorem preserves_nn_genRand {party : Participant} {tr₀ : ExecTrace} (n : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Random.genRand n : Traceful Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ noNewPartyState_append_other hInv (RndE n) rfl

private theorem preserves_nn_sendMessage {party : Participant} {tr₀ : ExecTrace} (m : Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ noNewPartyState_append_other hInv (NetE m) rfl

private theorem preserves_nn_storeTR {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (hp : p ≠ party) (st : TRState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by rw [storeLocalState_tr_snd_eq]; exact noNewPartyState_append_trSt_ne hInv p hp st

private theorem preserves_nn_storePQ {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (st : PQXDHState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Runs.storeLocalState tr p st).2.symm ▸ noNewPartyState_append_other hInv (PQStE p st) rfl

private theorem preserves_nn_logPQ {party : Participant} {tr₀ : ExecTrace} (ev0 : PQXDHEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev0) :=
  fun tr hInv => (Runs.logEvent tr ev0).2.symm ▸ noNewPartyState_append_other hInv (PQEvE ev0) rfl

private theorem preserves_nn_logC {party : Participant} {tr₀ : ExecTrace} (ev0 : ComposedEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev0) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (CEvE ev0) rfl

private theorem preserves_nn_logTR {party : Participant} {tr₀ : ExecTrace} (ev0 : TREvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev0) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (TREvE ev0) rfl

private theorem preserves_nn_getKey {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_nn_lookupIdentity {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_nn_logMKAndStore {party : Participant} {tr₀ : ExecTrace}
    (me : Participant) (hme : me ≠ party) (s : SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_nn_logTR _) fun _ => preserves_nn_storeTR me hme st

private theorem preserves_nn_dhRatchetStep {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  rw [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_nn_genRand 32) fun _ => Preserves.pure _

private theorem preserves_nn_ensureReceiverChain {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_nn_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_nn_logSkippedKeys {party : Participant} {tr₀ : ExecTrace}
    (s : SessionInfo) (pk : Bytes) (rIdx src : Nat) (ck : Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_nn_logTR _) fun _ => ih _ _

local macro "noPartySt_tac" hne:ident : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_nn_genRand
  | with_reducible apply preserves_nn_storeTR _ $hne
  | with_reducible apply preserves_nn_storePQ | with_reducible apply preserves_nn_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_nn_getKey | with_reducible apply preserves_nn_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply preserves_nn_dhRatchetStep
  | with_reducible apply preserves_nn_ensureReceiverChain
  | with_reducible apply preserves_nn_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_nn_logMKAndStore _ $hne
  | with_reducible apply preserves_nn_logPQ | with_reducible apply preserves_nn_logC
  | with_reducible apply preserves_nn_logTR | split | with_reducible intro))

theorem noNewPartyState_runSteps_network {party : Participant} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) → NoNewPartyState party tr (runSteps pre tr)
  | [], tr, _ => noNewPartyState_refl party tr
  | s :: pre, tr, hnet => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : NoNewPartyState party tr ((Step.network m).next tr) := by
      rw [next_network]
      exact noNewPartyState_append_other (noNewPartyState_refl party tr) (NetE m) rfl
    exact noNewPartyState_trans hm
      (noNewPartyState_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)))

theorem noNewPartyState_step_other {party : Participant} {s : Step} (tr : ExecTrace)
    (hcls : s.cls = .party) (hne : s.party? ≠ some party) :
    NoNewPartyState party tr (s.next tr) := by
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
    have hne' : a ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
      unfold DY.Libsignal.Composed.aliceStart DY.Libsignal.PQXDH.aliceHandshake; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    have hne' : b ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqr) := by
      rw [DY.Libsignal.Composed.bobStart_eq_inline]; unfold DY.Libsignal.PQXDH.bobHandshake; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncrypt me stateIdx cl pq =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncryptAbort me stateIdx =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr) := by
      rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | _ => simp [Step.cls] at hcls

/-! ## 3. `HSSidBound`, `SessionAliceDone`, and `ActiveAliceSt` -/

private theorem dhPk_rnd_ts_ne {ts1 ts2 : Nat} (hne : ts1 ≠ ts2) :
    dhPk (rnd ts1 32) ≠ dhPk (rnd ts2 32) := by
  intro heq
  have hpack1 :
      (({ sk := rnd ts1 32 } : DY.DiffieHellman.DhPk.SubF Bytes).pack) =
      (({ sk := rnd ts2 32 } : DY.DiffieHellman.DhPk.SubF Bytes).pack) := heq
  have hsk := congrArg DY.DiffieHellman.DhPk.SubF.sk
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack1)
  have hpack2 :
      (({ timestamp := ts1, size := 32 } : DY.Random.Random Bytes).pack) =
      (({ timestamp := ts2, size := 32 } : DY.Random.Random Bytes).pack) := hsk
  exact hne (congrArg DY.Random.Random.timestamp
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack2))

def HSSidBound (tr : ExecTrace) : Prop :=
  ∀ i s d, tr.getEventAt ComposedEvent i = some (.HandshakeSession s d) →
    s.me ≠ "alice" ∨ ∃ ts rk, ts < tr.length ∧ s.sid = DY.Concat.concat (dhPk (rnd ts 32)) rk

theorem hsSidBound_t4Opk : HSSidBound t4Opk := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  intro i s d hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : (t4Opk.at? i : Option CEvEntry) with _ | ev0
  · rw [hat] at hget; cases hget
  · exfalso
    have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
        (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option CEvEntry) = none →
        ((tr0.append e).at? j : Option CEvEntry) = some ev0 →
        (tr0.at? j : Option CEvEntry) = some ev0 := by
      intro E _ tr0 e j hnone h
      rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
      · exact h0
      · rw [hnone] at hp; cases hp
    dsimp only [t4Opk, genOneTimePrekeyTr] at hat
    iterate 4 replace hat := peel_non rfl hat
    rw [ht4] at hat; dsimp only [genPQPrekeyTr] at hat
    iterate 6 replace hat := peel_non rfl hat
    rw [ht3] at hat; dsimp only [genSignedPrekeyTr] at hat
    iterate 6 replace hat := peel_non rfl hat
    rw [ht2] at hat; dsimp only [registerIdentityTr] at hat
    iterate 5 replace hat := peel_non rfl hat
    rw [ht1] at hat; dsimp only [registerIdentityTr] at hat
    iterate 5 replace hat := peel_non rfl hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := CEvEntry) (DY.Trace.nil : ExecTrace) i
    rw [hat, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt

theorem hsSidBound_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : HSSidBound tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CEvEntry) = none) :
    HSSidBound (tr.append e) := by
  intro i s d hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append e).at? i : Option CEvEntry) with _ | ev0
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; injection hget with hev
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · rcases h i s d (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0, hev]) with hme | ⟨ts, rk, hts, hsid⟩
      · exact Or.inl hme
      · exact Or.inr ⟨ts, rk, by rw [append_len]; omega, hsid⟩
    · rw [hnone] at hproj; cases hproj

theorem hsSidBound_append_cev_ne {tr : ExecTrace} (h : HSSidBound tr)
    (s0 : SessionInfo) (hs0 : s0.me ≠ "alice") (d0 : Nat) :
    HSSidBound (tr.append (CEvE (.HandshakeSession s0 d0))) := by
  intro i s d hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append (CEvE (.HandshakeSession s0 d0))).at? i : Option CEvEntry) with _ | ev0
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; injection hget with hev
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · rcases h i s d (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0, hev]) with hme | ⟨ts, rk, hts, hsid⟩
      · exact Or.inl hme
      · exact Or.inr ⟨ts, rk, by rw [append_len]; omega, hsid⟩
    · simp only [CEvE, proj_inj_eq, Option.some.injEq] at hproj
      subst hproj; injection hev with hs_eq _
      exact Or.inl (hs_eq ▸ hs0)

theorem hsSidBound_runSteps_network :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) → HSSidBound tr → HSSidBound (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : HSSidBound ((Step.network m).next tr) := by
      rw [next_network]; exact hsSidBound_append_non h (NetE m) rfl
    exact hsSidBound_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem hsSidBound_aliceStartTrOfOut {tr : ExecTrace} {b : Participant} {o : AliceHandshakeOut}
    (h0 : HSSidBound tr) :
    HSSidBound (aliceStartTrOfOut tr "alice" b o) := by
  unfold aliceStartTrOfOut
  dsimp only
  refine hsSidBound_append_non ?_ _ rfl
  let dhsA := randTerm (tr.length + 2) 32
  let stA := aliceStartState tr b o
  let tr7 := (((((((tr.append (Symbolic.Swarm.CREF.TR.RndE 32)).append
    (Symbolic.Swarm.CREF.TR.RndE 32)).append (Symbolic.Swarm.CREF.TR.RndE 32)).append
    (Symbolic.Swarm.CREF.TR.NetE o.ek)).append (Symbolic.Swarm.CREF.TR.NetE o.ct)).append
    (Symbolic.Swarm.CREF.TR.EvE (.AliceDone "alice" b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (DY.ProtocolEvent.ExecEntryT.mk (TREvent.InitSession "alice" b (dhPk dhsA) o.spk)))
  have h7 : HSSidBound tr7 :=
    hsSidBound_append_non (hsSidBound_append_non (hsSidBound_append_non
      (hsSidBound_append_non (hsSidBound_append_non (hsSidBound_append_non
        (hsSidBound_append_non h0 _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl
  let tr8 := tr7.append
    (DY.ProtocolEvent.ExecEntryT.mk (ComposedEvent.HandshakeSession (stA.sessionInfo "alice") (tr.length + 5)))
  intro i s d hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : (tr8.at? i : Option CEvEntry) with _ | ev0
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; injection hget with hev
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · rcases h7 i s d (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0, hev]) with hme | ⟨ts, rk, hts, hsid⟩
      · exact Or.inl hme
      · dsimp only [tr7] at hts
        simp only [append_len] at hts
        exact Or.inr ⟨ts, rk, by simp only [append_len]; omega, hsid⟩
    · simp only [proj_inj_eq, Option.some.injEq] at hproj
      subst hproj; injection hev with hs_eq _
      subst hs_eq
      exact Or.inr ⟨tr.length + 2, o.keys.rk, by simp only [append_len]; omega, rfl⟩

theorem hsSidBound_encTrGen {tr : ExecTrace} {me : Participant} {stH cl : Nat}
    {st : TRState} {pq : Bytes} (h0 : HSSidBound tr) :
    HSSidBound (encTrGen tr me stH cl st pq) := by
  unfold encTrGen; dsimp only
  exact hsSidBound_append_non (hsSidBound_append_non (hsSidBound_append_non
    (hsSidBound_append_non (hsSidBound_append_non (hsSidBound_append_non
      (hsSidBound_append_non h0 _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl

theorem hsSidBound_step_other {s : Step} {tr : ExecTrace}
    (hcls : s.cls = .party) (hne : s.party? ≠ some "alice") (h0 : HSSidBound tr) :
    HSSidBound (s.next tr) := by
  have hgen : ∀ n, Preserves HSSidBound (DY.Random.genRand n : Traceful Bytes) :=
    fun n t h => (Runs.genRand t n).2.symm ▸ hsSidBound_append_non h (RndE n) rfl
  have hsend : ∀ m, Preserves HSSidBound (DY.Network.sendMessage m) :=
    fun m t h => (Runs.sendMessage t m).2.symm ▸ hsSidBound_append_non h (NetE m) rfl
  have hstoreTR : ∀ p (st : TRState), Preserves HSSidBound (DY.PersistentLocalState.storeLocalState p st) :=
    fun p st t h => by rw [storeLocalState_tr_snd_eq]; exact hsSidBound_append_non h (TRStE p st) rfl
  have hstorePQ : ∀ p (st : PQXDHState), Preserves HSSidBound (DY.PersistentLocalState.storeLocalState p st) :=
    fun p st t h => (Runs.storeLocalState t p st).2.symm ▸ hsSidBound_append_non h (PQStE p st) rfl
  have hlogPQ : ∀ ev0 : PQXDHEvent, Preserves HSSidBound (DY.ProtocolEvent.logEvent ev0) :=
    fun ev0 t h => (Runs.logEvent t ev0).2.symm ▸ hsSidBound_append_non h (PQEvE ev0) rfl
  have hlogTR : ∀ ev0 : TREvent, Preserves HSSidBound (DY.ProtocolEvent.logEvent ev0) :=
    fun ev0 t h => by rw [logEvent_snd_eq]; exact hsSidBound_append_non h (TREvE ev0) rfl
  have hlogC_ne : ∀ (p : Participant) (hp : p ≠ "alice") (st : TRState) (d : Nat),
      Preserves HSSidBound (DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo p) d)) :=
    fun p hp st d t h => by rw [logEvent_snd_eq]; exact hsSidBound_append_cev_ne h (st.sessionInfo p) hp d
  have hgetK : ∀ p idx kind, Preserves HSSidBound (DY.Libsignal.PQXDH.getKey p idx kind) :=
    fun p idx _ => Preserves.bind (Preserves.getLocalState_pq p idx) fun _ =>
      Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  have hlook : ∀ p idx, Preserves HSSidBound (DY.Libsignal.PQXDH.lookupIdentity p idx) := by
    intro p idx; unfold DY.Libsignal.PQXDH.lookupIdentity
    refine Preserves.bind (Preserves.getEntry idx) fun _ => ?_
    split
    · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
    · exact Preserves.failure
  have hdhr : ∀ (st : TRState) (pk : Bytes), Preserves HSSidBound (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) :=
    fun st pk => by
      rw [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
      exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.bind (hgen 32) fun _ => Preserves.pure _
  have hens : ∀ (st : TRState) (pk : Bytes), Preserves HSSidBound (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
    intro st pk; rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
    · exact Preserves.pure _
    · exact Preserves.bind (hdhr st pk) fun _ => Preserves.pure _
    · exact Preserves.failure
  have hskip : ∀ s0 pk rIdx src ck n k, Preserves HSSidBound (DY.Libsignal.TripleRatchet.logSkippedKeys s0 pk rIdx src ck n k) := by
    intro s0 pk rIdx src ck n k; induction k generalizing ck n with
    | zero => exact Preserves.pure _
    | succ k ih => exact Preserves.bind (hlogTR _) fun _ => ih _ _
  have hlmk : ∀ me s0 dir seed pqSalt n r par st,
      Preserves HSSidBound (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s0 dir seed pqSalt n r par st) :=
    fun me _ _ _ _ _ _ _ st => Preserves.bind (hlogTR _) fun _ => hstoreTR me st
  cases s with
  | aliceStart a b idIdx regB bh =>
    have hne' : a ≠ "alice" := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves HSSidBound (DY.Libsignal.Composed.aliceStart a b idIdx regB bh) := by
      unfold DY.Libsignal.Composed.aliceStart DY.Libsignal.PQXDH.aliceHandshake
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
        | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hgen
        | with_reducible apply hstoreTR | with_reducible apply hstorePQ | with_reducible apply hsend
        | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
        | with_reducible apply hgetK | with_reducible apply hlook
        | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
        | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
        | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
        | with_reducible apply Preserves.traceLength
        | with_reducible apply hlogC_ne a hne' | with_reducible apply hlogPQ
        | with_reducible apply hlogTR | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | bobStart b a kh regA mh pqIdx spqr =>
    have hne' : b ≠ "alice" := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves HSSidBound (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqr) := by
      rw [DY.Libsignal.Composed.bobStart_eq_inline]; unfold DY.Libsignal.PQXDH.bobHandshake
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
        | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hgen
        | with_reducible apply hstoreTR | with_reducible apply hstorePQ | with_reducible apply hsend
        | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
        | with_reducible apply hgetK | with_reducible apply hlook
        | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
        | with_reducible apply Preserves.receiveSignalMsg | with_reducible apply Preserves.verifyMacAndDecrypt
        | with_reducible apply hdhr | with_reducible apply hens | with_reducible apply hskip
        | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
        | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
        | with_reducible apply Preserves.traceLength | with_reducible apply hlmk
        | with_reducible apply hlogC_ne b hne' | with_reducible apply hlogPQ
        | with_reducible apply hlogTR | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | messageEncrypt me stateIdx cl pq =>
    have hact : Preserves HSSidBound (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
        | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hgen
        | with_reducible apply hstoreTR | with_reducible apply hsend
        | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.receiveMessage
        | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.guardP
        | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
        | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
        | with_reducible apply hlmk | with_reducible apply hlogTR | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | messageEncryptAbort me stateIdx =>
    have hact : Preserves HSSidBound (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hgen
        | with_reducible apply hsend | with_reducible apply hstoreTR | with_reducible apply hlogTR
        | with_reducible apply Preserves.getLocalState_tr
        | with_reducible apply Preserves.guardP | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hact : Preserves HSSidBound (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx mIdx pq spqr) := by
      rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
        | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hgen
        | with_reducible apply hstoreTR | with_reducible apply hsend
        | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.receiveMessage
        | with_reducible apply Preserves.receiveSignalMsg | with_reducible apply Preserves.verifyMacAndDecrypt
        | with_reducible apply hdhr | with_reducible apply hens | with_reducible apply hskip
        | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.guardP
        | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
        | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
        | with_reducible apply hlmk | with_reducible apply hlogTR | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hact : Preserves HSSidBound
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
      repeat (first
        | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
        | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
        | with_reducible apply Preserves.failure | with_reducible apply hstoreTR | with_reducible apply hsend
        | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.receiveMessage
        | with_reducible apply Preserves.receiveSignalMsg | with_reducible apply Preserves.verifyMacAndDecrypt
        | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.guardP
        | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
        | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
        | with_reducible apply hlmk | with_reducible apply hlogTR | split | with_reducible intro)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]; exact hact tr h0
  | _ => simp [Step.cls] at hcls

def SessionAliceDone (s0 : SessionInfo) (ek0 ct0 : Bytes) (tr : ExecTrace) : Prop :=
  ∀ i d, tr.getEventAt ComposedEvent i = some (.HandshakeSession s0 d) →
    d < tr.length ∧
    ∃ a b ik1 ik2 spk pq opk keys,
      tr.getEventAt PQXDHEvent d = some (.AliceDone a b ik1 ik2 spk pq opk ek0 ct0 keys)

theorem sessionAliceDone_append_non {E : Type} [ExecTraceTypes.Has E]
    {s0 : SessionInfo} {ek0 ct0 : Bytes} {tr : ExecTrace}
    (h : SessionAliceDone s0 ek0 ct0 tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CEvEntry) = none) :
    SessionAliceDone s0 ek0 ct0 (tr.append e) := by
  intro i d hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append e).at? i : Option CEvEntry) with _ | ev0
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; injection hget with hev
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · obtain ⟨hd_lt, a, b, ik1, ik2, spk, pq, opk, keys, hpq⟩ :=
        h i d (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0, hev])
      refine ⟨by rw [append_len]; omega, a, b, ik1, ik2, spk, pq, opk, keys, ?_⟩
      rwa [bks_getEventAt_of_le PQXDHEvent (DY.Trace.append_le tr e) hd_lt]
    · rw [hnone] at hproj; cases hproj

theorem sessionAliceDone_runSteps_network {s0 : SessionInfo} {ek0 ct0 : Bytes} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      SessionAliceDone s0 ek0 ct0 tr → SessionAliceDone s0 ek0 ct0 (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : SessionAliceDone s0 ek0 ct0 ((Step.network m).next tr) := by
      rw [next_network]; exact sessionAliceDone_append_non h (NetE m) rfl
    exact sessionAliceDone_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem sessionAliceDone_encTrGen {s0 : SessionInfo} {ek0 ct0 : Bytes}
    {tr : ExecTrace} {me : Participant} {stH cl : Nat} {st : TRState} {pq : Bytes}
    (h0 : SessionAliceDone s0 ek0 ct0 tr) :
    SessionAliceDone s0 ek0 ct0 (encTrGen tr me stH cl st pq) := by
  unfold encTrGen; dsimp only
  exact sessionAliceDone_append_non (sessionAliceDone_append_non (sessionAliceDone_append_non
    (sessionAliceDone_append_non (sessionAliceDone_append_non (sessionAliceDone_append_non
      (sessionAliceDone_append_non h0 _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl) _ rfl

theorem sessionAliceDone_aliceStartTrOfOut {tr : ExecTrace} {b : Participant}
    {o : AliceHandshakeOut} (hSid : HSSidBound tr) :
    SessionAliceDone ((aliceStartState tr b o).sessionInfo "alice") o.ek o.ct
      (aliceStartTrOfOut tr "alice" b o) := by
  let s0 := (aliceStartState tr b o).sessionInfo "alice"
  let tr' := aliceStartTrOfOut tr "alice" b o
  have hle : tr ≤ tr' := by
    dsimp only [tr', aliceStartTrOfOut]
    iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.append_le _ _
  have hlen : tr'.length = tr.length + 9 := length_aliceStartTrOfOut tr "alice" b o
  have hpq5 := (getEventAt_pq_aliceStartTrOfOut tr "alice" b o).2.2.2.2.2.1
  intro i d hget
  by_cases hlt : i < tr.length
  · exfalso
    rw [bks_getEventAt_of_le ComposedEvent hle hlt] at hget
    rcases hSid i s0 d hget with hme | ⟨ts, rk, hts, hsid⟩
    · exact hme rfl
    · have hpack :
          (({ lhs := dhPk (rnd (tr.length + 2) 32), rhs := o.keys.rk } : DY.Concat.Concat.SubF Bytes).pack) =
          (({ lhs := dhPk (rnd ts 32), rhs := rk } : DY.Concat.Concat.SubF Bytes).pack) := hsid
      have hdhs := congrArg DY.Concat.Concat.SubF.lhs (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack)
      exact dhPk_rnd_ts_ne (by omega) hdhs
  · by_cases hge : tr.length + 9 ≤ i
    · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
      rcases hat : (tr'.at? i : Option CEvEntry) with _ | _
      · rw [hat] at hget; cases hget
      · have := DY.Trace.at?_eq_some_implies_length_le (EntryT := CEvEntry) tr' i
        rw [hat, hlen] at this; simp at this; omega
    · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
      rcases hat : (tr'.at? i : Option CEvEntry) with _ | ev0
      · rw [hat] at hget; cases hget
      · rw [hat] at hget; injection hget with hev
        dsimp only [tr', aliceStartTrOfOut] at hat
        rcases at?_append_cases hat with ⟨_, hat8⟩ | ⟨_, hp8⟩
        · rcases at?_append_cases hat8 with ⟨hi7, hat7⟩ | ⟨_, hp7⟩
          · exfalso
            have peel_c : ∀ {E : Type} [ExecTraceTypes.Has E] {t0 : ExecTrace} {e : E} {j : Nat},
                (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option CEvEntry) = none →
                ((t0.append e).at? j : Option CEvEntry) = some ev0 →
                (t0.at? j : Option CEvEntry) = some ev0 := by
              intro E _ t0 e j hn h
              rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
              · exact h0
              · rw [hn] at hp; cases hp
            iterate 7 replace hat7 := peel_c rfl hat7
            exact hlt (bks_lt_length_of_at? hat7)
          · simp only [proj_inj_eq, Option.some.injEq] at hp7
            subst hp7; injection hev with _ hd_eq; subst hd_eq
            exact ⟨by rw [hlen]; omega, "alice", b, o.ikA, o.ikB, o.spk, o.pqpk, o.opk, o.keys, hpq5⟩
        · cases hp8

theorem pendingPreKey_eq_of_sessionAliceDone {stP : TRState} {ek0 ct0 : Bytes}
    {tr : ExecTrace} {stateIdx : Nat} {ek ct : Bytes}
    (hat_st : (tr.at? stateIdx : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩)
    (hsad : SessionAliceDone (stP.sessionInfo "alice") ek0 ct0 tr)
    (hpend : pendingPreKey tr stateIdx = some (ek, ct)) :
    ek = ek0 ∧ ct = ct0 := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hpend
  rw [hat_st] at hpend; dsimp only [Option.map] at hpend
  split at hpend
  · cases hpend
  · obtain ⟨ev_pq, hmem, hev_pq⟩ := List.exists_of_findSome?_eq_some hpend
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hmem
    rcases hce : tr.getEventAt ComposedEvent i with _ | ⟨s, d⟩
    · rw [hce] at hi; cases hi
    · rw [hce] at hi; dsimp only at hi
      split at hi
      · next hs_eq =>
        subst hs_eq
        obtain ⟨_, a, b, ik1, ik2, spk, pq, opk, keys, hpq⟩ := hsad i d hce
        rw [hpq] at hi
        injection hi with hi_eq
        subst hi_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at hev_pq
        exact ⟨hev_pq.1.symm, hev_pq.2.symm⟩
      · cases hi

def ActiveAliceSt (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (ek0 ct0 : Bytes) (stClean : TRState) (tr : ExecTrace) : Prop :=
  (∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true) ∧
  ∃ idxP stP,
    (tr.at? idxP : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩ ∧
    (∀ j st, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"alice", st⟩⟩) ∧
    StateBytesAgree S g g' stP stClean ∧
    SessionAliceDone (stP.sessionInfo "alice") ek0 ct0 tr

theorem activeAliceSt_pin_state {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {ek0 ct0 : Bytes} {stClean : TRState} {tr : ExecTrace} {stateIdx : Nat} {st : TRState}
    (hinv : ActiveAliceSt S g g' ek0 ct0 stClean tr)
    (hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    st.initiator = true ∧
    StateBytesAgree S g g' st stClean ∧
    SessionAliceDone (st.sessionInfo "alice") ek0 ct0 tr := by
  have hat := bks_stored_of_getLocalState hst
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hsad⟩ := hinv
  have hle : stateIdx ≤ idxP := by
    by_contra hgt; exact hmaxP stateIdx st (by omega) hat
  by_cases hlt : stateIdx < idxP
  · exfalso
    have hfalse := isCurrentSnapshot_false_of_later hat hatP hlt
      (by rw [hrole _ _ hatP, hrole _ _ hat])
    rw [hfalse] at hcur; cases hcur
  · have hidx : stateIdx = idxP := by omega
    subst hidx; rw [hatP] at hat; cases hat
    exact ⟨hrole _ _ hatP, hagree, hsad⟩

theorem activeAliceSt_init {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {ek0 ct0 : Bytes} {stClean : TRState} {tr tr' : ExecTrace}
    (hrole_prev : ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true)
    (hle : tr ≤ tr') {idxP' : Nat} {stP' : TRState}
    (hge : tr.length ≤ idxP')
    (hat' : (tr'.at? idxP' : Option TRStEntry) = some ⟨⟨"alice", stP'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → j = idxP' ∧ st = stP')
    (hinit' : stP'.initiator = true)
    (hagree' : StateBytesAgree S g g' stP' stClean)
    (hsad' : SessionAliceDone (stP'.sessionInfo "alice") ek0 ct0 tr') :
    ActiveAliceSt S g g' ek0 ct0 stClean tr' := by
  refine ⟨?_, idxP', stP', hat', ?_, hagree', hsad'⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat; exact hrole_prev i st hat
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat; exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat; omega

theorem activeAliceSt_runSteps_network {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {ek0 ct0 : Bytes} {stClean : TRState} {pre : List Step} {tr : ExecTrace}
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (h0 : ActiveAliceSt S g g' ek0 ct0 stClean tr) :
    ActiveAliceSt S g g' ek0 ct0 stClean (runSteps pre tr) := by
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hsad⟩ := h0
  have hnn := noNewPartyState_runSteps_network (party := "alice") pre tr hnet
  have hltP : idxP < tr.length := by
    have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr idxP
    rw [hatP] at h; simpa using h
  refine ⟨?_, idxP, stP, ?_, ?_, hagree, sessionAliceDone_runSteps_network pre hnet hsad⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hnn.1 hlt] at hat; exact hrole i st hat
    · exfalso; exact hnn.2 i st (Nat.le_of_not_lt hlt) hat
  · rwa [at?_of_le_lt hnn.1 hltP]
  · intro j st hj hat
    by_cases hlt : j < tr.length
    · rw [at?_of_le_lt hnn.1 hlt] at hat; exact hmaxP j st hj hat
    · exact hnn.2 j st (Nat.le_of_not_lt hlt) hat

theorem aliceAllInit_encTrGen {tr : ExecTrace} {stH cl : Nat} {stA : TRState} {pq : Bytes}
    (hrole : ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true)
    (hinit : stA.initiator = true) :
    ∀ i st, ((encTrGen tr "alice" stH cl stA pq).at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ →
      st.initiator = true := by
  intro i st hat
  unfold encTrGen at hat; dsimp only at hat
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none →
      ((tr0.append e).at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ →
      (tr0.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ := by
    intro E _ tr0 e hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  replace hat := peel_non rfl hat
  rcases at?_append_cases hat with ⟨_, hat5⟩ | ⟨_, hproj⟩
  · iterate 5 replace hat5 := peel_non rfl hat5
    exact hrole i st hat5
  · simp only [StT, proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1; injection h1 with _ hst
    subst hst; simpa [encSt] using hinit

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixB

