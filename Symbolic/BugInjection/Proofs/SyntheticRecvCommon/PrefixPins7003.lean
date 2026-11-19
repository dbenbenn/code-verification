/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
public import Symbolic.Proofs.Tests.Shared.Composed.Runs
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Prefix Pinning and Whole-Trace `Explains` Refutations for Seed 7003

Establishes:
1. `SemPinned2 S cl₁` from any model explanation of `[.run ev0, .run ev1_m1]` or `[.run ev0, .run ev1_m2]`.
2. `KnownBaseKeyOn` and `SemPinned2 S cl₁` from any explanation of `[.run ev0, .run ev1_m1, .run ev2_m1]`.
3. `¬ Explains compI7003 r S g ss vis m1Events` (`not_explains_m1`).
4. `SemPinned4_M2 S cl₁ cl₃` from any explanation of `[.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2]`.
5. `¬ Explains compI7003 r S g ss vis m2Events` (`not_explains_m2`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003

open ByteSpecs (hmacWith)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement (WireFields canonicalVariation)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys AliceHandshakeOut agree serializedIk)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg RecvChain SessionInfo parseTrSignalMsg computeMac trMsgKeys
   kdfCk createChain findRecvChain setRecvChain consumeMessageKey spqrA2B spqrB2A u32Max)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli (aliceUuid bobUuid serializeAddresses)
open Symbolic.Swarm.COMPOSED.CompTrace (at?_append_of_lt)
open Symbolic.Swarm.CREF (b1_setupTr1 b1_setupTr2 b1_setupTr3 b1_setupTr4 b1_RndE b1_NetE b1_EvE b1_StE)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next stepIn_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux (pack_of_view_eq_some)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd RndE NetE EvP EvT EvC StP StT aliceOut aliceSt aliceTr aliceTrOpt encMsg encSig encSt
   parse_encMsg bobSt0 ratchetState skipTr notInit_recv)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (runMatches_filter_send_send)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 hiding
  rk0Bytes seedA0Bytes cksA1Bytes seedB0Bytes cksA0Bytes cksB1Bytes cksB0Bytes
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003

/-! ## 1. Pinned Semantics Predicates -/

/-- Semantics equations pinned by explaining the 2-call prefix `[ev0, ev1]`. -/
def SemPinned2 (S : OpaqueSymbolSemantics) (cl₁ : Nat) : Prop :=
  (cl₁ = 0 ∨ cl₁ = 32 ∨ cl₁ = 64) ∧
  spqrKeyBytes (S.chainKey pqrBytes [0#8] [1#8, 0#8, 0#8, 0#8]) = salt1Bytes ∧
  S.sendMsg (S.init pqrBytes [0#8]) (coins1Bytes.take cl₁) = pqMsg1Bytes

theorem SemPinned2.le64 {S : OpaqueSymbolSemantics} {cl₁ : Nat} (h : SemPinned2 S cl₁) :
    cl₁ ≤ 64 := by
  rcases h.1 with rfl | rfl | rfl <;> decide

/-- Semantics equations pinned by explaining the 4-call M2 prefix `[ev0, ev1_m2, ev2_m2, ev3_m2]`. -/
def SemPinned4_M2 (S : OpaqueSymbolSemantics) (cl₁ cl₃ : Nat) : Prop :=
  SemPinned2 S cl₁ ∧
  (cl₃ = 0 ∨ cl₃ = 32 ∨ cl₃ = 64) ∧
  spqrKeyBytes (S.sendKey (S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes)
    (coins3M2Bytes.take cl₃)) = salt3Bytes ∧
  S.sendMsg (S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes)
    (coins3M2Bytes.take cl₃) = pqMsg3Bytes

theorem SemPinned4_M2.le64 {S : OpaqueSymbolSemantics} {cl₁ cl₃ : Nat}
    (h : SemPinned4_M2 S cl₁ cl₃) : cl₃ ≤ 64 := by
  rcases h.2.1 with rfl | rfl | rfl <;> decide

/-! ## 2. Basic List, HMAC, and Trace Lookup Helpers -/

theorem if_pos' {c : Prop} [Decidable c] {α : Sort _} (hc : c) {t e : α} :
    (if c then t else e) = t := by simp [hc]

theorem if_neg' {c : Prop} [Decidable c] {α : Sort _} (hnc : ¬ c) {t e : α} :
    (if c then t else e) = e := by simp [hnc]

theorem spqrKeyBytes_length (k : HwBytes) : (spqrKeyBytes k).length = 32 := by
  unfold spqrKeyBytes
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

private theorem sha256With_length (F : ByteSpecs.ShaState → HwBytes → ByteSpecs.ShaState)
    (m : HwBytes) : (ByteSpecs.sha256With F m).length = 32 := by
  unfold ByteSpecs.sha256With
  rcases ((ByteSpecs.chunks64 (ByteSpecs.sha256Pad m)).foldl F ByteSpecs.sha256IV) with ⟨l, hl⟩
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases hl
  rfl

theorem hmacWith_F7_length (k m : HwBytes) : (hmacWith F7 k m).length = 32 :=
  sha256With_length F7 _

theorem hmacWith_inj_of_untagged {k₁ k₂ m₁ m₂ : HwBytes}
    (hk₁ : k₁.length = 32) (hk₂ : k₂.length = 32)
    (h₂ : (hmacWith F7 k₂ m₂).take 4 ≠ compTag4)
    (heq : hmacWith F7 k₁ m₁ = hmacWith F7 k₂ m₂) :
    k₁ = k₂ ∧ m₁ = m₂ :=
  hmacWith_take8_inj_of_untagged hk₁ hk₂ h₂ (congrArg (List.take 8) heq)

theorem ratchet_b_untagged :
    (hmacWith F7 prkMsg3Bytes (encKey3Bytes ++ infoMessageKeysBytes ++ [0x02#8])).take 4 ≠ compTag4 ∧
    (hmacWith F7 salt3Bytes seedB0Bytes).take 4 ≠ compTag4 := by
  decide +kernel

theorem ecKey_inj {a b : HwBytes} (h : ecKey a = ecKey b) : a = b :=
  (List.cons.inj h).2

theorem kyberKey_inj {a b : HwBytes} (h : kyberKey a = kyberKey b) : a = b :=
  (List.cons.inj h).2

theorem append_inj_of_right_len {a₁ b₁ a₂ b₂ : HwBytes}
    (hb₁ : b₁.length = 8) (hb₂ : b₂.length = 8) (heq : a₁ ++ b₁ = a₂ ++ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hlen := congrArg List.length heq
  simp only [List.length_append, hb₁, hb₂] at hlen
  exact List.append_inj heq (by omega)

theorem ghostWF_append {g : Ghost} {v₁ v₂ : List VisEntry} (h : GhostWF g (v₁ ++ v₂)) :
    GhostWF g v₁ ∧ GhostWF g v₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨⟨fun v hv => h1 v (List.mem_append_left _ hv), h2,
          fun v hv => h3 v (List.mem_append_left _ hv)⟩,
         ⟨fun v hv => h1 v (List.mem_append_right _ hv), h2,
          fun v hv => h3 v (List.mem_append_right _ hv)⟩⟩

theorem stepsWF_append :
    ∀ (a b : List Step) (tr : ExecTrace),
      StepsWF (a ++ b) tr ↔ StepsWF a tr ∧ StepsWF b (runSteps a tr)
  | [], b, tr => by simp [StepsWF, runSteps]
  | s :: a, b, tr => by
    simp only [List.cons_append, StepsWF, runSteps]
    rw [stepsWF_append a b (s.next tr)]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
           fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem matchesEventsAt_run_exit0_inv
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry} {out : HwBytes}
    (hexit : ev.exit = some (0, out))
    (hm : MatchesEventsAt i r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs',
      ss = pre ++ s :: ss' ∧
      vis = v ++ vs' ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      RunMatches i r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsAt i r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss' evs vs' := by
  cases hm with
  | run1 hinv hrm hrest => exact ⟨_, _, _, _, _, rfl, rfl, hinv, hrm, hrest⟩
  | run0 _ hrej _ => exact absurd hexit (hrej out)

theorem length_append_eq {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem at?_nil_eq {E : Type} [ExecTraceTypes.Has E] (i : Nat) :
    ((Trace.nil : ExecTrace).at? i : Option E) = none := by
  have h0 : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  simp [DY.Trace.at?, h0]

theorem at?_ge_length_eq {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (h : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have hnlt : ¬ i < tr.length := by omega
  simp [DY.Trace.at?, hnlt]

theorem at?_append_same_eq {E : Type} [ExecTraceTypes.Has E]
    (hproj : ∀ x : E, (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option E) = some x)
    (tr : ExecTrace) (e : E) (i : Nat) :
    ((tr.append e).at? i : Option E) = if i = tr.length then some e else tr.at? i := by
  by_cases hi : i < tr.length
  · have hne : i ≠ tr.length := by omega
    rw [if_neg' hne]
    exact at?_append_of_lt tr e hi
  · by_cases heq : i = tr.length
    · subst heq
      rw [if_pos' rfl]
      have hlt : tr.length < (tr.append e).length := by rw [length_append_eq]; omega
      have hnlt : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [DY.Trace.at?, hlt, ↓reduceDIte]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2,
        hnlt, ↓reduceDIte]
      exact hproj e
    · rw [if_neg' heq, at?_ge_length_eq (tr.append e) (by rw [length_append_eq]; omega),
          at?_ge_length_eq tr (by omega)]

theorem at?_append_other_eq {E₁ E₂ : Type} [ExecTraceTypes.Has E₁] [ExecTraceTypes.Has E₂]
    {e : E₁}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E₂) = none)
    (tr : ExecTrace) (i : Nat) :
    ((tr.append e).at? i : Option E₂) = tr.at? i := by
  by_cases hi : i < tr.length
  · exact at?_append_of_lt tr e hi
  · by_cases heq : i = tr.length
    · subst heq
      have hlt : tr.length < (tr.append e).length := by rw [length_append_eq]; omega
      have hnlt : ¬ tr.length < tr.length := Nat.lt_irrefl _
      simp only [DY.Trace.at?, hlt, ↓reduceDIte]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2,
        hnlt, ↓reduceDIte, hnone]
    · rw [at?_ge_length_eq (tr.append e) (by rw [length_append_eq]; omega),
          at?_ge_length_eq tr (by omega)]

/-! ## 3. Monadic Inversion Helpers -/

theorem bind_some_inv {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace} {b : β}
    (h : ((x >>= f).run tr).1 = some b) :
    ∃ a tr₁, (x.run tr).1 = some a ∧ (x.run tr).2.val = tr₁ ∧
      ((f a).run tr₁).1 = some b ∧ ((x >>= f).run tr).2.val = ((f a).run tr₁).2.val := by
  rw [Traceful.run_bind] at h ⊢
  rcases hx : x.run tr with ⟨_ | a, ⟨t₁, _⟩⟩
  · simp [hx] at h
  · rw [hx] at h
    dsimp only at h ⊢
    rcases hf : (f a).run t₁ with ⟨_ | b', ⟨t₂, _⟩⟩
    · rw [hf] at h; cases h
    · rw [hf] at h
      refine ⟨a, t₁, rfl, rfl, ?_, ?_⟩
      · rw [hf]; exact h
      · rw [hf]

theorem isSome_iff_exists {α : Type} {o : Option α} : o.isSome = true ↔ ∃ a, o = some a := by
  cases o <;> simp

theorem guard_some_inv {p : Prop} [Decidable p] {tr : ExecTrace} {u : Unit}
    (h : ((_root_.guard p : Traceful Unit).run tr).1 = some u) : p := by
  by_cases hp : p
  · exact hp
  · simp [_root_.guard, hp, Traceful.run_failure] at h

theorem getEntry_some_inv {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : ((DY.getEntry i : Traceful E).run tr).1 = some e) :
    tr.at? i = some e ∧ ((DY.getEntry i : Traceful E).run tr).2.val = tr := by
  rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk] at h ⊢
  exact ⟨h, rfl⟩

theorem receiveMessage_some_inv {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : ((DY.Network.receiveMessage i).run tr).1 = some b) :
    tr.at? i = some (NetE b) ∧ ((DY.Network.receiveMessage i).run tr).2.val = tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1] at h ⊢
  obtain ⟨⟨m⟩, tr₁, he, htr₁, hp, hval⟩ := bind_some_inv h
  obtain ⟨hat, htr_e⟩ := getEntry_some_inv he
  rw [htr_e] at htr₁; subst htr₁
  rw [Traceful.run_pure] at hp hval
  cases hp
  exact ⟨hat, hval⟩

theorem getLocalState_tr_some_inv {tr : ExecTrace} {me : Participant} {i : Nat} {st : TRState}
    (h : ((DY.PersistentLocalState.getLocalState me i : Traceful TRState).run tr).1 = some st) :
    tr.at? i = some (StT me st) ∧
    ((DY.PersistentLocalState.getLocalState me i : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1] at h ⊢
  obtain ⟨ls, tr₁, hg, htr₁, hrest, hval₁⟩ := bind_some_inv h
  obtain ⟨⟨ls'⟩, tr₀, he, htr₀, hp₀, hval₀⟩ := bind_some_inv hg
  obtain ⟨hat, htr_e⟩ := getEntry_some_inv he
  rw [htr_e] at htr₀; subst htr₀
  rw [Traceful.run_pure] at hp₀ hval₀
  cases hp₀; subst htr₁; rw [hval₀] at hrest hval₁
  obtain ⟨_, tr₂, hgd, htr₂, hp₂, hval₂⟩ := bind_some_inv hrest
  have hpart : ls'.participant = me := guard_some_inv hgd
  rw [_root_.guard, if_pos' hpart, Traceful.run_pure] at htr₂
  subst htr₂
  rw [Traceful.run_pure] at hp₂ hval₂
  cases hp₂
  rcases ls' with ⟨p', st'⟩
  dsimp only at hpart; subst hpart
  exact ⟨hat, hval₁.trans hval₂⟩

theorem getKey_some_inv {tr : ExecTrace} {me : Participant} {i : Nat}
    {kind : DY.Libsignal.PQXDH.KeyKind} {sk : DY.Bytes}
    (h : ((DY.Libsignal.PQXDH.getKey me i kind).run tr).1 = some sk) :
    tr.at? i = some (StP me { kind, sk }) ∧
    ((DY.Libsignal.PQXDH.getKey me i kind).run tr).2.val = tr := by
  unfold DY.Libsignal.PQXDH.getKey at h ⊢
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1] at h ⊢
  obtain ⟨pst, tr₁, hg, htr₁, hrest, hval₁⟩ := bind_some_inv h
  obtain ⟨ls, tr₀a, hg₀, htr₀a, hrest₀, hval₀a⟩ := bind_some_inv hg
  obtain ⟨⟨ls'⟩, tr₀, he, htr₀, hp₀, hval₀⟩ := bind_some_inv hg₀
  obtain ⟨hat, htr_e⟩ := getEntry_some_inv he
  rw [htr_e] at htr₀; subst htr₀
  rw [Traceful.run_pure] at hp₀ hval₀; cases hp₀; subst htr₀a; rw [hval₀] at hrest₀ hval₀a
  obtain ⟨_, tr₀b, hgd₀, htr₀b, hp₀b, hval₀b⟩ := bind_some_inv hrest₀
  have hpart : ls'.participant = me := guard_some_inv hgd₀
  rw [_root_.guard, if_pos' hpart, Traceful.run_pure] at htr₀b; subst htr₀b
  rw [Traceful.run_pure] at hp₀b hval₀b; cases hp₀b; subst htr₁
  rw [hval₀a, hval₀b] at hrest hval₁
  obtain ⟨_, tr₂, hgd₁, htr₂, hp₂, hval₂⟩ := bind_some_inv hrest
  have hkind : ls'.state.kind = kind := guard_some_inv hgd₁
  rw [_root_.guard, if_pos' hkind, Traceful.run_pure] at htr₂; subst htr₂
  rw [Traceful.run_pure] at hp₂ hval₂; cases hp₂
  rcases ls' with ⟨p', k', sk'⟩
  dsimp only at hpart hkind; subst hpart; subst hkind
  exact ⟨hat, hval₁.trans hval₂⟩

theorem lookupIdentity_some_inv {tr : ExecTrace} {p : Participant} {i : Nat} {ik vk : DY.Bytes}
    (h : ((DY.Libsignal.PQXDH.lookupIdentity p i).run tr).1 = some (ik, vk)) :
    ∃ honest, tr.at? i = some (EvP (.IdentityRegistered p ik vk honest)) ∧
      ((DY.Libsignal.PQXDH.lookupIdentity p i).run tr).2.val = tr := by
  unfold DY.Libsignal.PQXDH.lookupIdentity at h ⊢
  obtain ⟨⟨ev⟩, tr₁, he, htr₁, hrest, hval₁⟩ := bind_some_inv h
  obtain ⟨hat, htr_e⟩ := getEntry_some_inv he
  rw [htr_e] at htr₁; subst htr₁
  cases ev with
  | IdentityRegistered q ik' vk' honest =>
    dsimp only at hrest hval₁
    obtain ⟨_, tr₂, hgd, htr₂, hp, hval₂⟩ := bind_some_inv hrest
    have hpq : q = p := guard_some_inv hgd
    rw [_root_.guard, if_pos' hpq, Traceful.run_pure] at htr₂; subst htr₂; subst hpq
    rw [Traceful.run_pure] at hp hval₂
    injection hp with hp'
    injection hp' with hik hvk; subst hik; subst hvk
    exact ⟨honest, hat, hval₁.trans hval₂⟩
  | _ => simp [Traceful.run_failure] at hrest

theorem receiveSignalMsg_some_inv {tr : ExecTrace} {i : Nat} {msg : TRSignalMsg}
    (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg i).run tr).1 = some msg) :
    ∃ raw, tr.at? i = some (NetE raw) ∧ parseTrSignalMsg raw = some msg ∧
      msg.version = DY.Libsignal.TripleRatchet.messageVersion ∧
      ((DY.Libsignal.TripleRatchet.receiveSignalMsg i).run tr).2.val = tr := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h ⊢
  obtain ⟨raw, tr₁, hm, htr₁, hrest, hval₁⟩ := bind_some_inv h
  obtain ⟨hat, htr_e⟩ := receiveMessage_some_inv hm
  rw [htr_e] at htr₁; subst htr₁
  rcases hp : parseTrSignalMsg raw with _ | m <;> rw [hp] at hrest hval₁
  · simp [Traceful.run_failure] at hrest
  · dsimp only at hrest hval₁
    obtain ⟨_, tr₂, hgd, htr₂, hpure, hval₂⟩ := bind_some_inv hrest
    have hv : m.version = DY.Libsignal.TripleRatchet.messageVersion := guard_some_inv hgd
    rw [_root_.guard, if_pos' hv, Traceful.run_pure] at htr₂; subst htr₂
    rw [Traceful.run_pure] at hpure hval₂
    cases hpure
    exact ⟨raw, hat, hp, hv, hval₁.trans hval₂⟩

/-! ## 4. Setup Trace (`b1_setupTr4 "alice" "bob"`) Characterization -/

theorem setupTr4_pqxdhState_eq (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) =
    if i = 19 then some (StP "bob" { kind := .pqPrekey, sk := randTerm 16 64 })
    else if i = 13 then some (StP "bob" { kind := .signedPrekey, sk := randTerm 10 32 })
    else if i = 9 then some (StP "bob" { kind := .identity, sk := randTerm 5 32 })
    else if i = 4 then some (StP "alice" { kind := .identity, sk := randTerm 0 32 })
    else none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState)) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  rw [at?_nil_eq]
  simp only [length_append_eq]
  have hnil : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  rw [hnil]

theorem setupTr4_pqxdhEvent_eq (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
    if i = 18 then some (EvP (.PQPrekeyPublished "bob" (DY.PQKem.kemPk (randTerm 16 64))))
    else if i = 12 then some (EvP (.SignedPrekeyPublished "bob" (DY.DiffieHellman.dhPk (randTerm 10 32))))
    else if i = 6 then some (EvP (.IdentityRegistered "bob" (DY.DiffieHellman.dhPk (randTerm 5 32))
      (DY.Signature.vk (randTerm 5 32)) true))
    else if i = 1 then some (EvP (.IdentityRegistered "alice" (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true))
    else none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  rw [at?_nil_eq]
  simp only [length_append_eq]
  have hnil : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  rw [hnil]

theorem setupTr4_trState_none (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
    (DY.PersistentLocalState.LocalState TRState)) rfl]
  exact at?_nil_eq i

theorem setupTr4_trEvent_none (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
  exact at?_nil_eq i

theorem setupTr4_compEvent_none (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl]
  exact at?_nil_eq i

theorem setupTr4_bobDone_nil :
    bobDoneBaseKeys (b1_setupTr4 "alice" "bob") = [] := by
  unfold bobDoneBaseKeys
  rw [List.filterMap_eq_nil_iff]
  intro i _
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, setupTr4_pqxdhEvent_eq]
  by_cases h18 : i = 18 <;> simp [h18]
  by_cases h12 : i = 12 <;> simp [h12]
  by_cases h6 : i = 6 <;> simp [h6]
  by_cases h1 : i = 1 <;> simp [h1]

/-! ## 5. Step 0 (`ev0`, `alice init`) Pinning -/

theorem getMessageSentAt_of_at?_net {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.at? i = some (NetE b)) : tr.getMessageSentAt i = some b := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, h]

theorem forall₂_append_inv {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys₁ ys₂ : List β},
      List.Forall₂ R xs (ys₁ ++ ys₂) →
      ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂
  | xs, [], _ys₂, h => ⟨[], xs, rfl, .nil, h⟩
  | _ :: _, _ :: _, _, .cons hr hrest =>
    let ⟨xs₁, xs₂, heq, h1, h2⟩ := forall₂_append_inv hrest
    ⟨_ :: xs₁, xs₂, congrArg (_ :: ·) heq, .cons hr h1, h2⟩

private theorem drawsMatch_aliceDraws_coins0
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {done : Option Nat} {t₀ : Nat} {vis : List VisEntry}
    (hgwf : GhostWF g vis)
    (hsub : ∀ v ∈ aliceDraws done [randTerm t₀ 32, randTerm (t₀ + 1) 32, randTerm (t₀ + 2) 32],
      v ∈ vis)
    (hdm : DrawsMatch compI7003 r S g
      (aliceDraws done [randTerm t₀ 32, randTerm (t₀ + 1) 32, randTerm (t₀ + 2) 32]) coins0Bytes) :
    gamma compI7003 S g (randTerm t₀ 32) = ek0Bytes ∧
    gamma compI7003 S g (randTerm (t₀ + 1) 32) = ent0Bytes ∧
    gamma compI7003 S g (randTerm (t₀ + 2) 32) = dhsA0Bytes := by
  set ek := randTerm t₀ 32
  set ent := randTerm (t₀ + 1) 32
  set dhs := randTerm (t₀ + 2) 32
  obtain ⟨pieces, _, hpref, hf2⟩ := hdm
  dsimp only [aliceDraws, List.take] at hf2 hsub
  rcases pieces with _ | ⟨p0, pcs_tail⟩
  · cases hf2
  cases hf2 with
  | cons hbm0 hf2_rest =>
    obtain ⟨pcs_mid, pcs_end, htail, hf_mid, hf_end⟩ := forall₂_append_inv hf2_rest
    subst htail
    rcases pcs_end with _ | ⟨p33, _ | _⟩
    · cases hf_end
    · cases hf_end with
      | cons hbm33 hf_nil =>
        dsimp only [BytesMatchEntry, rngEntry, List.map] at hbm0 hbm33
        have hp0_eq : gamma compI7003 S g ek = p0 := List.singleton_injective hbm0.2
        have hp33_eq : gamma compI7003 S g dhs = p33 := List.singleton_injective hbm33.2
        have hp0_len : (gamma compI7003 S g ek).length = 32 := by
          rw [gamma_randTerm_pos S g t₀ 32 (by decide)]
          exact hgwf.1 (rngEntry ek) (hsub _ List.mem_cons_self) rfl t₀ 32 (by decide)
            (by simp [rngEntry, ek])
        have hp33_len : (gamma compI7003 S g dhs).length = 32 := by
          rw [gamma_randTerm_pos S g (t₀ + 2) 32 (by decide)]
          refine hgwf.1 { rngEntry dhs with anchor := done } (hsub _ ?_) rfl (t₀ + 2) 32 (by decide)
            (by simp [rngEntry, dhs])
          exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp))
        have hmid_len : pcs_mid.length = 32 := by
          simpa [kyberCoinEntries] using hf_mid.length_eq
        have hmid_each : ∀ j : Fin 32,
            (pcs_mid[j.1]'(by omega)).length = 4 ∧
            (gamma compI7003 S g ent).length = 32 ∧
            (pcs_mid[j.1]'(by omega)).head? = (gamma compI7003 S g ent)[j.1]? := by
          intro j
          have hj := (List.forall₂_iff_get.mp hf_mid).2 j.1 (by omega)
            (by simp [kyberCoinEntries])
          simp only [kyberCoinEntries, List.get_eq_getElem, List.getElem_map,
            List.getElem_range] at hj
          obtain ⟨_, hlen4, t', ht', hlen32, hhd⟩ := hj
          have hteq : t' = ent := (List.singleton_injective (by simpa using ht')).symm
          subst hteq
          exact ⟨hlen4, hlen32, hhd⟩
        have hflat_mid_len : pcs_mid.flatten.length = 128 := by
          have hmap : pcs_mid.map List.length = List.replicate 32 4 := by
            apply List.ext_getElem
            · simp [hmid_len]
            · intro i hi1 hi2
              rw [List.length_map, hmid_len] at hi1
              rw [List.getElem_map, List.getElem_replicate]
              exact (hmid_each ⟨i, hi1⟩).1
          rw [List.length_flatten, hmap, List.sum_replicate, smul_eq_mul]
        have hp0_l : p0.length = 32 := hp0_eq ▸ hp0_len
        have hp33_l : p33.length = 32 := hp33_eq ▸ hp33_len
        have hflat_eq : p0 ++ pcs_mid.flatten ++ p33 = coins0Bytes := by
          obtain ⟨rem, hrem⟩ := hpref
          have hlen := congrArg List.length hrem
          simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil,
            List.length_append, hp0_l, hflat_mid_len, hp33_l, coins_secret_indices.1] at hlen
          have hrem_nil : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hrem_nil
          simpa [List.append_assoc] using hrem
        have hp0_val : p0 = ek0Bytes := by
          have ht := congrArg (List.take 32) hflat_eq
          rw [List.append_assoc, List.take_left' hp0_l, coins_secret_indices.2.1] at ht
          exact ht
        have hp33_val : p33 = dhsA0Bytes := by
          have hd := congrArg (fun l => (l.drop 160).take 32) hflat_eq
          have h160 : (p0 ++ pcs_mid.flatten).length = 160 := by
            rw [List.length_append, hp0_l, hflat_mid_len]
          rw [List.drop_left' h160, List.take_of_length_le (by omega), coins_secret_indices.2.2.2.1] at hd
          exact hd
        have hent_len : (gamma compI7003 S g ent).length = 32 := (hmid_each ⟨0, by decide⟩).2.1
        have hmid_get : ∀ j : Fin 32, (pcs_mid.flatten)[4 * j.1]? = (pcs_mid[j.1]'(by omega)).head? := by
          have h4 : ∀ (l : List HwBytes), (∀ x ∈ l, x.length = 4) → ∀ k : Nat, (hk : k < l.length) →
              l.flatten[4 * k]? = (l[k]'hk).head? := by
            intro l hl
            induction l with
            | nil => intro k hk; cases hk
            | cons x xs ih =>
              intro k hk
              cases k with
              | zero =>
                have hx4 : x.length = 4 := hl x List.mem_cons_self
                rcases x with _ | ⟨b0, _⟩
                · cases hx4
                · rfl
              | succ k' =>
                have hx4 : x.length = 4 := hl x List.mem_cons_self
                simp only [List.flatten_cons]
                have hmul : 4 * (k' + 1) = x.length + 4 * k' := by omega
                rw [hmul, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
                exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) k' (by simp at hk; omega)
          intro j
          refine h4 pcs_mid (fun x hx => ?_) j.1 (by omega)
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          exact (hmid_each ⟨i, by omega⟩).1
        have hent_val : gamma compI7003 S g ent = ent0Bytes := by
          rw [← coins_secret_indices.2.2.1]
          apply List.ext_getElem
          · simp [hent_len]
          · intro j hj1 hj2
            rw [List.getElem_ofFn]
            have heq_opt : some ((gamma compI7003 S g ent)[j]'hj1) = coins0Bytes[32 + 4 * j]? := by
              rw [← List.getElem?_eq_getElem, ← (hmid_each ⟨j, by omega⟩).2.2,
                  ← hmid_get ⟨j, by omega⟩, ← hflat_eq,
                  List.append_assoc, List.getElem?_append_right (by rw [hp0_l]; omega)]
              have hsub32 : 32 + 4 * j - p0.length = 4 * j := by omega
              rw [hsub32, List.getElem?_append_left (by rw [hflat_mid_len]; omega)]
            have hc_lt : 32 + 4 * j < coins0Bytes.length := by rw [coins_secret_indices.1]; omega
            rw [List.getElem?_eq_getElem hc_lt] at heq_opt
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc_lt, Option.getD_some]
            exact Option.some.inj heq_opt
        exact ⟨hp0_eq.trans hp0_val, hent_val, hp33_eq.trans hp33_val⟩
    · cases hf_end with
      | cons _ hf_rest2 => cases hf_rest2

attribute [local irreducible] ByteSpecs.hmacWith

theorem compLookupDh_secret_pub {s : HwBytes} {i j : Fin 6}
    (hs : compSecretIdx (clamp s) = some i) :
    compLookupDh (clamp s) (compPubOfIdx j) = compDhByIdx i j := by
  change compLookupDh (clamp s) (compPubOfOpt (some j)) = compDhByIdx i j
  unfold compLookupDh
  simp only [compPubOfOpt_not_lowOrder (some j), Bool.false_eq_true, ↓reduceIte,
    hs, compPointIdx_compPubOfOpt (some j)]

theorem gamma_pqxdhKdf_eq (S : OpaqueSymbolSemantics) (g : Ghost) (ikm : DY.Bytes)
    {ikmB prkB rkB ckB pqrB : HwBytes}
    (hikm : gamma compI7003 S g ikm = ikmB)
    (hprk : hmacWith F7 (List.replicate 32 0#8) ikmB = prkB)
    (hrk : hmacWith F7 prkB (infoPqxdhBytes ++ [0x01#8]) = rkB)
    (hck : hmacWith F7 prkB (rkB ++ infoPqxdhBytes ++ [0x02#8]) = ckB)
    (hpqr : hmacWith F7 prkB (ckB ++ infoPqxdhBytes ++ [0x03#8]) = pqrB) :
    gamma compI7003 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk = rkB ∧
    gamma compI7003 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck = ckB ∧
    gamma compI7003 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).pqr = pqrB := by
  have hz : ofByteArray (ByteArray.mk (Array.replicate 32 0)) = List.replicate 32 0#8 := by decide
  have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
  have hb2 : ofByteArray (ByteArray.mk #[2]) = [0x02#8] := by decide
  have hb3 : ofByteArray (ByteArray.mk #[3]) = [0x03#8] := by decide
  have hg_prk : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hmac
      DY.Libsignal.TripleRatchet.zeroSalt ikm) = prkB := by
    show gamma compI7003 S g (DY.KdfExtract.kdfExtract DY.Libsignal.TripleRatchet.zeroSalt ikm) = prkB
    unfold DY.Libsignal.TripleRatchet.zeroSalt
    rw [gamma_kdfExtract, gamma_literalToBytes, hz, hikm, hprk]
  have hg_lbl : gamma compI7003 S g DY.Libsignal.PQXDH.pqxdhLabel = infoPqxdhBytes := by
    unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit
    rw [gamma_literalToBytes, ofByteArray_info_labels.1]
  have hg_rk : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hkdfBlock1
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      DY.Libsignal.PQXDH.pqxdhLabel) = rkB := by
    show gamma compI7003 S g (DY.KdfExtract.kdfExtract
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel
        (DY.Literal.literalToBytes (ByteArray.mk #[1])))) = rkB
    rw [gamma_kdfExtract, hg_prk, gamma_concat, hg_lbl, gamma_literalToBytes, hb1, hrk]
  have hg_ck : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hkdfBlock2
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      DY.Libsignal.PQXDH.pqxdhLabel) = ckB := by
    show gamma compI7003 S g (DY.KdfExtract.kdfExtract
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.hkdfBlock1
        (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
        DY.Libsignal.PQXDH.pqxdhLabel)
        (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel
          (DY.Literal.literalToBytes (ByteArray.mk #[2]))))) = ckB
    rw [gamma_kdfExtract, hg_prk, gamma_concat, hg_rk, gamma_concat, hg_lbl,
        gamma_literalToBytes, hb2, ← List.append_assoc, hck]
  have hg_pqr : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hkdfBlock3
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      DY.Libsignal.PQXDH.pqxdhLabel) = pqrB := by
    show gamma compI7003 S g (DY.KdfExtract.kdfExtract
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.hkdfBlock2
        (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm)
        DY.Libsignal.PQXDH.pqxdhLabel)
        (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel
          (DY.Literal.literalToBytes (ByteArray.mk #[3]))))) = pqrB
    rw [gamma_kdfExtract, hg_prk, gamma_concat, hg_ck, gamma_concat, hg_lbl,
        gamma_literalToBytes, hb3, ← List.append_assoc, hpqr]
  exact ⟨hg_rk, hg_ck, hg_pqr⟩

structure AlicePin0 (S : OpaqueSymbolSemantics) (g : Ghost) (tr₀ : ExecTrace)
    (o : AliceHandshakeOut) (stA₀ : TRState) : Prop where
  st_def : stA₀ = aliceSt "bob" o (randTerm (tr₀.length + 2) 32)
  pqr_eq : gamma compI7003 S g o.keys.pqr = pqrBytes
  ek_eq : gamma compI7003 S g o.ek = compPubOfIdx 3
  ct_eq : gamma compI7003 S g o.ct = kyberCt0Bytes
  rk_eq : gamma compI7003 S g stA₀.rk = rk1Bytes
  cks_eq : gamma compI7003 S g stA₀.cks = cksA0Bytes
  dhs_eq : gamma compI7003 S g stA₀.dhs = dhsA0Bytes
  dhs_pk_eq : gamma compI7003 S g (DY.DiffieHellman.dhPk stA₀.dhs) = compPubOfIdx 4
  myIk_eq : gamma compI7003 S g stA₀.myIk = ecKey (compPubOfIdx 0)
  peerIk_eq : gamma compI7003 S g stA₀.peerIk = ecKey (compPubOfIdx 1)

theorem pin_step0_init
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pre₀ : List Step} {s₀ : Step} {v₀ : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hgs : GhostAndSemMatchSetup compI7003 r S g)
    (hgwf : GhostWF g v₀)
    (hinv₀ : ∀ x ∈ pre₀, x.cls = .invisible)
    (hrm₀ : RunMatches compI7003 r S g (runSteps pre₀ (setupTrace r)) s₀ ev0 v₀ none) :
    let tr₀ := runSteps pre₀ (setupTrace r)
    ∃ spkPk pqPk,
      s₀.next tr₀ = aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk ∧
      AlicePin0 S g tr₀
        (aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)
        (aliceSt "bob" (aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)
          (randTerm (tr₀.length + 2) 32)) := by
  intro tr₀
  obtain ⟨_, hb_id, _, _⟩ := setup_ids_7003 hf
  obtain ⟨hcls, hparty, hfits, hpeer, hok, _, hv_eq, inp, drs, outs, hv_split,
    hinp, hdrs, houts, _, _⟩ := hrm₀
  cases s₀ with
  | aliceStart a b idH regB bh =>
    have ha : a = "alice" := Option.some.inj hparty
    subst ha
    dsimp only [Step.MatchesSetupPeer] at hpeer
    rw [hb_id] at hpeer; subst hpeer
    have hok' : ((DY.Libsignal.Composed.aliceStart "alice" "bob" idH regB bh).run tr₀).1.isSome = true := by
      dsimp only [Step.ok, Step.toInput] at hok
      erw [stepIn_ok] at hok
      exact hok
    obtain ⟨n_ret, hrun⟩ := isSome_iff_exists.mp hok'
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline] at hrun
    obtain ⟨o_hs, tr_hs, hhs, _, _⟩ := bind_some_inv hrun
    unfold DY.Libsignal.PQXDH.aliceHandshake at hhs
    obtain ⟨ikA, _, hik, htr_ik, hhs1, _⟩ := bind_some_inv hhs
    obtain ⟨hat_ik, htr_ik'⟩ := getKey_some_inv hik; rw [htr_ik'] at htr_ik; subst htr_ik
    obtain ⟨⟨ikBPk, vkB⟩, _, hreg, htr_reg, hhs2, _⟩ := bind_some_inv hhs1
    obtain ⟨honB, hat_reg, htr_reg'⟩ := lookupIdentity_some_inv hreg; rw [htr_reg'] at htr_reg; subst htr_reg
    obtain ⟨spkPk, _, hspk, htr_spk, hhs3, _⟩ := bind_some_inv hhs2
    obtain ⟨hat_spk, htr_spk'⟩ := receiveMessage_some_inv hspk; rw [htr_spk'] at htr_spk; subst htr_spk
    obtain ⟨spkSig, _, hss, htr_ss, hhs4, _⟩ := bind_some_inv hhs3
    obtain ⟨hat_ss, htr_ss'⟩ := receiveMessage_some_inv hss; rw [htr_ss'] at htr_ss; subst htr_ss
    obtain ⟨pqPk, _, hpq, htr_pq, hhs5, _⟩ := bind_some_inv hhs4
    obtain ⟨hat_pq, htr_pq'⟩ := receiveMessage_some_inv hpq; rw [htr_pq'] at htr_pq; subst htr_pq
    obtain ⟨pqSig, _, hps, htr_ps, hhs6, _⟩ := bind_some_inv hhs5
    obtain ⟨hat_ps, htr_ps'⟩ := receiveMessage_some_inv hps; rw [htr_ps'] at htr_ps; subst htr_ps
    obtain ⟨_, _, hgd1, htr_g1, hhs7, _⟩ := bind_some_inv hhs6
    have hv1 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spkPk) spkSig = true :=
      guard_some_inv hgd1
    rw [_root_.guard, if_pos' hv1, Traceful.run_pure] at htr_g1; subst htr_g1
    obtain ⟨_, _, hgd2, htr_g2, hhs8, _⟩ := bind_some_inv hhs7
    have hv2 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqPk) pqSig = true :=
      guard_some_inv hgd2
    rw [_root_.guard, if_pos' hv2, Traceful.run_pure] at htr_g2; subst htr_g2
    have hikA_eq : ikA = randTerm 0 32 := by
      dsimp only [tr₀] at hat_ik
      rw [runSteps_invisible_at?_pqxdhState hinv₀, setupTrace_eq_7003 hf, setupTr4_pqxdhState_eq] at hat_ik
      split at hat_ik <;> try (split at hat_ik <;> try (split at hat_ik <;> try (split at hat_ik)))
      all_goals simp [StP] at hat_ik
      exact hat_ik.symm
    subst hikA_eq
    have hikB_eq : ikBPk = DY.DiffieHellman.dhPk (randTerm 5 32) := by
      dsimp only [tr₀] at hat_reg
      have hat_ev : (tr₀.getEventAt PQXDHEvent regB) =
          some (.IdentityRegistered "bob" ikBPk vkB honB) := by
        rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat_reg]
      rw [runSteps_invisible_getEventAt_pqxdh hinv₀, setupTrace_eq_7003 hf,
          Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, setupTr4_pqxdhEvent_eq] at hat_ev
      by_cases h18 : regB = 18 <;> simp [h18, EvP] at hat_ev
      by_cases h12 : regB = 12 <;> simp [h12, EvP] at hat_ev
      by_cases h6 : regB = 6 <;> simp [h6, EvP] at hat_ev
      · exact hat_ev.1.symm
      · by_cases h1 : regB = 1 <;> simp [h1, EvP] at hat_ev
    subst hikB_eq
    have hopk_none : bh.opk = none := by
      cases hopk : bh.opk with
      | none => rfl
      | some oi =>
        rw [hopk] at hhs8
        dsimp only at hhs8
        obtain ⟨opkPk, _, hopk_m, _, _, _⟩ := bind_some_inv hhs8
        obtain ⟨hat_opk, _⟩ := receiveMessage_some_inv hopk_m
        dsimp only [tr₀] at *
        dsimp only [stepView] at hv_eq
        rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hv_eq
        dsimp only [aliceVis] at hv_eq
        rw [List.cons_append] at hv_eq
        have hinp_eq : inp = ⟨.recv, received (runSteps pre₀ (setupTrace r))
            ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
            .bundle, none⟩ := (List.cons.inj (hv_split.symm.trans hv_eq)).1
        rw [hinp_eq, hopk] at hinp
        simp only [BytesMatchEntry, received, Option.toList, List.cons_append, List.nil_append,
          List.filterMap, tr₀] at hinp hat_spk hat_ss hat_pq hat_ps hat_opk
        rw [getMessageSentAt_of_at?_net hat_spk, getMessageSentAt_of_at?_net hat_ss,
            getMessageSentAt_of_at?_net hat_pq, getMessageSentAt_of_at?_net hat_ps,
            getMessageSentAt_of_at?_net hat_opk] at hinp
        dsimp only [PreKeyBundleLayoutMatches, ev0] at hinp
        rw [bun0Raw_eq] at hinp
        have hb4 : DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte bun0Bytes = some 0#8 :=
          bun0_props.2.1
        rw [hinp.2.2.1] at hb4
        cases hb4
    rw [hopk_none] at hhs8
    dsimp only at hhs8
    obtain ⟨_, _, hp_none, htr_p, hhs9, _⟩ := bind_some_inv hhs8
    rw [Traceful.run_pure] at htr_p; subst htr_p
    obtain ⟨_, tr_ek, hgr_ek, htr_ek, hhs10, _⟩ := bind_some_inv hhs9
    rw [(Runs.genRand tr₀ 32).2] at htr_ek; subst htr_ek
    obtain ⟨_, _, hgd_lo, _, _, _⟩ := bind_some_inv hhs10
    have hlow_b : (!DY.Libsignal.PQXDH.x25519LowOrder spkPk) = true := guard_some_inv hgd_lo
    have hlow : DY.Libsignal.PQXDH.x25519LowOrder spkPk = false := by
      cases hx : DY.Libsignal.PQXDH.x25519LowOrder spkPk <;> simp [hx] at hlow_b ⊢
    have hruns0 := Runs.aliceStart hat_ik hat_reg hat_spk hat_ss hat_pq hat_ps hv1 hv2 hopk_none hlow
    have hnext0 : (Step.aliceStart "alice" "bob" idH regB bh).next tr₀ =
        aliceTr tr₀ "alice" "bob" (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk := by
      dsimp only [Step.next, Step.toInput]
      erw [stepIn_next]
      exact hruns0.2
    refine ⟨spkPk, pqPk, hnext0, ?_⟩
    -- Unpack stepView of s₀ to pin spkPk, pqPk, and random draws
    have hexp0 : exposures tr₀ (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk) = [] := by
      unfold exposures newIndices
      have hlen_tr : (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
          (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).length = tr₀.length + 9 := by
        simp only [aliceTr, aliceTrOpt, length_append_eq, Nat.add_assoc]
      rw [hlen_tr, Nat.add_sub_cancel_left]
      have hpq_nil : (List.range' tr₀.length 9).filterMap
          (pqExposureAt (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
            (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)) = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro j hj
        rw [List.mem_range'_1] at hj
        unfold pqExposureAt
        rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        dsimp only [aliceTr, aliceTrOpt]
        repeat first
          | rw [at?_append_other_eq rfl]
          | rw [at?_append_same_eq (fun _ => rfl)]
        simp only [length_append_eq, Nat.add_assoc]
        by_cases hj5 : j = tr₀.length + 5
        · subst hj5; simp
        · rw [if_neg' hj5, at?_ge_length_eq tr₀ (by omega)]
      have htr_nil : (List.range' tr₀.length 9).filterMap
          (trExposureAt (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
            (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)) = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro j hj
        rw [List.mem_range'_1] at hj
        unfold trExposureAt
        rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
        dsimp only [aliceTr, aliceTrOpt]
        repeat first
          | rw [at?_append_other_eq rfl]
          | rw [at?_append_same_eq (fun _ => rfl)]
        simp only [length_append_eq, Nat.add_assoc]
        by_cases hj6 : j = tr₀.length + 6
        · subst hj6; simp
        · rw [if_neg' hj6, at?_ge_length_eq tr₀ (by omega)]
      rw [hpq_nil, htr_nil]; rfl
    have hnr0 : (newRandoms tr₀ (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)).map (·.1) =
        [randTerm tr₀.length 32, randTerm (tr₀.length + 1) 32, randTerm (tr₀.length + 2) 32] := by
      unfold newRandoms newIndices
      have hlen_tr : (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
          (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).length = tr₀.length + 9 := by
        simp only [aliceTr, aliceTrOpt, length_append_eq, Nat.add_assoc]
      rw [hlen_tr, Nat.add_sub_cancel_left]
      have hat_rnd : ∀ k : Nat, k < 9 →
          ((aliceTr tr₀ "alice" "bob" (randTerm 0 32)
            (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).at? (tr₀.length + k) :
              Option DY.Random.ExecEntryT) =
          if k = 0 ∨ k = 1 ∨ k = 2 then some (RndE 32) else none := by
        intro k hk
        dsimp only [aliceTr, aliceTrOpt]
        repeat first
          | rw [at?_append_other_eq rfl]
          | rw [at?_append_same_eq (fun _ => rfl)]
        simp only [length_append_eq, Nat.add_assoc]
        by_cases hk0 : k = 0
        · subst hk0; simp
        · by_cases hk1 : k = 1
          · subst hk1
            simp [show tr₀.length + 1 ≠ tr₀.length + 2 by omega,
                  show tr₀.length + 1 ≠ tr₀.length by omega]
          · by_cases hk2 : k = 2
            · subst hk2; simp
            · have hne2 : tr₀.length + k ≠ tr₀.length + 2 := by omega
              have hne1 : tr₀.length + k ≠ tr₀.length + 1 := by omega
              have hne0 : tr₀.length + k ≠ tr₀.length := by omega
              rw [if_neg' (by omega : ¬ (k = 0 ∨ k = 1 ∨ k = 2)),
                  if_neg' hne2, if_neg' hne1, if_neg' hne0]
              exact at?_ge_length_eq tr₀ (by omega)
      have hrange : List.range' tr₀.length 9 =
          [tr₀.length + 0, tr₀.length + 1, tr₀.length + 2, tr₀.length + 3, tr₀.length + 4,
           tr₀.length + 5, tr₀.length + 6, tr₀.length + 7, tr₀.length + 8] := by
        simp [List.range', Nat.add_assoc]
      rw [hrange]
      dsimp only [List.filterMap]
      rw [hat_rnd 0 (by decide), hat_rnd 1 (by decide), hat_rnd 2 (by decide),
          hat_rnd 3 (by decide), hat_rnd 4 (by decide), hat_rnd 5 (by decide),
          hat_rnd 6 (by decide), hat_rnd 7 (by decide), hat_rnd 8 (by decide)]
      simp [Option.map, List.map, RndE, Nat.add_zero]
    have houts_nil : outs = [] := by
      simpa [OutputsMatch, ev0] using houts
    subst houts_nil
    rw [List.append_nil] at hv_split
    dsimp only [stepView] at hv_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h), hnext0, hexp0, List.append_nil] at hv_eq
    dsimp only [aliceVis] at hv_eq
    rw [hnr0] at hv_eq
    have hinp_eq := (List.cons.inj (hv_split.symm.trans hv_eq)).1
    have hdrs_eq := (List.cons.inj (hv_split.symm.trans hv_eq)).2
    subst hinp_eq; subst hdrs_eq
    -- Extract γ spkPk and γ pqPk from PreKeyBundleLayoutMatches
    rw [hopk_none] at hinp
    simp only [BytesMatchEntry, inputKind, ev0, received, Option.toList, List.cons_append,
      List.nil_append, List.filterMap, tr₀] at hinp hat_spk hat_ss hat_pq hat_ps
    rw [getMessageSentAt_of_at?_net hat_spk, getMessageSentAt_of_at?_net hat_ss,
        getMessageSentAt_of_at?_net hat_pq, getMessageSentAt_of_at?_net hat_ps, bun0Raw_eq] at hinp
    dsimp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch] at hinp
    have hg_spk : gamma compI7003 S g spkPk = compPubOfIdx 2 :=
      ecKey_inj (hinp.2.1.2.1.symm.trans bun0_props.2.2.2.1)
    have hg_pqpk : gamma compI7003 S g pqPk = setup7003.kyberPk :=
      kyberKey_inj (hinp.2.1.2.2.2.1.symm.trans bun0_props.2.2.2.2.2.1)
    -- Extract γ of the 3 random draws from DrawsMatch
    rw [ev0, coins0Raw_eq] at hdrs
    obtain ⟨hg_ek0, hg_ent0, hg_dhs0⟩ := drawsMatch_aliceDraws_coins0 hgwf
      (fun v hv => by rw [hv_eq]; exact List.mem_cons_of_mem _ hv) hdrs
    obtain ⟨hg_s0, hg_s5, _, _, hg_pk0, hg_pk5, _, _, _⟩ := gamma_setup_keys_7003 hf hgs
    -- Evaluate AliceHandshakeOut and aliceSt under γ
    set o := aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk
    have h_rnd_eq : ∀ t n, rnd t n = randTerm t n := fun _ _ => rfl
    have h_crnd_eq : ∀ t n,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd t n = randTerm t n :=
      fun _ _ => rfl
    have hg_ek_pk : gamma compI7003 S g o.ek = compPubOfIdx 3 := by
      dsimp only [o, aliceOut, Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
      rw [h_crnd_eq, gamma_dhPk, hg_ek0]
      unfold compLookupPub
      rw [coins_secret_indices.2.2.2.2.2.2.2.1]; rfl
    have hent_len :
        (gamma compI7003 S g
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd (tr₀.length + 1) 32)).length = 32 := by
      rw [h_crnd_eq, hg_ent0]; decide
    have hg_ct : gamma compI7003 S g o.ct = kyberCt0Bytes := by
      dsimp only [o, aliceOut, Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement]
      rw [gamma_kemEncap_fst_32 S g pqPk _ hent_len, h_crnd_eq, hg_ent0,
          coins_secret_indices.2.2.2.2.2.2.2.2.2.2.1]
      decide
    have hg_ss : gamma compI7003 S g
        (DY.PQKem.kemEncap pqPk
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd (tr₀.length + 1) 32)).2 =
        kyberSs0Bytes := by
      rw [gamma_kemEncap_snd_32 S g pqPk _ hent_len, h_crnd_eq, hg_ent0,
          coins_secret_indices.2.2.2.2.2.2.2.2.2.2.1]
      decide
    have hdh1 : gamma compI7003 S g (agree spkPk (randTerm 0 32)) = compDhByIdx 2 0 := by
      rw [gamma_agree, hg_s0, hg_spk,
          compLookupDh_secret_pub coins_secret_indices.2.2.2.2.1, compDhByIdx_comm]
    have hdh2 : gamma compI7003 S g
        (agree (DY.DiffieHellman.dhPk (randTerm 5 32))
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd tr₀.length 32)) =
        compDhByIdx 1 3 := by
      rw [h_crnd_eq, gamma_agree, hg_ek0, hg_pk5,
          compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.2.1, compDhByIdx_comm]
    have hdh3 : gamma compI7003 S g
        (agree spkPk
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd tr₀.length 32)) =
        compDhByIdx 2 3 := by
      rw [h_crnd_eq, gamma_agree, hg_ek0, hg_spk,
          compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.2.1, compDhByIdx_comm]
    have hg_ikm : gamma compI7003 S g
        (DY.Libsignal.PQXDH.pqxdhIkm (agree spkPk (randTerm 0 32))
          (agree (DY.DiffieHellman.dhPk (randTerm 5 32))
            (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd tr₀.length 32))
          (agree spkPk
            (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd tr₀.length 32)) none
          (DY.PQKem.kemEncap pqPk
            (Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd (tr₀.length + 1) 32)).2) =
        List.replicate 32 0xff#8 ++ compDhByIdx 2 0 ++ compDhByIdx 1 3 ++ compDhByIdx 2 3 ++
          kyberSs0Bytes := by
      unfold DY.Libsignal.PQXDH.pqxdhIkm DY.Libsignal.PQXDH.discontinuity
      simp only [gamma_concat, gamma_literalToBytes, hdh1, hdh2, hdh3, hg_ss, List.append_assoc]
      have hdisc : ofByteArray (ByteArray.mk (Array.replicate 32 0xFF)) = List.replicate 32 0xff#8 := by
        decide
      rw [hdisc]
    obtain ⟨hg_rk0, hg_ck0, hg_pqr⟩ :
        gamma compI7003 S g o.keys.rk = rk0Bytes ∧
        gamma compI7003 S g o.keys.ck = ck0Bytes ∧
        gamma compI7003 S g o.keys.pqr = pqrBytes := by
      dsimp only [o, aliceOut, Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement, Option.map]
      exact gamma_pqxdhKdf_eq S g _ hg_ikm
        pqxdh_and_mac_facts_7003.1
        pqxdh_and_mac_facts_7003.2.1
        pqxdh_and_mac_facts_7003.2.2.1
        pqxdh_and_mac_facts_7003.2.2.2.1
    -- Now evaluate createChain o.keys.rk o.spk dhsA
    set dhsA := randTerm (tr₀.length + 2) 32
    have hg_dhA : gamma compI7003 S g (agree spkPk dhsA) = compDhByIdx 2 4 := by
      rw [gamma_agree, hg_dhs0, hg_spk,
          compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.2.2.1, compDhByIdx_comm]
    have hg_prkA1 : gamma compI7003 S g
        (DY.Libsignal.TripleRatchet.hmac o.keys.rk (agree spkPk dhsA)) = prkA1Bytes := by
      unfold DY.Libsignal.TripleRatchet.hmac
      rw [gamma_kdfExtract, hg_rk0, hg_dhA]
      exact ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hg_rk1 : gamma compI7003 S g (createChain o.keys.rk spkPk dhsA).1 = rk1Bytes := by
      show gamma compI7003 S g (DY.KdfExtract.kdfExtract
        (DY.Libsignal.TripleRatchet.hmac o.keys.rk (agree spkPk dhsA))
        (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
          (DY.Literal.literalToBytes (ByteArray.mk #[1])))) = rk1Bytes
      unfold DY.Libsignal.TripleRatchet.lit
      rw [gamma_kdfExtract, hg_prkA1, gamma_concat, gamma_literalToBytes, gamma_literalToBytes,
          ofByteArray_info_labels.2.1]
      have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
      rw [hb1]
      exact ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.1
    have hg_cks0 : gamma compI7003 S g (createChain o.keys.rk spkPk dhsA).2 = cksA0Bytes := by
      show gamma compI7003 S g (DY.KdfExtract.kdfExtract
        (DY.Libsignal.TripleRatchet.hmac o.keys.rk (agree spkPk dhsA))
        (DY.Concat.concat (createChain o.keys.rk spkPk dhsA).1
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
            (DY.Literal.literalToBytes (ByteArray.mk #[2]))))) = cksA0Bytes
      unfold DY.Libsignal.TripleRatchet.lit
      rw [gamma_kdfExtract, hg_prkA1, gamma_concat, hg_rk1, gamma_concat,
          gamma_literalToBytes, gamma_literalToBytes, ofByteArray_info_labels.2.1]
      have hb2 : ofByteArray (ByteArray.mk #[2]) = [0x02#8] := by decide
      rw [hb2, ← List.append_assoc]
      exact ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1
    have hg_dhs_pk : gamma compI7003 S g (DY.DiffieHellman.dhPk dhsA) = compPubOfIdx 4 := by
      rw [gamma_dhPk, hg_dhs0]; unfold compLookupPub
      rw [coins_secret_indices.2.2.2.2.2.2.2.2.1]; rfl
    have hg_myIk : gamma compI7003 S g (serializedIk (DY.DiffieHellman.dhPk (randTerm 0 32))) =
        ecKey (compPubOfIdx 0) := by
      unfold serializedIk DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
      rw [gamma_concat, gamma_literalToBytes, hg_pk0]; rfl
    have hg_peerIk : gamma compI7003 S g (serializedIk (DY.DiffieHellman.dhPk (randTerm 5 32))) =
        ecKey (compPubOfIdx 1) := by
      unfold serializedIk DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
      rw [gamma_concat, gamma_literalToBytes, hg_pk5]; rfl
    exact ⟨rfl, hg_pqr, hg_ek_pk, hg_ct, hg_rk1, hg_cks0, hg_dhs0, hg_dhs_pk, hg_myIk, hg_peerIk⟩
  | _ => simp [Step.FitsCmd, ev0] at hfits

/-! ## 6. Step 1 (`ev1_m1` / `ev1_m2`, `alice send`) Pinning -/

/-- General trace shape of `messageEncrypt me stH cl (tr.length + 2)`. -/
def encTrCl (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl : Nat) :
    ExecTrace :=
  let m := randTerm tr.length 32
  let coins := randTerm (tr.length + 1) cl
  let pq := (DY.Spqr.spqrSend st.spqr coins).2.1
  ((((((tr.append (RndE 32)).append (RndE cl)).append
    (NetE pq)).append
    (EvT (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

theorem messageEncrypt_pin_aux {tr : ExecTrace} {me : Participant}
    {stH cl pqH : Nat}
    (hlok : (Step.messageEncrypt me stH cl pqH).LocalOk tr)
    (hok : (Step.messageEncrypt me stH cl pqH).ok tr = true) :
    ∃ st, tr.at? stH = some (StT me st) ∧ pqH = tr.length + 2 ∧
      (Step.messageEncrypt me stH cl pqH).next tr = encTrCl tr me stH st cl ∧
      lastSent tr ((Step.messageEncrypt me stH cl pqH).next tr) =
        some (encMsg st (randTerm (tr.length + 1) cl)
          (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1
          (randTerm tr.length 32)) ∧
      exposures tr ((Step.messageEncrypt me stH cl pqH).next tr) = [] ∧
      encDraws (newRandoms tr ((Step.messageEncrypt me stH cl pqH).next tr)) =
        ⟨.pt, [randTerm tr.length 32], .single, none⟩ ::
          (if cl = 0 then [] else [rngEntry (randTerm (tr.length + 1) cl)]) := by
  have hok' : ((DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pqH).run tr).1.isSome = true := by
    dsimp only [Step.ok, Step.toInput] at hok
    erw [stepIn_ok] at hok
    exact hok
  obtain ⟨_, hrun⟩ := isSome_iff_exists.mp hok'
  unfold DY.Libsignal.TripleRatchet.messageEncrypt at hrun
  obtain ⟨st, _, hst, htr_st, hr1, _⟩ := bind_some_inv hrun
  obtain ⟨hat_st, htr_st'⟩ := getLocalState_tr_some_inv hst; rw [htr_st'] at htr_st; subst htr_st
  obtain ⟨_, _, hgd_ns, htr_ns, hr2, _⟩ := bind_some_inv hr1
  have hns : st.ns ≠ u32Max := guard_some_inv hgd_ns
  rw [_root_.guard, if_pos' hns, Traceful.run_pure] at htr_ns; subst htr_ns
  obtain ⟨m, tr_m, hgm, htr_m, hr3, _⟩ := bind_some_inv hr2
  rw [(Runs.genRand tr 32).1] at hgm; injection hgm with hm_eq; subst hm_eq
  rw [(Runs.genRand tr 32).2] at htr_m; subst htr_m
  obtain ⟨coins, tr_c, hgc, htr_c, hr4, _⟩ := bind_some_inv hr3
  rw [(Runs.genRand (tr.append (RndE 32)) cl).1] at hgc; injection hgc with hc_eq; subst hc_eq
  rw [(Runs.genRand (tr.append (RndE 32)) cl).2] at htr_c; subst htr_c
  obtain ⟨_, tr_k, hsk, htr_k, hr5, _⟩ := bind_some_inv hr4
  rw [(Runs.sendMessage _ _).2] at htr_k; subst htr_k
  obtain ⟨pq, _, hrpq, _, _, _⟩ := bind_some_inv hr5
  obtain ⟨hat_pq, _⟩ := receiveMessage_some_inv hrpq
  have hpq_eq : pqH = tr.length + 2 := by
    rcases hlok.2 with h2 | h3
    · exact h2
    · change pqH = tr.length + 3 at h3
      subst h3
      have hge_none {E : Type} [ExecTraceTypes.Has E] {t : ExecTrace} {i : Nat} {e : E}
          (hle : t.length ≤ i) (hat : t.at? i = some e) : False := by
        rw [at?_ge_length_eq t hle] at hat; cases hat
      exact False.elim (hge_none (by simp [RndE, NetE, length_append_eq]) hat_pq)
  subst hpq_eq
  -- Now run TripleRatchet.messageEncrypt forward cleanly
  have hlen1 : (tr.append (RndE 32)).length = tr.length + 1 := length_append_eq _ _
  have h_rnd_eq : ∀ t n, rnd t n = randTerm t n := fun _ _ => rfl
  have hpq_at : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1)).at? (tr.length + 2) =
      some (NetE (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1) := by
    rw [at?_append_same_eq (fun _ => rfl), if_pos' (by simp [length_append_eq, Nat.add_assoc])]
  have hruns_enc : Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl (tr.length + 2)) tr
      (tr.length + 6) (encTrCl tr me stH st cl) := by
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    refine Runs.bind (Runs.getLocalState hat_st) ?_
    refine Runs.bind (Runs.guard _ hns) ?_
    refine Runs.bind (Runs.genRand _ _) ?_
    refine Runs.bind (Runs.genRand _ _) ?_
    refine Runs.bind (Runs.sendMessage _ _) ?_
    rw [hlen1, h_rnd_eq, h_rnd_eq]
    refine Runs.bind (Runs.receiveMessage hpq_at) ?_
    refine Runs.bind (Runs.logEvent _ _) ?_
    refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
    refine ⟨?_, ?_⟩
    · rw [(Runs.sendMessage _ _).1]
      simp [RndE, NetE, EvT, StT, length_append_eq, Nat.add_assoc]
    · rw [(Runs.sendMessage _ _).2]
      simp only [encTrCl, encSt, encMsg, RndE, NetE, EvT, StT, length_append_eq]
      dsimp only [kdfCk, DY.Spqr.spqrSend, rnd]
  have hnext : (Step.messageEncrypt me stH cl (tr.length + 2)).next tr = encTrCl tr me stH st cl := by
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    exact hruns_enc.2
  have hlen_enc : (encTrCl tr me stH st cl).length = tr.length + 7 := by
    simp only [encTrCl, length_append_eq, Nat.add_assoc]
  have hls : lastSent tr (encTrCl tr me stH st cl) =
      some (encMsg st (randTerm (tr.length + 1) cl)
        (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1
        (randTerm tr.length 32)) := by
    unfold lastSent
    rw [hlen_enc, if_pos' (by omega), show tr.length + 7 - 1 = tr.length + 6 by omega]
    apply getMessageSentAt_of_at?_net
    dsimp only [encTrCl]
    rw [at?_append_same_eq (fun _ => rfl), if_pos' (by simp [length_append_eq, Nat.add_assoc])]
  have hexp : exposures tr (encTrCl tr me stH st cl) = [] := by
    unfold exposures newIndices
    rw [hlen_enc, Nat.add_sub_cancel_left]
    have hpq_nil : (List.range' tr.length 7).filterMap (pqExposureAt (encTrCl tr me stH st cl)) = [] := by
      rw [List.filterMap_eq_nil_iff]; intro j hj; rw [List.mem_range'_1] at hj
      unfold pqExposureAt; rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      dsimp only [encTrCl]
      repeat rw [at?_append_other_eq rfl]
      rw [at?_ge_length_eq tr (by omega)]
    have htr_nil : (List.range' tr.length 7).filterMap (trExposureAt (encTrCl tr me stH st cl)) = [] := by
      rw [List.filterMap_eq_nil_iff]; intro j hj; rw [List.mem_range'_1] at hj
      unfold trExposureAt; rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
      dsimp only [encTrCl]
      repeat first
        | rw [at?_append_other_eq rfl]
        | rw [at?_append_same_eq (fun _ => rfl)]
      simp only [length_append_eq, Nat.add_assoc]
      by_cases hj4 : j = tr.length + 4
      · subst hj4; simp
      · by_cases hj3 : j = tr.length + 3
        · subst hj3; simp
        · rw [if_neg' hj4, if_neg' hj3, at?_ge_length_eq tr (by omega)]
    rw [hpq_nil, htr_nil]; rfl
  have hnr : newRandoms tr (encTrCl tr me stH st cl) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
    unfold newRandoms newIndices
    rw [hlen_enc, Nat.add_sub_cancel_left]
    have hat_r : ∀ k : Nat, k < 7 →
        ((encTrCl tr me stH st cl).at? (tr.length + k) : Option DY.Random.ExecEntryT) =
        if k = 0 then some (RndE 32) else if k = 1 then some (RndE cl) else none := by
      intro k hk
      dsimp only [encTrCl]
      repeat first
        | rw [at?_append_other_eq rfl]
        | rw [at?_append_same_eq (fun _ => rfl)]
      simp only [length_append_eq, Nat.add_assoc]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · by_cases hk1 : k = 1
        · subst hk1; simp
        · have hne1 : tr.length + k ≠ tr.length + 1 := by omega
          have hne0 : tr.length + k ≠ tr.length := by omega
          rw [if_neg' hk0, if_neg' hk1, if_neg' hne1, if_neg' hne0]
          exact at?_ge_length_eq tr (by omega)
    have hrange : List.range' tr.length 7 =
        [tr.length + 0, tr.length + 1, tr.length + 2, tr.length + 3,
         tr.length + 4, tr.length + 5, tr.length + 6] := by
      simp [List.range', Nat.add_assoc]
    rw [hrange]
    dsimp only [List.filterMap]
    rw [hat_r 0 (by decide), hat_r 1 (by decide), hat_r 2 (by decide),
        hat_r 3 (by decide), hat_r 4 (by decide), hat_r 5 (by decide), hat_r 6 (by decide)]
    simp [Option.map, RndE, Nat.add_zero]
  refine ⟨st, hat_st, rfl, hnext, ?_, ?_, ?_⟩
  · rw [hnext]; exact hls
  · rw [hnext]; exact hexp
  · rw [hnext, hnr]
    dsimp only [encDraws, List.filter]
    rcases cl with _ | cl'
    · rfl
    · rw [if_neg' (Nat.succ_ne_zero cl')]; rfl

theorem drs_outs_of_stepView_send
    {inp : VisEntry} {drs₀ drs outs : List VisEntry} {vo : VisEntry}
    (houts : ∃ v, outs = [v] ∧ v.kind = .send)
    (heq : inp :: (drs ++ outs) = inp :: (drs₀ ++ [vo])) :
    drs = drs₀ ∧ outs = [vo] := by
  have h1 := (List.cons.inj heq).2
  obtain ⟨v, rfl, _⟩ := houts
  have hl := congrArg List.length h1
  simp only [List.length_append, List.length_singleton] at hl
  have hdrs : drs = drs₀ := (List.append_inj h1 (by omega)).1
  subst hdrs
  exact ⟨rfl, List.append_cancel_left h1⟩

theorem pin_step1_encrypt
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₀ : ExecTrace} {spkPk pqPk : DY.Bytes}
    {pre₁ : List Step} {s₁ : Step} {v₁ : List VisEntry}
    {ev1 : RunEvent} {ptBytes outBytes ctBytes wireBytes macBytes msgBytes : HwBytes}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hpin0 : AlicePin0 S g tr₀
      (aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)
      (aliceSt "bob" (aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)
        (randTerm (tr₀.length + 2) 32)))
    (htr₀_trNone : ∀ i, (tr₀.at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none)
    (htr₀_compNone : ∀ i, (tr₀.at? i :
      Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none)
    (hgwf : GhostWF g v₁)
    (hinv₁ : ∀ x ∈ pre₁, x.cls = .invisible)
    (hlok₁ : s₁.LocalOk (runSteps pre₁
      (aliceTr tr₀ "alice" "bob" (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)))
    (hev_party : ev1.party = "alice")
    (hev_cmd : ev1.cmd = .send peerAddrBob)
    (hev_inp : ev1.input = ptBytes)
    (hev_coins : ev1.coins = coins1Bytes)
    (hev_exit : ev1.exit = some (0, outBytes))
    (hwrap : runWrapped ev1 = true)
    (hout_wire : outBytes = preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0))
      (compPubOfIdx 3) kyberCt0Bytes msgBytes)
    (hmsg_len : msgBytes.length = 159)
    (hmsg_split : msgBytes = wireBytes ++ macBytes)
    (hmac_len : macBytes.length = 8)
    (hmac_eq : (hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wireBytes)).take 8 = macBytes)
    (hmac_untag : (hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wireBytes)).take 4 ≠ compTag4)
    (haes_eq : compAesPerm encKey1Bytes iv1Bytes ptBytes = ctBytes)
    (htr_wire : trWireBytes addr1Bytes canonicalVariation
      (WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ctBytes)
      pqMsg1Bytes = wireBytes)
    (hrm₁ : RunMatches compI7003 r S g
      (runSteps pre₁ (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk))
      s₁ ev1 v₁ (some (bundlePreKeyIds bun0Raw))) :
    let tr₁ := runSteps pre₁ (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
      (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)
    let o := aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk
    let stA₀ := aliceSt "bob" o (randTerm (tr₀.length + 2) 32)
    ∃ cl₁,
      SemPinned2 S cl₁ ∧
      s₁.next tr₁ = encTrCl tr₁ "alice" (tr₀.length + 8) stA₀ cl₁ := by
  intro tr₁ o stA₀
  obtain ⟨stH₁, cl₁, pqH₁, w₁, hs₁_eq, hls₁, hwrap_prop, _⟩ :=
    runMatches_filter_send_send hev_cmd hrm₁
  rw [hev_party] at hs₁_eq; subst hs₁_eq
  obtain ⟨st₁, hat_st₁, rfl, hnext₁, hls₁', hexp₁, hedr₁⟩ :=
    messageEncrypt_pin_aux hlok₁ hrm₁.2.2.2.2.1
  -- Identify st₁ = stA₀ and stH₁ = tr₀.length + 8
  have hst₁_pin : stH₁ = tr₀.length + 8 ∧ st₁ = stA₀ := by
    change ((runSteps pre₁ (aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk)).at? stH₁ :
        Option (DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState))) = some (StT "alice" st₁) at hat_st₁
    rw [runSteps_invisible_at?_trState hinv₁] at hat_st₁
    unfold aliceTr aliceTrOpt at hat_st₁
    rw [at?_append_same_eq (fun _ => rfl)] at hat_st₁
    simp only [length_append_eq, Nat.add_assoc] at hat_st₁
    split at hat_st₁
    · next heq =>
      injection hat_st₁ with h1
      injection h1 with h2
      injection h2 with _ hst_eq
      exact ⟨heq, hst_eq.symm⟩
    · repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState)) rfl] at hat_st₁
      rw [htr₀_trNone] at hat_st₁; cases hat_st₁
  obtain ⟨rfl, rfl⟩ := hst₁_pin
  refine ⟨cl₁, ?_, hnext₁⟩
  -- Unpack stepView of s₁
  obtain ⟨ek₁, ct₁, hppk₁, hv_fsend⟩ := hwrap_prop hwrap
  -- Show (ek₁, ct₁) = (o.ek, o.ct) via pendingPreKey on tr₁
  have hppk_eq : ek₁ = o.ek ∧ ct₁ = o.ct := by
    unfold pendingPreKey DY.ExecTrace.getLocalStateAt at hppk₁
    rw [runSteps_invisible_at?_trState hinv₁] at hppk₁
    have hat_s0 : ((aliceTr tr₀ "alice" "bob" (randTerm 0 32)
        (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).at? (tr₀.length + 8) :
        Option (DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState))) = some (StT "alice" stA₀) := by
      unfold aliceTr aliceTrOpt
      rw [at?_append_same_eq (fun _ => rfl), if_pos' (by simp [length_append_eq, Nat.add_assoc])]
      rfl
    rw [hat_s0] at hppk₁
    dsimp only [Option.map, StT] at hppk₁
    unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hppk₁
    split at hppk₁
    · cases hppk₁
    · obtain ⟨ev_pq, hmem_pq, hfind_pq⟩ := List.exists_of_findSome?_eq_some hppk₁
      obtain ⟨idx_hs, _, hfind_hs⟩ := List.mem_filterMap.mp hmem_pq
      rw [runSteps_invisible_getEventAt_comp hinv₁,
          Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hfind_hs
      have hat_hs : ((aliceTr tr₀ "alice" "bob" (randTerm 0 32)
          (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).at? idx_hs :
          Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) =
          if idx_hs = tr₀.length + 7 then
            some (EvC (.HandshakeSession (stA₀.sessionInfo "alice") (tr₀.length + 5)))
          else (tr₀.at? idx_hs : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) := by
        unfold aliceTr aliceTrOpt
        rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl,
            at?_append_same_eq (fun _ => rfl)]
        simp only [length_append_eq, Nat.add_assoc]
        split
        · rfl
        · repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl]
      rw [hat_hs] at hfind_hs
      by_cases hidx_hs : idx_hs = tr₀.length + 7
      · subst hidx_hs
        simp only [↓reduceIte] at hfind_hs
        rw [runSteps_invisible_getEventAt_pqxdh hinv₁,
            Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hfind_hs
        have hat_ad : ((aliceTr tr₀ "alice" "bob" (randTerm 0 32)
            (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk).at? (tr₀.length + 5) :
            Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
            some (EvP (.AliceDone "alice" "bob" o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by
          unfold aliceTr aliceTrOpt
          rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
              at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
              at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
              at?_append_same_eq (fun _ => rfl), if_pos' (by simp [length_append_eq, Nat.add_assoc])]
        rw [hat_ad] at hfind_hs
        injection hfind_hs with hev_eq
        subst hev_eq
        dsimp only at hfind_pq
        injection hfind_pq with hpair
        exact Prod.mk.inj hpair.symm
      · rw [if_neg' hidx_hs, htr₀_compNone idx_hs] at hfind_hs
        cases hfind_hs
  obtain ⟨rfl, rfl⟩ := hppk_eq
  -- Unpack RunMatches of s₁
  obtain ⟨_, _, _, _, hok₁, _, hv₁_eq, inp₁, drs₁, outs₁, hv₁_split,
    hinp₁, hdrs₁, houts₁, _, _⟩ := hrm₁
  have hw₁_eq : w₁ = encMsg stA₀ (randTerm (tr₁.length + 1) cl₁)
      (DY.Spqr.spqrSend stA₀.spqr (randTerm (tr₁.length + 1) cl₁)).2.1
      (randTerm tr₁.length 32) := Option.some.inj (hls₁.symm.trans hls₁')
  subst hw₁_eq
  have hese₁ : encSendEntry tr₁ ((Step.messageEncrypt "alice" (tr₀.length + 8) cl₁ (tr₁.length + 2)).next tr₁)
      (tr₀.length + 8) true =
      [⟨.send, [o.ek, o.ct, encMsg stA₀ (randTerm (tr₁.length + 1) cl₁)
        (DY.Spqr.spqrSend stA₀.spqr (randTerm (tr₁.length + 1) cl₁)).2.1
        (randTerm tr₁.length 32)], .preKeySend, none⟩] := by
    unfold encSendEntry
    rw [hls₁', hppk₁]
  dsimp only [tr₁] at hexp₁ hls₁' hedr₁ hese₁ hv₁_eq
  dsimp only [stepView] at hv₁_eq
  rw [ite_eq_left_iff.mpr (fun h => absurd hok₁ h), hexp₁, List.append_nil,
      hwrap, hedr₁, hese₁, List.cons_append] at hv₁_eq
  have hinp₁_eq : inp₁ = ⟨.pt, [randTerm tr₁.length 32], .single, none⟩ :=
    (List.cons.inj (hv₁_split.symm.trans hv₁_eq)).1
  subst hinp₁_eq
  have houts₁_k : ∃ v, outs₁ = [v] ∧ v.kind = .send := by
    unfold OutputsMatch at houts₁
    rw [hev_exit, hev_cmd] at houts₁
    obtain ⟨vo, rfl, hvo⟩ := houts₁
    exact ⟨vo, rfl, hvo.1.symm⟩
  obtain ⟨hdrs₁_eq, houts₁_eq⟩ :=
    drs_outs_of_stepView_send houts₁_k (hv₁_split.symm.trans hv₁_eq)
  -- Plaintext m₁ bytes
  rw [hev_inp, inputKind, hev_cmd] at hinp₁
  have hg_m₁ : gamma compI7003 S g (randTerm tr₁.length 32) = ptBytes :=
    List.singleton_injective hinp₁.2
  -- Coins cl₁ bytes
  rw [hdrs₁_eq, hev_coins] at hdrs₁
  have hcl₁_pin := drawsMatch_nil_or_single (r := r) (S := S) (g := g)
    (ts := tr₁.length + 1) (cl := cl₁) (coins := coins1Bytes)
    (fun v hv hne => by
      subst hv
      refine hgwf.1 (rngEntry (randTerm (tr₁.length + 1) cl₁)) ?_ rfl (tr₁.length + 1) cl₁ hne
        (by simp [rngEntry])
      dsimp only [tr₁]
      rw [hv₁_eq]; simp [if_neg' hne])
    hdrs₁
  have hcl₁_le : cl₁ ≤ 64 := by
    have h64 : coins1Bytes.length = 64 := by decide
    omega
  have hg_coins₁ : gamma compI7003 S g (randTerm (tr₁.length + 1) cl₁) = coins1Bytes.take cl₁ :=
    hcl₁_pin.2
  -- Sent wire bytes γ w₁ = msgBytes
  unfold OutputsMatch at houts₁
  rw [hev_exit, hev_cmd, houts₁_eq] at houts₁
  obtain ⟨vo, hvo_eq, hbm_out⟩ := houts₁
  have hvo_inj := List.singleton_injective hvo_eq.symm
  subst hvo_inj
  dsimp only [BytesMatchEntry, SendMatches] at hbm_out
  obtain ⟨pkId, spkId, kpkId, hids, hwire_eq⟩ := hbm_out.2
  rw [bun0Raw_eq, bun0_props.2.2.1] at hids
  injection hids with hids'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ hids'
  unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes at hwire_eq
  rw [(setup_ids_7003 hf).2.2.2.1, pubBytes_ikA_7003 hf, hpin0.ek_eq, hpin0.ct_eq] at hwire_eq
  set m₁ := randTerm tr₁.length 32
  set c₁ := randTerm (tr₁.length + 1) cl₁
  set pq₁ := (DY.Spqr.spqrSend stA₀.spqr c₁).2.1
  set w₁ := encMsg stA₀ c₁ pq₁ m₁
  have hg_w₁ : gamma compI7003 S g w₁ = msgBytes :=
    preKeyWire_msg_inj_7003 hmsg_len (hwire_eq.symm.trans hout_wire)
  -- Split w₁ into wire₁ and mac₁
  set keys₁ := trMsgKeys pq₁ (kdfCk stA₀.cks).2
  set wire₁ := DY.Libsignal.TripleRatchet.trHonestWireMsg
    (DY.DiffieHellman.dhPk stA₀.dhs) stA₀.ns stA₀.pn
    (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁)
    (DY.Spqr.spqrSend stA₀.spqr c₁).2.2
  set mac_t₁ := computeMac keys₁.macKey stA₀.myIk stA₀.peerIk wire₁
  have hg_mac_len : (gamma compI7003 S g mac_t₁).length = 8 := by
    dsimp only [mac_t₁, computeMac, DY.Libsignal.TripleRatchet.hmac]
    rw [gamma_trunc8, gamma_kdfExtract, List.length_take, hmacWith_F7_length]
    decide
  have hsplit_w₁ : gamma compI7003 S g wire₁ ++ gamma compI7003 S g mac_t₁ =
      wireBytes ++ macBytes := by
    simpa [w₁, encMsg, gamma_concat] using hg_w₁.trans hmsg_split
  obtain ⟨hg_wire₁, hg_mac₁⟩ := append_inj_of_right_len hg_mac_len hmac_len hsplit_w₁
  -- Pin γ pq₁ = salt1Bytes via HMAC injectivity
  have hg_seedA : gamma compI7003 S g (kdfCk stA₀.cks).2 = seedA0Bytes := by
    unfold kdfCk DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.litByte
    rw [gamma_kdfExtract, hpin0.cks_eq, gamma_literalToBytes]
    have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
    rw [hb1]
    exact ratchet_a_facts_7003.2.2.2.2.2.2.2.1
  have hpq₁_eq : pq₁ = DY.Spqr.spqrChainKey o.keys.pqr spqrA2B (DY.Spqr.encodeSpqrIndexTerm 1) := by
    dsimp only [pq₁, stA₀, aliceSt, DY.Spqr.spqrSend, DY.Spqr.spqrInit]
    rw [DY.BytesView.view_pack]
  have hp_a2b : gamma compI7003 S g spqrA2B = [0#8] := by
    unfold spqrA2B DY.Spqr.encodeSpqrDirectionParams
    rw [gamma_literalToBytes]; decide
  have hg_pq₁_bytes : gamma compI7003 S g pq₁ =
      spqrKeyBytes (S.chainKey pqrBytes [0#8] [1#8, 0#8, 0#8, 0#8]) := by
    rw [hpq₁_eq, gamma_spqrChainKey, hpin0.pqr_eq]
    have hidx1 : gamma compI7003 S g (DY.Spqr.encodeSpqrIndexTerm 1) = [1#8, 0#8, 0#8, 0#8] := by
      unfold DY.Spqr.encodeSpqrIndexTerm
      rw [gamma_literalToBytes]; decide
    rw [hp_a2b, hidx1]
  have hg_mk₁_len : (gamma compI7003 S g keys₁.macKey).length = 32 := by
    dsimp only [keys₁, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2,
      DY.Libsignal.TripleRatchet.hmac]
    rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
  have hg_mk₁ : gamma compI7003 S g keys₁.macKey = macKey1Bytes := by
    dsimp only [mac_t₁, computeMac, DY.Libsignal.TripleRatchet.hmac] at hg_mac₁
    rw [gamma_trunc8, gamma_kdfExtract, gamma_concat, gamma_concat,
        hpin0.myIk_eq, hpin0.peerIk_eq, hg_wire₁, ← List.append_assoc] at hg_mac₁
    exact (hmacWith_take8_inj_of_untagged hg_mk₁_len (by decide) hmac_untag
      (hg_mac₁.trans hmac_eq.symm)).1
  have hg_prkMsg₁_len : (gamma compI7003 S g (DY.Libsignal.TripleRatchet.hmac pq₁ (kdfCk stA₀.cks).2)).length = 32 := by
    unfold DY.Libsignal.TripleRatchet.hmac; rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
  have hg_prkMsg₁ : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hmac pq₁ (kdfCk stA₀.cks).2) =
      prkMsg1Bytes := by
    dsimp only [keys₁, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2,
      DY.Libsignal.TripleRatchet.hmac] at hg_mk₁
    rw [gamma_kdfExtract] at hg_mk₁
    exact (hmacWith_inj_of_untagged hg_prkMsg₁_len (by decide)
      ratchet_a_facts_7003.2.2.1 (hg_mk₁.trans ratchet_a_facts_7003.2.1.symm)).1
  have hg_pq₁_len : (gamma compI7003 S g pq₁).length = 32 := by
    rw [hg_pq₁_bytes]; exact spqrKeyBytes_length _
  have hsalt₁_pin : spqrKeyBytes (S.chainKey pqrBytes [0#8] [1#8, 0#8, 0#8, 0#8]) = salt1Bytes := by
    rw [← hg_pq₁_bytes]
    unfold DY.Libsignal.TripleRatchet.hmac at hg_prkMsg₁
    rw [gamma_kdfExtract, hg_seedA] at hg_prkMsg₁
    exact (hmacWith_inj_of_untagged hg_pq₁_len (by decide)
      ratchet_a_facts_7003.2.2.2.2.2.2.1
      (hg_prkMsg₁.trans ratchet_a_facts_7003.2.2.2.2.2.1.symm)).1
  -- Pin S.sendMsg via GhostWF + trWireBytes_pq_inj_7003
  have hg_encKey₁ : gamma compI7003 S g keys₁.cipherKey = encKey1Bytes := by
    dsimp only [keys₁, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1]
    unfold DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.lit
      DY.Libsignal.TripleRatchet.litByte
    rw [gamma_kdfExtract, show gamma compI7003 S g (DY.KdfExtract.kdfExtract pq₁ (kdfCk stA₀.cks).2) =
        prkMsg1Bytes from hg_prkMsg₁, gamma_concat, gamma_literalToBytes, gamma_literalToBytes,
        ofByteArray_info_labels.2.2]
    have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
    rw [hb1]
    exact ratchet_a_facts_7003.1
  have hg_iv₁ : (gamma compI7003 S g keys₁.iv).take 16 = iv1Bytes := by
    change (gamma compI7003 S g
      (DY.KdfExtract.kdfExtract (DY.KdfExtract.kdfExtract pq₁ (kdfCk stA₀.cks).2)
        (DY.Concat.concat keys₁.macKey
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
            (DY.Libsignal.TripleRatchet.litByte 3))))).take 16 = iv1Bytes
    rw [gamma_kdfExtract, show gamma compI7003 S g (DY.KdfExtract.kdfExtract pq₁ (kdfCk stA₀.cks).2) =
        prkMsg1Bytes from hg_prkMsg₁, gamma_concat, hg_mk₁, gamma_concat]
    unfold DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
    rw [gamma_literalToBytes, gamma_literalToBytes, ofByteArray_info_labels.2.2]
    have hb3 : ofByteArray (ByteArray.mk #[3]) = [0x03#8] := by decide
    rw [hb3, ← List.append_assoc, ratchet_a_facts_7003.2.2.2.1]
    exact ratchet_a_facts_7003.2.2.2.2.1
  have hg_ct₁ : gamma compI7003 S g (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁) = ctBytes := by
    rw [gamma_symEnc, hg_encKey₁, hg_iv₁, hg_m₁, haes_eq]
  have hvo_mem : (⟨.send, [o.ek, o.ct, w₁], .preKeySend, none⟩ : VisEntry) ∈ v₁ := by
    rw [hv₁_eq]; simp
  have haddr_w₁ : g.addr wire₁ = addr1Bytes := by
    have ha := (hgwf.2.2 _ hvo_mem rfl).1 rfl o.ek o.ct w₁
      (encSig stA₀ c₁ pq₁ m₁) rfl (parse_encMsg stA₀ c₁ pq₁ m₁)
    exact ha.trans addr1_eq_serialized.symm
  have hpq_msg₁ : (DY.Spqr.spqrSend stA₀.spqr c₁).2.2 =
      ({ st := DY.Spqr.spqrInit o.keys.pqr spqrA2B, coins := c₁ } :
        DY.Spqr.SendMsg.SubF DY.Bytes).pack := by
    dsimp only [stA₀, aliceSt, DY.Spqr.spqrSend, DY.Spqr.spqrInit]
  have hg_wire₁' :
      trWireBytes addr1Bytes DY.TrWire.canonicalVariation
        (WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ctBytes)
        (gamma compI7003 S g (DY.Spqr.spqrSend stA₀.spqr c₁).2.2) = wireBytes := by
    have hns0 : stA₀.ns = 0 := rfl
    have hpn0 : stA₀.pn = 0 := rfl
    have hw_unfold : wire₁ = DY.TrWire.trWireMsg DY.Libsignal.TripleRatchet.messageVersion
        (DY.DiffieHellman.dhPk stA₀.dhs) 0 0
        (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁)
        (DY.Spqr.spqrSend stA₀.spqr c₁).2.2 DY.TrWire.canonicalVariation := by
      dsimp only [wire₁, DY.Libsignal.TripleRatchet.trHonestWireMsg]
      rw [hns0, hpn0]
    rw [hw_unfold] at hg_wire₁ haddr_w₁
    rw [gamma_trWireMsg, haddr_w₁, hpin0.dhs_pk_eq, hg_ct₁] at hg_wire₁
    exact hg_wire₁
  have hpq_bytes_eq : gamma compI7003 S g (DY.Spqr.spqrSend stA₀.spqr c₁).2.2 = pqMsg1Bytes :=
    trWireBytes_pq_inj_7003 (by decide : 0 < pqMsg1Bytes.length)
      (by decide : pqMsg1Bytes.length < 64) (hg_wire₁'.trans htr_wire.symm)
  rw [hpq_msg₁, gamma_spqrSendMsg, gamma_spqrInit, hpin0.pqr_eq, hp_a2b, hg_coins₁] at hpq_bytes_eq
  exact ⟨hlok₁.1, hsalt₁_pin, hpq_bytes_eq⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003

