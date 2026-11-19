/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.Witness
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.UA.HwKnows -- shake: keep
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
# Plaintext Draw Non-Collision for `compI7003` (`PtNoCollision7003.lean`)

Proves `not_nextEventCollides_pt7003`: under `compI7003` and any well-formed setup `r` and opaque
semantics `S`, any `.send` plaintext `ev.input` with `8 < ev.input.length` and
`ev.input.length % 16 ≠ 0` containing a distinguishing byte `b₀` cannot trigger `NextEventCollides`
after an explained CLI prefix `evs₁` whose run coin buffers exclude `b₀`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PtNoCollision7003

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles)
open DY.Libsignal.Composed (ComposedEvent reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost ConcretizedTerm Step VisEntry
   BundlePreKeyIds
   node opaqueNode
   concretizeDhPk concretizeDh concretizeKdf concretizeSym concretizeTrunc
   concretizeKemEncap concretizeKemSS concretizeAll
   gamma' gamma assumedInjective
   setupTrace newIndices newRandoms rngEntry eventIdx isAliceDone
   kyberCoinEntries aliceDraws aliceVis bobOpkPk bobVis encDraws encSendEntry decVis
   invertEntry stepView runSteps
   randTerm setupRandomsAt runTrace ptEntryAt
   storedStates storedSecrets principalTerms
   BytesMatchEntry DrawsMatch OutputsMatch inputKind runWrapped
   EnvMatches RunMatches MatchesEventsAt MatchesEvents Explains HwAttackerKnows
   plaintextTerms prefixTerms MemoCollisionOn)
open DY.Libsignal.Composed.Refinement.Cli
  (PrefixExplainingGhosts NextEventCollides)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
  (compI7003_publicKey compI7003_agreement compI7003_aesEncrypt compI7003_kyberEncaps
   compLookupPub_length compLookupDh_length compAesPerm_length compKyberEncaps_length)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (length_hmacWith_32)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt PQEvEntry pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
  (lt_of_randAt randAt_of_le_of_lt step_le_next runSteps_le runSteps_append
   mem_newRandoms_of_randAt randAt_setupTrace_mem_setupRandomsAt prefixTerms_termRandAt
   newRandoms_self newRandoms_append_rnd_ge newRandoms_append_nonRnd_ge
   run_bind_fst run_bind_snd Preserves
   noRandAt_append_nonRnd noRandAt_compromise noRandAt_compromiseOPK noRandAt_exposeKey
   noRandAt_exposeSpqr noRandAt_exposeSkipped noRandAt_invertDH noRandAt_invertKEM
   randAt_invisible)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (stepIn_next stepIn_ok
   bobStart_newRandoms_32 messageDecrypt_newRandoms_32 messageDecryptSkipped_newRandoms_32)

/-! ## 1. Non-`Random` `assumedInjective` Length Exclusion under `compI7003` -/

section Unsealed
unseal DY.Bytes

private theorem rec_eq_concretizeAll
    {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) (x : F DY.Bytes)
    (hsub : DY.Bytes.SubFunction pf (concretizeAll i S g) := by
      refine @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => ?_⟩
      simp -failIfUnchanged only [concretizeAll,
        DY.Libsignal.Composed.Refinement.allFuns,
        DY.Libsignal.Composed.Refinement.litFuns,
        DY.Libsignal.Composed.Refinement.concatFuns,
        DY.Libsignal.Composed.Refinement.dhFuns,
        DY.Libsignal.Composed.Refinement.kdfFuns,
        DY.Libsignal.Composed.Refinement.symFuns,
        DY.Libsignal.Composed.Refinement.truncFuns,
        DY.Libsignal.Composed.Refinement.x25519Funs,
        DY.Libsignal.Composed.Refinement.kemFuns,
        DY.Libsignal.Composed.Refinement.sigFuns,
        DY.Libsignal.Composed.Refinement.spqrFuns,
        DY.Libsignal.Composed.Refinement.trWireFuns,
        Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
      rfl) :
    DY.Bytes.rec (concretizeAll i S g) (DY.BytesView.pack x) =
      pf x (fun y _ => DY.Bytes.rec (concretizeAll i S g) y) := by
  have := hsub
  exact DY.Bytes.rec_eq pf (concretizeAll i S g) x

private theorem nonRandom_assumedInjective_len7003
    (S : OpaqueSymbolSemantics) (g : Ghost) (u : DY.Bytes)
    (hinj : assumedInjective u = true)
    (hss32 : ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
      u = x.pack → (gamma compI7003 S g x.entropy).length = 32)
    (hgt8 : 8 < (gamma compI7003 S g u).length)
    (hmod16 : (gamma compI7003 S g u).length % 16 ≠ 0) :
    ∃ rnd : DY.Random.Random DY.Bytes, u.view? DY.Random.Random = some rnd ∧ rnd.size ≠ 0 := by
  rcases (assumedInjective_eq_true_iff u).mp hinj with
    hrnd | hdhPk | hdh | hkdf | hsym | htrunc | hencap | hss
  · exact hrnd
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdhPk
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma compI7003 S g x.pack).length = 32 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeDhPk compI7003) x]
      dsimp only [concretizeDhPk, node]
      rw [compI7003_publicKey, Option.getD_some]
      exact compLookupPub_length _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdh
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma compI7003 S g x.pack).length = 32 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeDh compI7003) x]
      dsimp only [concretizeDh, node]
      rw [compI7003_agreement, Option.getD_some]
      exact compLookupDh_length _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkdf
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma compI7003 S g x.pack).length = 32 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeKdf compI7003) x]
      exact length_hmacWith_32 (sha256CompressFunction compI7003) _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsym
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma compI7003 S g x.pack).length % 16 = 0 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeSym compI7003) x]
      dsimp only [concretizeSym, node]
      rw [compI7003_aesEncrypt, Option.getD_some, compAesPerm_length]
      omega
    exact absurd hg hmod16
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htrunc
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma compI7003 S g x.pack).length ≤ 8 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) concretizeTrunc x]
      exact List.length_take_le 8 _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hencap
    rcases pack_of_view_eq_some hx with rfl
    unfold gamma gamma' at hgt8 hmod16
    rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeKemEncap compI7003) x]
      at hgt8 hmod16
    dsimp only [concretizeKemEncap] at hgt8 hmod16
    split at hmod16
    · rename_i he32
      have h1600 := compKyberEncaps_length (x.entropy.rec (concretizeAll compI7003 S g)).bytes
      have hg : ((((compI7003 kyberEncapsSymbol
          [(x.pk.rec (concretizeAll compI7003 S g)).bytes,
           (x.entropy.rec (concretizeAll compI7003 S g)).bytes]).getD []).take 1568)).length = 1568 := by
        rw [compI7003_kyberEncaps, Option.getD_some, List.length_take, h1600]
        decide
      dsimp only [node] at hmod16
      omega
    · rename_i hne32
      simp only [hne32, ↓reduceIte, opaqueNode, List.length_nil] at hgt8
      omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hss
    rcases pack_of_view_eq_some hx with rfl
    have he32 := hss32 x rfl
    have hg : (gamma compI7003 S g x.pack).length = 32 := by
      unfold gamma gamma'
      rw [rec_eq_concretizeAll (i := compI7003) (S := S) (g := g) (concretizeKemSS compI7003 S) x]
      dsimp only [concretizeKemSS]
      simp only [show ((x.entropy.rec (concretizeAll compI7003 S g)).bytes).length = 32 from he32,
        ↓reduceIte, node]
      have h1600 := compKyberEncaps_length (x.entropy.rec (concretizeAll compI7003 S g)).bytes
      rw [compI7003_kyberEncaps, Option.getD_some, List.length_drop, h1600]
    omega

end Unsealed

/-! ## 2. Random Draw Classification Along `MatchesEventsAt` -/

private theorem setupRandomsAt_size_mod16 {r : ProtocolSetup} {ts sz : Nat}
    (hne : r.alice ≠ r.bob) (h : (ts, sz) ∈ setupRandomsAt r) : sz % 16 = 0 := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hne] at h
  rcases List.mem_append.mp h with h1 | h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h1
    rcases h1 with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  · split at h2
    · simp only [List.mem_singleton, Prod.mk.injEq] at h2
      rcases h2 with ⟨_, rfl⟩; decide
    · cases h2

private theorem randAt_envMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step}
    {ev : EnvEvent} {vis : List VisEntry} {ts sz : Nat}
    (hem : EnvMatches interp r S g tr s ev vis)
    (hrnd : RandAt (s.next tr) ts sz) : RandAt tr ts sz := by
  by_contra hno
  cases ev with
  | registerCorrupt _ _ => exact hem
  | breakDH =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakDH.next tr = (DY.Libsignal.PQXDH.breakDH.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakDH.reachability () tr] at hrnd
    have hb : (DY.Libsignal.PQXDH.breakDH.run tr).2.val =
        tr.append ({ ev := PQXDHEvent.BrokenDH } : PQEvEntry) := by
      unfold DY.Libsignal.PQXDH.breakDH
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
        Traceful.run_pure]
    rw [hb] at hrnd
    exact noRandAt_append_nonRnd ({ ev := PQXDHEvent.BrokenDH } : PQEvEntry) rfl hno hrnd
  | breakKEM =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakKEM.next tr = (DY.Libsignal.PQXDH.breakKEM.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakKEM.reachability () tr] at hrnd
    have hb : (DY.Libsignal.PQXDH.breakKEM.run tr).2.val =
        tr.append ({ ev := PQXDHEvent.BrokenKEM } : PQEvEntry) := by
      unfold DY.Libsignal.PQXDH.breakKEM
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
        Traceful.run_pure]
    rw [hb] at hrnd
    exact noRandAt_append_nonRnd ({ ev := PQXDHEvent.BrokenKEM } : PQEvEntry) rfl hno hrnd
  | invertDH _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertDH h).next tr = ((DY.Libsignal.PQXDH.invertDH h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertDH.reachability h tr] at hrnd
    exact (noRandAt_invertDH h).run tr hno hrnd
  | invertKEM _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertKEM h).next tr = ((DY.Libsignal.PQXDH.invertKEM h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertKEM.reachability h tr] at hrnd
    exact (noRandAt_invertKEM h).run tr hno hrnd
  | leak _ _ =>
    have hleak : s.IsLeak := hem.2.1
    cases s <;> try exact False.elim hleak
    · rename_i me si k
      rw [show (Step.exposeKey me si k).next tr =
          ((DY.Libsignal.TripleRatchet.exposeKey me si k).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability (me, si, k) tr] at hrnd
      exact (noRandAt_exposeKey me si k).run tr hno hrnd
    · rename_i me si
      rw [show (Step.exposeSpqr me si).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSpqr me si).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSpqr.reachability (me, si) tr] at hrnd
      exact (noRandAt_exposeSpqr me si).run tr hno hrnd
    · rename_i sk
      rw [show (Step.exposeSkipped sk).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSkipped sk).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSkipped.reachability sk tr] at hrnd
      exact (noRandAt_exposeSkipped sk).run tr hno hrnd
    · rename_i p si
      rw [show (Step.compromiseIK p si).next tr =
          ((DY.Libsignal.PQXDH.compromiseIK p si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseIK.reachability (p, si) tr] at hrnd
      exact (noRandAt_compromise p si .identity
        (PQXDHEvent.CompromisedIK p ∘ DY.DiffieHellman.dhPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromiseSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseSPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromise b si .signedPrekey
        (PQXDHEvent.CompromisedSPK b ∘ DY.DiffieHellman.dhPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromisePQSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromisePQSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromisePQSPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromise b si .pqPrekey
        (PQXDHEvent.CompromisedPQSPK b ∘ DY.PQKem.kemPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromiseOPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseOPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseOPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromiseOPK b si).run tr hno hrnd

private theorem genRand_run_fst (n : Nat) (tr : ExecTrace) :
    ((DY.Random.genRand n).run tr).1 = some (randTerm tr.length n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, Traceful.run_pure]
  rfl
private theorem genRand_run_snd (n : Nat) (tr : ExecTrace) :
    ((DY.Random.genRand n).run tr).2.val = tr.append (DY.Random.ExecEntryT.mk n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, Traceful.run_pure]
private theorem pure_run_fst {α : Type} (a : α) (tr : ExecTrace) :
    ((Pure.pure a : Traceful α).run tr).1 = some a := by
  rw [Traceful.run_pure]
private theorem pure_run_snd {α : Type} (a : α) (tr : ExecTrace) :
    ((Pure.pure a : Traceful α).run tr).2.val = tr := by
  rw [Traceful.run_pure]
private theorem failure_run_fst {α : Type} (tr : ExecTrace) :
    ((Alternative.failure : Traceful α).run tr).1 = none := by
  rw [Traceful.run_failure]
private theorem failure_run_snd {α : Type} (tr : ExecTrace) :
    ((Alternative.failure : Traceful α).run tr).2.val = tr := by
  rw [Traceful.run_failure]

private structure HSWp (tr₀ : ExecTrace) {α : Type} (x : Traceful α) : Prop where
  ok :
    ((x.run tr₀).1 = none ∧
      ((x.run tr₀).2.val = tr₀ ∨ (x.run tr₀).2.val = tr₀.append (DY.Random.ExecEntryT.mk 32))) ∨
    ((x.run tr₀).1.isSome = true ∧
      (x.run tr₀).2.val =
        (tr₀.append (DY.Random.ExecEntryT.mk 32)).append (DY.Random.ExecEntryT.mk 32))

private theorem HSWp.bind_ro {tr₀ : ExecTrace} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves (fun t => t = tr₀) x) (hf : ∀ a, HSWp tr₀ (f a)) : HSWp tr₀ (x >>= f) :=
  ⟨by
    rw [run_bind_fst, run_bind_snd]
    have htr : (x.run tr₀).2.val = tr₀ := hx.run tr₀ rfl
    cases (x.run tr₀).1 with
    | none => exact Or.inl ⟨rfl, Or.inl htr⟩
    | some a => rw [htr]; exact (hf a).ok⟩

private theorem HSWp.tail (tr₀ : ExecTrace) (p₁ p₂ : Prop) [Decidable p₁] [Decidable p₂]
    {α : Type} (k : DY.Bytes → DY.Bytes → α) :
    HSWp tr₀ (do
      let ek ← DY.Random.genRand 32
      _root_.guard p₁
      _root_.guard p₂
      let entropy ← DY.Random.genRand 32
      Pure.pure (k ek entropy)) :=
  ⟨by
    unfold _root_.guard
    by_cases hp1 : p₁
    · by_cases hp2 : p₂
      · exact Or.inr (by simp [hp1, hp2, run_bind_fst, run_bind_snd, genRand_run_fst,
          genRand_run_snd, pure_run_fst, pure_run_snd])
      · exact Or.inl ⟨by simp [hp1, hp2, run_bind_fst, genRand_run_fst,
          pure_run_fst, failure_run_fst],
          Or.inr (by simp [hp1, hp2, run_bind_snd, genRand_run_fst,
            genRand_run_snd, pure_run_fst, pure_run_snd, failure_run_fst, failure_run_snd])⟩
    · exact Or.inl ⟨by simp [hp1, run_bind_fst, genRand_run_fst, failure_run_fst],
        Or.inr (by simp [hp1, run_bind_snd, genRand_run_fst, genRand_run_snd,
          failure_run_fst, failure_run_snd])⟩⟩

private theorem aliceHandshake_run_cases
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) (tr₀ : ExecTrace) :
    HSWp tr₀ (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply HSWp.bind_ro (Preserves.getKey a idStateIdx .identity); intro _
  apply HSWp.bind_ro (Preserves.lookupIdentity b regIdxB); intro p
  rcases p with ⟨_, _⟩; dsimp only
  apply HSWp.bind_ro (Preserves.receiveMessage h.spk); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.spkSig); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.pqpk); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.pqpkSig); intro _
  apply HSWp.bind_ro (Preserves.guardP _); intro _
  apply HSWp.bind_ro (Preserves.guardP _); intro _
  cases h.opk <;> dsimp only
  · apply HSWp.bind_ro Preserves.pure; intro _
    exact HSWp.tail tr₀ _ _ _
  · apply HSWp.bind_ro (Preserves.receiveMessage _); intro _
    apply HSWp.bind_ro Preserves.pure; intro _
    exact HSWp.tail tr₀ _ _ _

private theorem aliceStart_ok_newRandoms
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) (tr₀ : ExecTrace)
    (hok : (Step.aliceStart a b idStateIdx regIdxB h).ok tr₀ = true) :
    newRandoms tr₀ ((Step.aliceStart a b idStateIdx regIdxB h).next tr₀) =
      [(randTerm tr₀.length 32, 32),
       (randTerm (tr₀.length + 1) 32, 32),
       (randTerm (tr₀.length + 2) 32, 32)] := by
  have hnext_eq :
      (Step.aliceStart a b idStateIdx regIdxB h).next tr₀ =
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).2.val :=
    stepIn_next DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, h) tr₀
  have hok_eq :
      ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).1.isSome = true := by
    rwa [show (Step.aliceStart a b idStateIdx regIdxB h).ok tr₀ =
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).1.isSome from
      stepIn_ok DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, h) tr₀] at hok
  rcases (aliceHandshake_run_cases a b idStateIdx regIdxB h tr₀).ok with
    ⟨hnone, _⟩ | ⟨hsome_b, htr_eq⟩
  · unfold DY.Libsignal.Composed.aliceStart at hok_eq
    rw [run_bind_fst, hnone] at hok_eq
    cases hok_eq
  · obtain ⟨_, hsome⟩ := Option.isSome_iff_exists.mp hsome_b
    have htr1 :
        ∃ (e1 e2 : Network.ExecEntryT) (e3 : PQEvEntry)
          (e4 : Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.TREntry)
          (e5 : DY.ProtocolEvent.ExecEntryT ComposedEvent)
          (e6 : Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux.StEntry),
          (Step.aliceStart a b idStateIdx regIdxB h).next tr₀ =
            ((((((((tr₀.append (DY.Random.ExecEntryT.mk 32)).append
              (DY.Random.ExecEntryT.mk 32)).append
              (DY.Random.ExecEntryT.mk 32)).append e1).append e2).append e3).append e4).append e5).append e6 := by
      rw [hnext_eq]; unfold DY.Libsignal.Composed.aliceStart
      rw [run_bind_snd, hsome, htr_eq]
      dsimp only
      simp only [DY.Libsignal.TripleRatchet.traceLength,
        Symbolic.DYBridge.DY.Random.genRand_eq_1,
        Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact ⟨_, _, _, _, _, _, rfl⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, htr1⟩ := htr1
    rw [htr1]
    have hlen_app : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (x : E),
        (t.append x).length = t.length + 1 := fun _ _ => by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e6 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e5 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e4 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e3 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e2 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e1 rfl,
      newRandoms_append_rnd_ge (by simp only [hlen_app]; omega) 32,
      newRandoms_append_rnd_ge (by simp only [hlen_app]; omega) 32,
      newRandoms_append_rnd_ge (Nat.le_refl _) 32,
      newRandoms_self]
    simp only [hlen_app, List.nil_append, List.cons_append]

private def CoinDrawn (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (evs : List CliEvent) (vis : List VisEntry)
    (ts sz : Nat) : Prop :=
  randTerm ts sz ∈ plaintextTerms vis ∨
  (∃ v ∈ vis, v.kind = .rng ∧ sz = 32 ∧ randTerm ts sz ∈ v.terms) ∨
  (∃ rEv, .run rEv ∈ evs ∧ ∃ p, (∀ x ∈ p, x ∈ rEv.coins) ∧
    ∃ v ∈ vis, v.kind = .rng ∧ v.layout = .single ∧ v.terms = [randTerm ts sz] ∧
      BytesMatchEntry interp r S g .rng p v)

private theorem coinDrawn_mono {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {evs₁ evs₂ : List CliEvent} {v₁ v₂ : List VisEntry}
    {ts sz : Nat}
    (hevs : ∀ x ∈ evs₁, x ∈ evs₂) (hvis : ∀ x ∈ v₁, x ∈ v₂)
    (h : CoinDrawn interp r S g evs₁ v₁ ts sz) :
    CoinDrawn interp r S g evs₂ v₂ ts sz := by
  rcases h with hpt | ⟨v, hv, hk, h32, ht⟩ | ⟨rEv, hrEv, p, hp, v, hv, hk, hl, hts, hbme⟩
  · unfold plaintextTerms at hpt
    obtain ⟨v, hv_filt, ht⟩ := List.mem_flatMap.mp hpt
    obtain ⟨hv, hk⟩ := List.mem_filter.mp hv_filt
    refine Or.inl ?_
    unfold plaintextTerms
    exact List.mem_flatMap.mpr ⟨v, List.mem_filter.mpr ⟨hvis v hv, hk⟩, ht⟩
  · exact Or.inr (Or.inl ⟨v, hvis v hv, hk, h32, ht⟩)
  · exact Or.inr (Or.inr ⟨rEv, hevs _ hrEv, p, hp, v, hvis v hv, hk, hl, hts, hbme⟩)

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (hf : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction hf with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hr'⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hr'⟩

private theorem rng_mem_drs_of_runMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {ev : RunEvent} {inp : VisEntry}
    {drs outs : List VisEntry} {w : VisEntry}
    (hinp : BytesMatchEntry interp r S g (inputKind ev) ev.input inp)
    (houts : OutputsMatch interp r S g ev outs initIds)
    (hw_mem : w ∈ inp :: (drs ++ outs)) (hw_rng : w.kind = .rng) :
    w ∈ drs := by
  rcases List.mem_cons.mp hw_mem with rfl | hdo
  · have hk := hinp.1
    rw [hw_rng] at hk
    unfold inputKind at hk
    split at hk <;> cases hk
  · rcases List.mem_append.mp hdo with hdrs | ho
    · exact hdrs
    · unfold OutputsMatch at houts
      split at houts
      · obtain ⟨_, rfl, hbme⟩ := houts
        rcases List.mem_singleton.mp ho with rfl
        have hk := hbme.1; rw [hw_rng] at hk; cases hk
      · obtain ⟨_, rfl, hbme⟩ := houts
        rcases List.mem_singleton.mp ho with rfl
        have hk := hbme.1; rw [hw_rng] at hk; cases hk
      · rw [houts] at ho; cases ho

private theorem runMatches_coinDrawn {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {s : Step}
    {ev : RunEvent} {v : List VisEntry} {ts sz : Nat}
    (hsz : sz ≠ 0)
    (hrm : RunMatches interp r S g tr s ev v initIds)
    (hlo : tr.length ≤ ts)
    (hrnd : RandAt (s.next tr) ts sz) :
    CoinDrawn interp r S g [.run ev] v ts sz := by
  obtain ⟨hcls, _, _, _, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, hdrs, houts, _, _⟩ := hrm
  have hmem_nr : (randTerm ts sz, sz) ∈ newRandoms tr (s.next tr) :=
    mem_newRandoms_of_randAt hlo hrnd
  have henc : ∀ (hsub : ∀ w ∈ encDraws (newRandoms tr (s.next tr)), w ∈ v),
      CoinDrawn interp r S g [.run ev] v ts sz := by
    intro hsub
    cases hnr : newRandoms tr (s.next tr) with
    | nil => rw [hnr] at hmem_nr; cases hmem_nr
    | cons r0 rest =>
      rcases r0 with ⟨m0, n0⟩
      rw [hnr] at hmem_nr
      rcases List.mem_cons.mp hmem_nr with hhead | htail
      · injection hhead with hm0 _
        subst hm0
        have hv_pt : (⟨.pt, [randTerm ts sz], .single, none⟩ : VisEntry) ∈ v := by
          apply hsub; rw [hnr]; exact List.mem_cons_self
        refine Or.inl ?_
        unfold plaintextTerms
        exact List.mem_flatMap.mpr ⟨_, List.mem_filter.mpr ⟨hv_pt, rfl⟩, List.mem_singleton.mpr rfl⟩
      · have hfilt : (randTerm ts sz, sz) ∈ rest.filter (·.2 != 0) :=
          List.mem_filter.mpr ⟨htail, bne_iff_ne.mpr hsz⟩
        have hv_rng : rngEntry (randTerm ts sz) ∈ v := by
          apply hsub; rw [hnr]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hfilt, rfl⟩)
        have hdrs_mem : rngEntry (randTerm ts sz) ∈ drs :=
          rng_mem_drs_of_runMatches hinp houts (hv_split ▸ hv_rng) rfl
        obtain ⟨pieces, _, hflat_pre, hfa2⟩ := hdrs
        obtain ⟨p, hp_mem, hbme⟩ := forall₂_mem_right hfa2 hdrs_mem
        refine Or.inr (Or.inr ⟨ev, List.mem_singleton.mpr rfl, p, ?_,
          rngEntry (randTerm ts sz), hv_rng, rfl, rfl, rfl, hbme⟩)
        intro x hx
        exact hflat_pre.subset (List.mem_flatten.mpr ⟨p, hp_mem, hx⟩)
  cases s with
  | aliceStart a b idStateIdx regIdxB h =>
    have hnr := aliceStart_ok_newRandoms a b idStateIdx regIdxB h tr hok
    rw [hnr] at hmem_nr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem_nr
    have hv_own : ∀ w ∈ aliceVis tr ((Step.aliceStart a b idStateIdx regIdxB h).next tr) h,
        w ∈ v := by
      intro w hw
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      exact List.mem_append_left _ hw
    rcases hmem_nr with ⟨heq, rfl⟩ | ⟨heq, rfl⟩ | ⟨heq, rfl⟩
    · have hw : rngEntry (randTerm tr.length 32) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [rngEntry, heq]⟩)
    · have hkyb0 : (⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈
          kyberCoinEntries (randTerm (tr.length + 1) 32) := by
        unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by simp, rfl⟩
      have hw : (⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hkyb0))
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [heq]⟩)
    · let done := eventIdx isAliceDone tr ((Step.aliceStart a b idStateIdx regIdxB h).next tr)
      have hw : ({ rngEntry (randTerm (tr.length + 2) 32) with anchor := done } : VisEntry) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_singleton.mpr rfl)))
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [rngEntry, heq]⟩)
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    obtain ⟨_, h32⟩ := bobStart_newRandoms_32 b a kh regIdxA mh pqIdx spqrMsgIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left
      unfold bobVis
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageDecrypt me sIdx mIdx pqIdx spqrIdx =>
    obtain ⟨_, h32⟩ := messageDecrypt_newRandoms_32 me sIdx mIdx pqIdx spqrIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left; unfold decVis
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageDecryptSkipped me sIdx mIdx skIdx pqIdx spqrIdx =>
    obtain ⟨_, h32⟩ :=
      messageDecryptSkipped_newRandoms_32 me sIdx mIdx skIdx pqIdx spqrIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left; unfold decVis
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageEncrypt _ _ _ _ =>
    refine henc fun w hw => ?_
    rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_append_left _ hw)
  | messageEncryptAbort _ _ =>
    refine henc fun w hw => ?_
    rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
    exact List.mem_append_left _ hw
  | _ => cases hcls

private theorem matchesEvents_coinDrawn {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr₀ : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry} {ts sz : Nat}
    (hsz : sz ≠ 0)
    (hMe : MatchesEventsAt interp r S g initIds tr₀ ss evs vis)
    (hlo : tr₀.length ≤ ts)
    (hrnd : RandAt (runSteps ss tr₀) ts sz) :
    CoinDrawn interp r S g evs vis ts sz := by
  induction hMe with
  | nil hinv =>
    have hrnd₀ := randAt_invisible hinv hrnd
    exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
  | @run0 _ tr pre ss' ev evs' vs hinv _ _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt : ts < (runSteps pre tr).length
    · have hrnd₀ := randAt_invisible hinv (randAt_of_le_of_lt (runSteps_le ss' _) hlt hrnd)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx) (fun _ h => h)
        (ih (Nat.not_lt.mp hlt) hrnd)
  | @env _ tr pre s ss' ev evs' v_step vs hinv hem _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt : ts < (s.next (runSteps pre tr)).length
    · have hrnd_s := randAt_of_le_of_lt (runSteps_le ss' _) hlt hrnd
      have hrnd₀ := randAt_invisible hinv (randAt_envMatches hem hrnd_s)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx)
        (fun x hx => List.mem_append_right _ hx) (ih (Nat.not_lt.mp hlt) hrnd)
  | @run1 _ tr pre s ss' ev evs' v_step vs hinv hrm _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt_pre : ts < (runSteps pre tr).length
    · have hrnd₀ := randAt_invisible hinv
        (randAt_of_le_of_lt (DY.Trace.le_trans _ _ _ (step_le_next s _) (runSteps_le ss' _))
          hlt_pre hrnd)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · by_cases hlt_s : ts < (s.next (runSteps pre tr)).length
      · have hrnd_s := randAt_of_le_of_lt (runSteps_le ss' _) hlt_s hrnd
        exact coinDrawn_mono
          (fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact List.mem_cons_self)
          (fun x hx => List.mem_append_left _ hx)
          (runMatches_coinDrawn hsz hrm (Nat.not_lt.mp hlt_pre) hrnd_s)
      · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx)
          (fun x hx => List.mem_append_right _ hx) (ih (Nat.not_lt.mp hlt_s) hrnd)

/-! ## 3. Main Theorem: `not_nextEventCollides_pt7003` -/

theorem not_nextEventCollides_pt7003
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {evs₁ : List CliEvent} {ev : RunEvent}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {peer : CryptoVerification.SignalSession.Address}
    {b₀ : BitVec 8}
    (hwf : ProtocolSetupWF r)
    (hcmd : ev.cmd = .send peer)
    (hb_gt8 : 8 < ev.input.length)
    (hb_mod16 : ev.input.length % 16 ≠ 0)
    (hb_mem : b₀ ∈ ev.input)
    (h_coins : (evs₁.all fun e => match e with
      | .run rEv => !(rEv.coins.contains b₀)
      | .env _ => true) = true)
    (hex : Explains compI7003 r S g ss vis evs₁) :
    ¬ NextEventCollides compI7003 r S g ss vis evs₁ ev := by
  unfold NextEventCollides
  rw [hcmd]
  rintro ⟨heme, hghosts⟩
  let tr := runTrace r ss
  have hgpt : gamma compI7003 S g (randTerm tr.length 32) = ev.input := by
    unfold BytesMatchEntry ptEntryAt at heme
    dsimp only [List.map] at heme
    exact List.head_eq_of_cons_eq heme.2
  have hg_mem : g ∈ PrefixExplainingGhosts compI7003 r S g ss evs₁ := ⟨rfl, vis, hex⟩
  have hmcol := hghosts g hg_mem
  unfold MemoCollisionOn ptEntryAt at hmcol
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hmcol
  obtain ⟨x₁, hx₁_new, x₂, hx₂_terms, hsh_ne, _, hx₁_pts_imp, _, hbytes_eq⟩ := hmcol
  have ⟨hmemo_pt, hgam_pt_σ⟩ := gamma'_randTerm_32 compI7003 S g tr.length
  rw [hmemo_pt] at hx₁_new
  rcases List.mem_singleton.mp hx₁_new with rfl
  have hx₁_in_pts :
      randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨hx₂_not_pts, hx₂_inj, _⟩ := hx₁_pts_imp hx₁_in_pts
  have hb_sigma : g.σ tr.length 32 = ev.input := hgam_pt_σ.symm.trans hgpt
  have hx₂_bytes : x₂.2.2 = ev.input := hbytes_eq.symm.trans hb_sigma
  have hx₂_in_pre :
      x₂ ∈ (prefixTerms r tr vis).flatMap (fun t => (gamma' compI7003 S g t).memo) := by
    rcases List.mem_append.mp hx₂_terms with hpre | hnew
    · exact hpre
    · rw [hmemo_pt] at hnew
      rcases List.mem_singleton.mp hnew with rfl
      exact absurd rfl hsh_ne
  obtain ⟨t₀, ht₀, hx₂_memo⟩ := List.mem_flatMap.mp hx₂_in_pre
  rcases x₂ with ⟨u, sh, v⟩
  dsimp only at hx₂_not_pts hx₂_inj hx₂_bytes
  cases hx₂_bytes
  obtain ⟨hgam_u, hss32⟩ := memo_entry_inv compI7003 S g t₀ u sh ev.input hx₂_memo
  have hlen_u_eq : (gamma compI7003 S g u).length = ev.input.length := by rw [← hgam_u]
  obtain ⟨rnd, hview, hsz_ne⟩ :=
    nonRandom_assumedInjective_len7003 S g u hx₂_inj hss32
      (hlen_u_eq ▸ hb_gt8) (hlen_u_eq ▸ hb_mod16)
  have hpack_u : u = rnd.pack := pack_of_view_eq_some hview
  obtain ⟨hgam_rnd, hrnd_eq⟩ := gamma_randTerm_of_ne_zero compI7003 S g rnd hsz_ne
  have hb_eq_σ : ev.input = g.σ rnd.timestamp rnd.size := by
    rw [hgam_u, hpack_u, hgam_rnd]
  have hu_eq_rand : u = randTerm rnd.timestamp rnd.size := hpack_u.trans hrnd_eq
  have hrnd : RandAt tr rnd.timestamp rnd.size :=
    prefixTerms_termRandAt hex ht₀ u sh ev.input rnd hx₂_memo hview
  by_cases hsetup : rnd.timestamp < (setupTrace r).length
  · have hrnd_s : RandAt (setupTrace r) rnd.timestamp rnd.size :=
      randAt_of_le_of_lt (runSteps_le ss _) hsetup hrnd
    have hsetup_mem := randAt_setupTrace_mem_setupRandomsAt hwf.1 hrnd_s
    have hfresh_eq := hex.1.1 (rnd.timestamp, rnd.size) hsetup_mem
    have hfresh_len := hwf.2.1 (rnd.timestamp, rnd.size) hsetup_mem
    dsimp only at hfresh_eq hfresh_len
    have hlen_eq : ev.input.length = rnd.size := by
      rw [hb_eq_σ, hfresh_eq, hfresh_len]
    have hmod0 := setupRandomsAt_size_mod16 hwf.1 hsetup_mem
    exact hb_mod16 (hlen_eq ▸ hmod0)
  · rcases matchesEvents_coinDrawn hsz_ne hex.2.2.2 (Nat.not_lt.mp hsetup) hrnd with
      hpt_mem | ⟨v_rng, hv_mem, hv_kind, hsz32, hv_term⟩ |
        ⟨rEv, hrEv_mem, p, hp_coins, v_rng, _, _, hv_lay, hv_terms, hbme⟩
    · exact hx₂_not_pts (List.mem_append_left _ (hu_eq_rand ▸ hpt_mem))
    · have hlen32 := hex.2.1.1 v_rng hv_mem hv_kind rnd.timestamp rnd.size hsz_ne hv_term
      have hlen_eq : ev.input.length = 32 := by
        rw [hb_eq_σ, hlen32, hsz32]
      exact hb_mod16 (by rw [hlen_eq])
    · unfold BytesMatchEntry at hbme
      rw [hv_lay, hv_terms] at hbme
      dsimp only [List.map] at hbme
      have hp_eq : gamma compI7003 S g (randTerm rnd.timestamp rnd.size) = p :=
        List.head_eq_of_cons_eq hbme.2
      have hb_eq_p : ev.input = p := by rw [hgam_u, hu_eq_rand, hp_eq]
      rw [hb_eq_p] at hb_mem
      have hb_coins : b₀ ∈ rEv.coins := hp_coins _ hb_mem
      have hall := List.all_eq_true.mp h_coins (.run rEv) hrEv_mem
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hall
      exact hall hb_coins

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PtNoCollision7003
