/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2DagWalk

/-!
# Clean Symbolic States and `SafeMemo2` State Invariants
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

section Step2CleanStateAndSafe

open DY.Libsignal.TripleRatchet
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.COMPOSED
open Symbolic.BugInjection (CompKyberCorrectOn fillFresh)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (compRecordsI0 compRecordsI0_randomsAt)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs registerIdentityTr genSignedPrekeyTr genPQPrekeyTr)

structure FitsPins (r : ProtocolSetup) : Prop where
  hwf : ProtocolSetupWF r
  ha : r.alice = "alice"
  hb : r.bob = "bob"
  hopk : r.withOpk = false
  hregA : r.regIdA = setup.regIdA
  hregB : r.regIdB = setup.regIdB
  hspkId : r.spkId = setup.spkId
  hkpkId : r.kpkId = setup.kpkId
  hsec0 : secretBytes r 0 = setup.aliceId
  hsec1 : secretBytes r 1 = setup.bobId
  hsec2 : secretBytes r 2 = setup.spk
  hsec3 : secretBytes r 3 = fillFresh 11 64
  hsec4 : secretBytes r 4 = fillFresh 16 64
  hsec5 : secretBytes r 5 = fillFresh 17 64
  hspkSig : r.opaqueBytes (setupPublic r 5) = setup.spkSig
  hpqpkPub : r.opaqueBytes (setupPublic r 6) = setup.kyberPk
  hpqpkSig : r.opaqueBytes (setupPublic r 7) = setup.kyberPkSig
  hkyberSec : r.kyberSecB = setup.kyberSec
  hkyberOk : CompKyberCorrectOn compI0 r setup.kyberCts

theorem fitsPins_of_pinned {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) : FitsPins r := by
  rcases hf with ⟨⟨hc, hi, ⟨hs3, hs4, hs5⟩, ⟨ha, hb⟩, _⟩, _⟩
  rw [hi] at hc
  rcases hc with ⟨hwf, hopk, hrA, hrB, hsId, hkId, hs0, hs1, hs2, hsig1, hpub, hsig2, hksec, _, _, hkok⟩
  exact ⟨hwf, ha, hb, hopk, hrA, hrB, hsId, hkId, hs0, hs1, hs2, hs3, hs4, hs5, hsig1, hpub, hsig2, hksec, hkok⟩

theorem p_c2_kyberCt_eq :
    p_c2.kyberCiphertext = some (kyberKey (setup.kyberCts[0])) := by
  decide +kernel

theorem kyberKey_inj {a b : HwBytes} (h : kyberKey a = kyberKey b) : a = b := by
  unfold kyberKey at h
  exact (List.cons.inj h).2

theorem not_kyberMismatch_p_c2 {r : ProtocolSetup} (hp : FitsPins r) :
    ¬ KyberMismatch compI0 r p_c2 := by
  rintro ⟨e, ct, ss, helen, hct_opt, henc, hdec_ne⟩
  rw [p_c2_kyberCt_eq, Option.some.injEq] at hct_opt
  have hct_eq : ct = setup.kyberCts[0] := (kyberKey_inj hct_opt).symm
  subst hct_eq
  have hmem : setup.kyberCts[0] ∈ setup.kyberCts := by simp [setup]
  exact hdec_ne (hp.hkyberOk _ hmem e ss helen henc)

-- Clean Ghost overriding timestamps >= 22 with exact DAG witness draws and fixing addr = cleanAddrBs
def gClean (g : Ghost) : Ghost where
  σ t n :=
    if t < 22 then g.σ t n
    else if t = 22 ∧ n = 32 then dagBytes 67
    else if t = 23 ∧ n = 32 then dagBytes 69
    else if t = 24 ∧ n = 32 then dagBytes 72
    else if t = 31 ∧ n = 32 then ev1.input
    else if t = 32 then ev1.coins.take n
    else if t = 38 ∧ n = 32 then ev2.input
    else if t = 39 then ev2.coins.take n
    else if t = 45 ∧ n = 32 then dagBytes 127
    else List.replicate n 0
  addr _ := cleanAddrBs

theorem gClean_σ_lt22 (g : Ghost) {t n : Nat} (ht : t < 22) :
    (gClean g).σ t n = g.σ t n := by
  unfold gClean; simp [ht]

theorem gamma'_rand_lt22 (S : OpaqueSymbolSemantics) (g : Ghost) {t n : Nat} (ht : t < 22) :
    gamma' compI0 S (gClean g) (randTerm t n) = gamma' compI0 S g (randTerm t n) := by
  unfold gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom (gClean g)) (concretizeAll compI0 S (gClean g)),
      DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI0 S g)]
  dsimp only [concretizeRandom]
  split
  · rfl
  · rw [gClean_σ_lt22 g ht]

theorem gamma'_lit_eq_gClean (S : OpaqueSymbolSemantics) (g : Ghost) (ba : ByteArray) :
    gamma' compI0 S (gClean g) (DY.Literal.literalToBytes ba) =
      gamma' compI0 S g (DY.Literal.literalToBytes ba) :=
  (DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S (gClean g)) { lit := ba }).trans
    (DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g) { lit := ba }).symm

theorem gamma'_dhPk_eq_of_eq (S : OpaqueSymbolSemantics) (g₁ g₂ : Ghost) {s : DY.Bytes}
    (hs : gamma' compI0 S g₁ s = gamma' compI0 S g₂ s) :
    gamma' compI0 S g₁ (DY.DiffieHellman.dhPk s) = gamma' compI0 S g₂ (DY.DiffieHellman.dhPk s) := by
  unfold gamma' at hs ⊢
  rw [show DY.DiffieHellman.dhPk s = ({ sk := s } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g₂)]
  dsimp only [concretizeDhPk]
  rw [hs]

theorem gamma'_kemPk_eq_of_eq (S : OpaqueSymbolSemantics) (g₁ g₂ : Ghost) {s : DY.Bytes}
    (hs : gamma' compI0 S g₁ s = gamma' compI0 S g₂ s) :
    gamma' compI0 S g₁ (DY.PQKem.kemPk s) = gamma' compI0 S g₂ (DY.PQKem.kemPk s) := by
  unfold gamma' at hs ⊢
  rw [show DY.PQKem.kemPk s = ({ sk := s } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI0 S g₂)]
  dsimp only [concretizeKemPk]
  rw [hs]

theorem gamma'_concat_eq_of_eq (S : OpaqueSymbolSemantics) (g₁ g₂ : Ghost) {a b : DY.Bytes}
    (ha : gamma' compI0 S g₁ a = gamma' compI0 S g₂ a)
    (hb : gamma' compI0 S g₁ b = gamma' compI0 S g₂ b) :
    gamma' compI0 S g₁ (DY.Concat.concat a b) = gamma' compI0 S g₂ (DY.Concat.concat a b) := by
  rw [concat_gamma' compI0 S g₁ a b, concat_gamma' compI0 S g₂ a b]
  dsimp only [concretizeConcat]
  rw [ha, hb]

theorem gamma'_sign_eq_of_eq (S : OpaqueSymbolSemantics) (g₁ g₂ : Ghost) {sk n m : DY.Bytes}
    (hsk : gamma' compI0 S g₁ sk = gamma' compI0 S g₂ sk)
    (hn : gamma' compI0 S g₁ n = gamma' compI0 S g₂ n)
    (hm : gamma' compI0 S g₁ m = gamma' compI0 S g₂ m) :
    gamma' compI0 S g₁ (DY.Signature.sign sk n m) = gamma' compI0 S g₂ (DY.Signature.sign sk n m) := by
  unfold gamma' at hsk hn hm ⊢
  rw [show DY.Signature.sign sk n m = ({ sk := sk, nonce := n, msg := m } : DY.Signature.Sign.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeSign S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (concretizeSign S) (concretizeAll compI0 S g₂)]
  dsimp only [concretizeSign]
  rw [hsk, hn, hm]

theorem setupRandomsAt_r0_eq :
    setupRandomsAt r0 = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] :=
  compRecordsI0_randomsAt setup

noncomputable abbrev setupTr1 : ExecTrace :=
  registerIdentityTr Trace.nil "alice"
noncomputable abbrev setupTr2 : ExecTrace :=
  registerIdentityTr setupTr1 "bob"
noncomputable abbrev setupTr3 : ExecTrace :=
  genSignedPrekeyTr setupTr2 "bob" (randTerm 5 32)
noncomputable abbrev setupTr0 : ExecTrace :=
  genPQPrekeyTr setupTr3 "bob" (randTerm 5 32)

theorem at?_append_of_some_loc {E E' : Type} [DY.ExecTraceTypes.Has E] [DY.ExecTraceTypes.Has E']
    {tr : ExecTrace} {e : E'} {i : Nat} {res : E} (h : tr.at? i = some res) :
    (tr.append e).at? i = some res := by
  have hle := DY.Trace.at?_le (EntryT := E) tr (tr.append e) i (DY.Trace.append_le tr e)
  rw [h] at hle; exact hle

theorem setupTrace_r0_eq : setupTrace r0 = setupTr0 := by
  have hunregA : (!DY.Libsignal.PQXDH.isRegisteredB Trace.nil "alice") = true := by
    unfold DY.Libsignal.PQXDH.isRegisteredB
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hunregB : (!DY.Libsignal.PQXDH.isRegisteredB setupTr1 "bob") = true := by
    have h0 : setupTr1.length = 5 := by
      simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have hat0 : (setupTr1.at? 0 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
      simp [setupTr1, registerIdentityTr, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
    have hat1 : (setupTr1.at? 1 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
        some (Symbolic.Proofs.Tests.Shared.Composed.Runs.EvP
          (.IdentityRegistered "alice" (DY.DiffieHellman.dhPk (randTerm 0 32))
            (DY.Signature.vk (randTerm 0 32)) true)) := by
      simp [setupTr1, registerIdentityTr, Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd,
        randTerm, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
    have hat2 : (setupTr1.at? 2 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
      simp [setupTr1, registerIdentityTr, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
    have hat3 : (setupTr1.at? 3 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
      simp [setupTr1, registerIdentityTr, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
    have hat4 : (setupTr1.at? 4 : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by
      simp [setupTr1, registerIdentityTr, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
    unfold DY.Libsignal.PQXDH.isRegisteredB
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?, h0]
    simp [List.range_succ, hat0, hat1, hat2, hat3, hat4]
  have hidB2 : setupTr2.at? 9 =
      some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob" { kind := .identity, sk := randTerm 5 32 }) := by
    have hlen1 : setupTr1.length = 5 := by
      simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    unfold setupTr2 registerIdentityTr
    dsimp only; rw [hlen1]
    exact at?_append_eq_of_eq _ _ (by simp [hlen1])
  have hidB3 : setupTr3.at? 9 =
      some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob" { kind := .identity, sk := randTerm 5 32 }) := by
    unfold setupTr3 genSignedPrekeyTr
    exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc hidB2)))))
  have hruns : Runs (DY.Libsignal.Composed.Refinement.setupAct r0.alice r0.bob r0.withOpk) Trace.nil () setupTr0 := by
    unfold DY.Libsignal.Composed.Refinement.setupAct
    dsimp only [r0, compRecordsI0, Bool.false_eq_true, ↓reduceIte]
    refine Runs.bind (Runs.registerIdentity hunregA) ?_
    have hrB := Runs.registerIdentity (p := "bob") hunregB
    have hlen1 : setupTr1.length + 4 = 9 := by
      simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [hlen1] at hrB
    refine Runs.bind hrB ?_
    refine Runs.bind (Runs.genSignedPrekey hidB2) ?_
    refine Runs.bind (Runs.genPQPrekey hidB3) ?_
    exact Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.pure () _
  exact hruns.2

theorem setupTrace_r0_len : (setupTrace r0).length = 22 := by
  rw [setupTrace_r0_eq]
  simp [setupTr0, setupTr3, setupTr2, setupTr1,
    genPQPrekeyTr, genSignedPrekeyTr, registerIdentityTr,
    Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem setupSent_r0_eq :
    setupSent r0 =
      [DY.DiffieHellman.dhPk (randTerm 0 32),
       DY.Signature.vk (randTerm 0 32),
       DY.DiffieHellman.dhPk (randTerm 5 32),
       DY.Signature.vk (randTerm 5 32),
       DY.DiffieHellman.dhPk (randTerm 10 32),
       DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
         (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))),
       DY.PQKem.kemPk (randTerm 16 64),
       DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
         (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))] := by
  have hstep : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E),
      (newIndices Trace.nil (tr.append e)).filterMap (fun i => (tr.append e).getMessageSentAt i) =
        (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) ++
          match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
              Option DY.Network.ExecEntryT) with
          | none => []
          | some entry => [entry.msg] := by
    intro E _ tr e
    have hcongr : ∀ (l : List Nat) (f g : Nat → Option DY.Bytes),
        (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
      intro l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
    have hni : newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
      unfold newIndices
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat, Nat.zero_add, Nat.one_mul]
    rw [hni, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    congr 1
    · refine hcongr _ _ _ fun i hi => ?_
      unfold newIndices at hi
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero, List.mem_range'_1,
        Nat.zero_add] at hi
      have hi2 : i < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?, hi.2, hi2,
        ↓reduceDIte, DY.Trace.at_le tr (tr.append e) i hi.2 (DY.Trace.append_le tr e)]
    · simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, DY.Trace.at?,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Nat.lt_succ_self, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]
      cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option DY.Network.ExecEntryT) <;> rfl
  have hnil : (newIndices Trace.nil (Trace.nil : ExecTrace)).filterMap
      (fun i => (Trace.nil : ExecTrace).getMessageSentAt i) = [] := by
    simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      (newIndices Trace.nil (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE m))).filterMap
        (fun i => (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE m)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) ++ [m] :=
    fun tr m => hstep tr (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE m)
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      (newIndices Trace.nil (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.RndE n))).filterMap
        (fun i => (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.RndE n)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr n; rw [hstep]; exact List.append_nil _
  have hev : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      (newIndices Trace.nil (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.EvP ev))).filterMap
        (fun i => (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.EvP ev)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr ev; rw [hstep]; exact List.append_nil _
  have hst : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.PQXDH.PQXDHState),
      (newIndices Trace.nil (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP me s))).filterMap
        (fun i => (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP me s)).getMessageSentAt i) =
      (newIndices Trace.nil tr).filterMap (fun i => tr.getMessageSentAt i) := by
    intro tr me s; rw [hstep]; exact List.append_nil _
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr
    simp [hl1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr
    simp [hl2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [setupSent, setupTrace_r0_eq]
  unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
  unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
  unfold setupTr2 registerIdentityTr; dsimp only; rw [hl1]
  unfold setupTr1 registerIdentityTr; dsimp only
  simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, hnet, hrnd, hev, hst, hnil,
    List.nil_append, List.cons_append]
  rfl

theorem setupPublic_r0_5 :
    setupPublic r0 5 =
      DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) := by
  rw [setupPublic, setupSent_r0_eq]; rfl

theorem setupPublic_r0_6 :
    setupPublic r0 6 = DY.PQKem.kemPk (randTerm 16 64) := by
  rw [setupPublic, setupSent_r0_eq]; rfl

theorem setupPublic_r0_7 :
    setupPublic r0 7 =
      DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) := by
  rw [setupPublic, setupSent_r0_eq]; rfl

theorem setupRandomsAt_eq_of_fits {r : ProtocolSetup} (hp : FitsPins r) :
    setupRandomsAt r = setupRandomsAt r0 := by
  unfold setupRandomsAt
  rw [setupTrace_eq_of_parties hp.ha hp.hb hp.hopk]

theorem setupPublic_eq_of_fits {r : ProtocolSetup} (hp : FitsPins r) (k : Nat) :
    setupPublic r k = setupPublic r0 k := by
  unfold setupPublic setupSent
  rw [setupTrace_eq_of_parties hp.ha hp.hb hp.hopk]

theorem ghostAndSemMatchSetup_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hp : FitsPins r) (hc : GhostAndSemMatchSetup compI0 r S g) :
    GhostAndSemMatchSetup compI0 r S (gClean g) := by
  refine ⟨?_, ?_, hc.2.2⟩
  · intro p hp_mem
    have hp_r0 : p ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
      rwa [setupRandomsAt_eq_of_fits hp, setupRandomsAt_r0_eq] at hp_mem
    have hlt : p.1 < 22 := by
      rcases List.mem_cons.mp hp_r0 with rfl | h1
      · decide
      · rcases List.mem_cons.mp h1 with rfl | h2
        · decide
        · rcases List.mem_cons.mp h2 with rfl | h3
          · decide
          · rcases List.mem_cons.mp h3 with rfl | h4
            · decide
            · rcases List.mem_cons.mp h4 with rfl | h5
              · decide
              · rcases List.mem_singleton.mp h5 with rfl; decide
    rw [gClean_σ_lt22 g hlt]
    exact hc.1 p hp_mem
  · intro t ht
    have h1 := hc.2.1 t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    suffices hEq : gamma' compI0 S (gClean g) t = gamma' compI0 S g t by
      unfold gamma at h1 ⊢; rw [hEq]; exact h1
    rcases ht with rfl | rfl | rfl
    · unfold ProtocolSetup.spkSigTerm
      rw [setupPublic_eq_of_fits hp 5, setupPublic_r0_5]
      exact gamma'_sign_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))
        (gamma'_rand_lt22 S g (by decide))
        (gamma'_concat_eq_of_eq S (gClean g) g (gamma'_lit_eq_gClean S g _)
          (gamma'_dhPk_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))))
    · unfold ProtocolSetup.pqpkPubTerm
      rw [setupPublic_eq_of_fits hp 6, setupPublic_r0_6]
      exact gamma'_kemPk_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))
    · unfold ProtocolSetup.pqpkSigTerm
      rw [setupPublic_eq_of_fits hp 7, setupPublic_r0_7]
      exact gamma'_sign_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))
        (gamma'_rand_lt22 S g (by decide))
        (gamma'_concat_eq_of_eq S (gClean g) g (gamma'_lit_eq_gClean S g _)
          (gamma'_kemPk_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))))

abbrev ikASkClean : DY.Bytes := randTerm 0 32
abbrev ikAPkClean : DY.Bytes := DY.DiffieHellman.dhPk ikASkClean
abbrev ikBSkClean : DY.Bytes := randTerm 5 32
abbrev ikBPkClean : DY.Bytes := DY.DiffieHellman.dhPk ikBSkClean
abbrev spkBSkClean : DY.Bytes := randTerm 10 32
abbrev spkBPkClean : DY.Bytes := DY.DiffieHellman.dhPk spkBSkClean
abbrev pqskBClean : DY.Bytes := randTerm 16 64
abbrev pqpkBClean : DY.Bytes := DY.PQKem.kemPk pqskBClean

noncomputable def oClean : DY.Libsignal.PQXDH.AliceHandshakeOut :=
  CompTrace.aliceOut (setupTrace r0) ikASkClean ikBPkClean spkBPkClean pqpkBClean none

noncomputable def stA0Clean : TRState :=
  localAliceStartState (setupTrace r0) "bob" oClean

abbrev coins1Clean (cl1 : Nat) : DY.Bytes := randTerm 32 cl1
noncomputable def spqrA1Clean (cl1 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend stA0Clean.spqr (coins1Clean cl1)).1
noncomputable def salt1Clean (cl1 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend stA0Clean.spqr (coins1Clean cl1)).2.1
noncomputable def pqm1Clean (cl1 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend stA0Clean.spqr (coins1Clean cl1)).2.2
noncomputable def stA1Clean (cl1 : Nat) : TRState :=
  localEncState stA0Clean (coins1Clean cl1)
noncomputable def m1Clean (cl1 : Nat) : DY.Bytes :=
  localEncMsg stA0Clean (coins1Clean cl1) (salt1Clean cl1) (randTerm 31 32)

abbrev coins2Clean (cl2 : Nat) : DY.Bytes := randTerm 39 cl2
noncomputable def spqrA2Clean (cl1 cl2 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend (spqrA1Clean cl1) (coins2Clean cl2)).1
noncomputable def salt2Clean (cl1 cl2 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend (spqrA1Clean cl1) (coins2Clean cl2)).2.1
noncomputable def pqm2Clean (cl1 cl2 : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend (spqrA1Clean cl1) (coins2Clean cl2)).2.2
noncomputable def stA2Clean (cl1 cl2 : Nat) : TRState :=
  localEncState (stA1Clean cl1) (coins2Clean cl2)
noncomputable def m2Clean (cl1 cl2 : Nat) : DY.Bytes :=
  localEncMsg (stA1Clean cl1) (coins2Clean cl2) (salt2Clean cl1 cl2) (randTerm 38 32)

-- OpaqueAt lemmas for litOf, zeroKey, kemPk, spqrSend outputs
theorem opaqueAt_of_termAt_lit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {b : DY.Bytes} {id : Nat} (hid : id < dagSize)
    (hop : dagOp id = .lit (dagBytes id))
    (ht : DagTermAt S g pts b id) : OpaqueAt S g pts b id := by
  refine ⟨ht.2.1, ?_, ht.2.2.2⟩
  rw [ht.2.2.1, dagShape_unfold (topo_of_nodes dag_nodes_ok) hid]
  simp only [evalDagShapeAux, hop]

theorem opaqueAt_litOf {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} (hid : id < dagSize) (hop : dagOp id = .lit (dagBytes id)) :
    OpaqueAt S g pts (litOf (dagBytes id)) id :=
  opaqueAt_of_termAt_lit hid hop (termAt_litOf dag_nodes_ok hid hop)

theorem opaqueAt_zeroKey {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} :
    OpaqueAt S g pts DY.Spqr.zeroKey 7 :=
  opaqueAt_of_termAt_lit (by decide) (dagOp_lit_eq rfl (by decide +kernel))
    (termAt_lit (ba := ⟨Array.replicate 32 0⟩) dag_nodes_ok (by decide)
      (dagOp_lit_eq rfl (by decide +kernel)))

theorem opaqueAt_kemPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {sk : DY.Bytes} {id : Nat}
    (hbs : gamma compI0 S g (DY.PQKem.kemPk sk) = dagBytes id)
    (hsk : DagSafeMemo S g pts sk) :
    OpaqueAt S g pts (DY.PQKem.kemPk sk) id := by
  refine ⟨hbs, ?_, safeMemo_kemPk hsk⟩
  rw [← hbs]; unfold gamma gamma'
  rw [show DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI0 S g)]
  rfl

theorem shape_eq_litOf_spqrSend_key {S : OpaqueSymbolSemantics} {g : Ghost}
    (st coins : DY.Bytes) :
    (gamma' compI0 S g (DY.Spqr.spqrSend st coins).2.1).shape =
      litOf (gamma compI0 S g (DY.Spqr.spqrSend st coins).2.1) := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · unfold gamma gamma' DY.Spqr.spqrChainKey
    rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll compI0 S g)]
    rfl
  · unfold gamma gamma'
    rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll compI0 S g)]
    rfl

theorem shape_eq_litOf_spqrSend_msg {S : OpaqueSymbolSemantics} {g : Ghost}
    (st coins : DY.Bytes) :
    (gamma' compI0 S g (DY.Spqr.spqrSend st coins).2.2).shape =
      litOf (gamma compI0 S g (DY.Spqr.spqrSend st coins).2.2) := by
  unfold DY.Spqr.spqrSend gamma gamma'
  dsimp only
  rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll compI0 S g)]
  rfl

-- Part 2C2: Alice oClean / stA0Clean / stA1Clean / stA2Clean DagTermAt & CleanDagHyp from SPQR pins

theorem agree_dhPk (pkSk sk : DY.Bytes) :
    DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk pkSk) sk =
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk pkSk) sk := by
  unfold DY.Libsignal.PQXDH.agree DY.X25519.normalizeX25519Key
  dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

theorem secretBytes_at_of_fits {r : ProtocolSetup} (hp : FitsPins r) :
    r.fresh 0 32 = setup.aliceId ∧
    r.fresh 5 32 = setup.bobId ∧
    r.fresh 10 32 = setup.spk ∧
    r.fresh 11 64 = fillFresh 11 64 ∧
    r.fresh 16 64 = fillFresh 16 64 ∧
    r.fresh 17 64 = fillFresh 17 64 := by
  have h0 := hp.hsec0; have h1 := hp.hsec1; have h2 := hp.hsec2
  have h3 := hp.hsec3; have h4 := hp.hsec4; have h5 := hp.hsec5
  unfold secretBytes at h0 h1 h2 h3 h4 h5
  rw [setupRandomsAt_eq_of_fits hp, setupRandomsAt_r0_eq] at h0 h1 h2 h3 h4 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem dagTermAt_oClean {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkBClean salt1T pqm1T salt2T pqm2T) :
    DagTermAt S g pts oClean.ek 68 ∧
    DagTermAt S g pts oClean.ct 70 ∧
    DagTermAt S g pts oClean.keys.rk 82 ∧
    DagTermAt S g pts oClean.keys.ck 84 ∧
    DagTermAt S g pts oClean.keys.pqr 86 := by
  have hlen := setupTrace_r0_len
  unfold oClean CompTrace.aliceOut DY.Libsignal.PQXDH.aliceAgreement
  dsimp only
  rw [hlen]
  have hdh1 : DagTermAt S g pts (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean) 74 := by
    rw [agree_dhPk]; exact dagN_74 hw
  have hdh2 : DagTermAt S g pts (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm 22 32)) 75 := by
    rw [agree_dhPk]; exact dagN_75_symm hw
  have hdh3 : DagTermAt S g pts (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm 22 32)) 76 := by
    rw [agree_dhPk]; exact dagN_76_symm hw
  have hss : DagTermAt S g pts (DY.PQKem.kemEncap pqpkBClean (randTerm 23 32)).2 71 := dagN_71 hw
  have hc3 := termAt_concat (id := 77) dag_nodes_ok (by decide) rfl hdh3 hss
  have hc2 := termAt_concat (id := 78) dag_nodes_ok (by decide) rfl hdh2 hc3
  have hc1 := termAt_concat (id := 79) dag_nodes_ok (by decide) rfl hdh1 hc2
  have hikm : DagTermAt S g pts
      (DY.Libsignal.PQXDH.pqxdhIkm
        (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean)
        (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm 22 32))
        (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm 22 32))
        none
        (DY.PQKem.kemEncap pqpkBClean (randTerm 23 32)).2) 80 :=
    termAt_concat (id := 80) dag_nodes_ok (by decide) rfl (dagN_6 hw) hc1
  have hprk := termAt_kdf (id := 81) dag_nodes_ok (by decide) rfl (dagN_7 hw) hikm
  have hb1 := termAt_kdf (id := 82) dag_nodes_ok (by decide) rfl hprk (dagN_18 hw)
  have hkc2 := termAt_concat (id := 83) dag_nodes_ok (by decide) rfl hb1 (dagN_19 hw)
  have hb2 := termAt_kdf (id := 84) dag_nodes_ok (by decide) rfl hprk hkc2
  have hkc3 := termAt_concat (id := 85) dag_nodes_ok (by decide) rfl hb2 (dagN_20 hw)
  have hb3 := termAt_kdf (id := 86) dag_nodes_ok (by decide) rfl hprk hkc3
  exact ⟨dagN_68 hw, dagN_70 hw, hb1, hb2, hb3⟩

theorem safeMemo_coinsClean {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    (∀ cl1, (cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64) → DagSafeMemo S g pts (coins1Clean cl1)) ∧
    (∀ cl2, (cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) → DagSafeMemo S g pts (coins2Clean cl2)) := by
  refine ⟨?_, ?_⟩
  · rintro cl1 (rfl | rfl | rfl)
    · exact safeMemo_randTerm_zero 32
    · exact (dagN_93 hw).safeMemo
    · exact (dagN_94 hw).safeMemo
  · rintro cl2 (rfl | rfl | rfl)
    · exact safeMemo_randTerm_zero 39
    · exact (dagN_95 hw).safeMemo
    · exact (dagN_96 hw).safeMemo

theorem cleanDagHyp_of_spqrPins {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hc : GhostAndSemMatchSetup compI0 r S g)
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hpt1 : randTerm 31 32 ∈ pts)
    (hpt2 : randTerm 38 32 ∈ pts)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24) :
    CleanDagHyp S (gClean g) pts pqpkBClean
      (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2) := by
  have hc' := ghostAndSemMatchSetup_gClean hp hc
  obtain ⟨hf0, hf5, hf10, hf11, hf16, hf17⟩ := secretBytes_at_of_fits hp
  have hmemR : ∀ p ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)],
      p ∈ setupRandomsAt r := by
    intro p hp0; rwa [setupRandomsAt_eq_of_fits hp, setupRandomsAt_r0_eq]
  have hσ_0 : (gClean g).σ 0 32 = dagBytes 26 := by
    rw [hc'.1 (0, 32) (hmemR _ (by simp)), hf0]; decide +kernel
  have hσ_5 : (gClean g).σ 5 32 = dagBytes 29 := by
    rw [hc'.1 (5, 32) (hmemR _ (by simp)), hf5]; decide +kernel
  have hσ_10 : (gClean g).σ 10 32 = dagBytes 32 := by
    rw [hc'.1 (10, 32) (hmemR _ (by simp)), hf10]; decide +kernel
  have hσ_11 : (gClean g).σ 11 64 = dagBytes 34 := by
    rw [hc'.1 (11, 64) (hmemR _ (by simp)), hf11]; decide +kernel
  have hσ_16 : (gClean g).σ 16 64 = dagBytes 35 := by
    rw [hc'.1 (16, 64) (hmemR _ (by simp)), hf16]; decide +kernel
  have hσ_17 : (gClean g).σ 17 64 = dagBytes 36 := by
    rw [hc'.1 (17, 64) (hmemR _ (by simp)), hf17]; decide +kernel
  have hpqpk_gamma : gamma compI0 S (gClean g) pqpkBClean = dagBytes 25 := by
    have hpub := hc'.2.1 r.pqpkPubTerm (by simp)
    unfold ProtocolSetup.pqpkPubTerm at hpub
    rw [hp.hpqpkPub] at hpub
    rw [setupPublic_eq_of_fits hp 6, setupPublic_r0_6] at hpub
    exact hpub.trans (by decide +kernel)
  have hpqsk_safe : DagSafeMemo S (gClean g) pts pqskBClean :=
    (termAt_rand (id := 35) dag_nodes_ok (by decide) rfl hσ_16).safeMemo
  have hpqpk_op : OpaqueAt S (gClean g) pts pqpkBClean 25 :=
    opaqueAt_kemPk hpqpk_gamma hpqsk_safe
  have hw₀ : CleanDagHyp S (gClean g) pts pqpkBClean
      (litOf (dagBytes 21)) (litOf (dagBytes 22)) (litOf (dagBytes 23)) (litOf (dagBytes 24)) :=
    { hσ_0_32 := hσ_0, hσ_5_32 := hσ_5, hσ_10_32 := hσ_10,
      hσ_11_64 := hσ_11, hσ_16_64 := hσ_16, hσ_17_64 := hσ_17,
      hσ_22_32 := rfl, hσ_23_32 := rfl, hσ_24_32 := rfl,
      hσ_32_32 := by change List.take 32 ev1.coins = dagBytes 93; decide +kernel,
      hσ_32_64 := by change List.take 64 ev1.coins = dagBytes 94; decide +kernel,
      hσ_39_32 := by change List.take 32 ev2.coins = dagBytes 95; decide +kernel,
      hσ_39_64 := by change List.take 64 ev2.coins = dagBytes 96; decide +kernel,
      hσ_45_32 := rfl,
      hσ_pt1 := rfl, hpt1_mem := hpt1,
      hσ_pt2 := rfl, hpt2_mem := hpt2,
      haddr := fun _ => rfl,
      hzero := opaqueAt_zeroKey,
      hpqpk := hpqpk_op,
      hsalt1 := opaqueAt_litOf (by decide) (dagOp_lit_eq rfl (by decide +kernel)),
      hpqm1 := opaqueAt_litOf (by decide) (dagOp_lit_eq rfl (by decide +kernel)),
      hsalt2 := opaqueAt_litOf (by decide) (dagOp_lit_eq rfl (by decide +kernel)),
      hpqm2 := opaqueAt_litOf (by decide) (dagOp_lit_eq rfl (by decide +kernel)) }
  have hpqr_safe : DagSafeMemo S (gClean g) pts oClean.keys.pqr :=
    (dagTermAt_oClean hw₀).2.2.2.2.safeMemo
  have hspqr0_safe : DagSafeMemo S (gClean g) pts stA0Clean.spqr :=
    safeMemo_spqrInit hpqr_safe (safeMemo_lit_short (by decide))
  obtain ⟨hc1_safe, hc2_safe⟩ := safeMemo_coinsClean hw₀
  obtain ⟨hspqr1_safe, hsalt1_safe, hpqm1_safe⟩ :=
    safeMemo_spqrSend hspqr0_safe (hc1_safe cl1 hcl1)
  obtain ⟨_, hsalt2_safe, hpqm2_safe⟩ :=
    safeMemo_spqrSend hspqr1_safe (hc2_safe cl2 hcl2)
  exact
    { hw₀ with
      hsalt1 := ⟨hsalt1, (shape_eq_litOf_spqrSend_key _ _).trans (congrArg litOf hsalt1), hsalt1_safe⟩,
      hpqm1 := ⟨hpqm1, (shape_eq_litOf_spqrSend_msg _ _).trans (congrArg litOf hpqm1), hpqm1_safe⟩,
      hsalt2 := ⟨hsalt2, (shape_eq_litOf_spqrSend_key _ _).trans (congrArg litOf hsalt2), hsalt2_safe⟩,
      hpqm2 := ⟨hpqm2, (shape_eq_litOf_spqrSend_msg _ _).trans (congrArg litOf hpqm2), hpqm2_safe⟩ }

theorem dagTermAt_aliceRatchetAndMsgs {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {cl1 cl2 : Nat}
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    DagTermAt S g pts stA0Clean.rk 89 ∧
    DagTermAt S g pts stA0Clean.dhs 72 ∧
    DagTermAt S g pts stA0Clean.cks 91 ∧
    DagTermAt S g pts stA0Clean.sid 92 ∧
    DagTermAt S g pts (stA1Clean cl1).cks 98 ∧
    DagTermAt S g pts (m1Clean cl1) 111 ∧
    DagTermAt S g pts (stA2Clean cl1 cl2).cks 113 ∧
    DagTermAt S g pts (m2Clean cl1 cl2) 126 := by
  obtain ⟨_, _, hrk0, _, _⟩ := dagTermAt_oClean hw
  have hlen := setupTrace_r0_len
  have hdhsA : DagTermAt S g pts stA0Clean.dhs 72 := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [hlen]; exact dagN_72 hw
  have hdhsPk : DagTermAt S g pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73 := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [hlen]; exact dagN_73 hw
  have hdhInit : DagTermAt S g pts (DY.Libsignal.PQXDH.agree oClean.spk stA0Clean.dhs) 87 := by
    unfold stA0Clean localAliceStartState oClean CompTrace.aliceOut; dsimp only; rw [hlen]
    rw [agree_dhPk]; exact dagN_87_symm hw
  have hprk0 := termAt_kdf (id := 88) dag_nodes_ok (by decide) rfl hrk0 hdhInit
  have hrkA0 : DagTermAt S g pts stA0Clean.rk 89 :=
    termAt_kdf (id := 89) dag_nodes_ok (by decide) rfl hprk0 (dagN_13 hw)
  have hc2_0 := termAt_concat (id := 90) dag_nodes_ok (by decide) rfl hrkA0 (dagN_14 hw)
  have hcks0 : DagTermAt S g pts stA0Clean.cks 91 :=
    termAt_kdf (id := 91) dag_nodes_ok (by decide) rfl hprk0 hc2_0
  have hsid0 : DagTermAt S g pts stA0Clean.sid 92 :=
    termAt_concat (id := 92) dag_nodes_ok (by decide) rfl hdhsPk hrk0
  -- Encrypt 1
  have hseed1 : DagTermAt S g pts (kdfCk stA0Clean.cks).2 97 :=
    termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0 (dagN_2 hw)
  have hcks1 : DagTermAt S g pts (stA1Clean cl1).cks 98 :=
    termAt_kdf (id := 98) dag_nodes_ok (by decide) rfl hcks0 (dagN_3 hw)
  obtain ⟨tck1, tmk1, tiv1⟩ := termAt_trMsgKeys
    (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
    dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) hseed1
  have hct1 := termAt_symEncPt (id := 105) dag_nodes_ok (by decide)
    (congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel) : dagOp 105 = .symEncPt 100 104 31 ev1.input)
    tck1 tiv1 hw.hpt1_mem hw.hσ_pt1 (by decide +kernel)
  have hwire1 := termAt_trWire (id := 106) dag_nodes_ok (by decide)
    (congrArg (DagOp.trWire messageVersion 73 0 0 105 22) (by decide +kernel) :
      dagOp 106 = .trWire messageVersion 73 0 0 105 22 cleanAddrBs)
    hdhsPk hct1 (dagN_22 hw) (hw.haddr _)
  have hmac1 := termAt_computeMac
    (c1_id := 107) (c2_id := 108) (h_id := 109) (t_id := 110)
    dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk1 (dagN_28 hw) (dagN_31 hw) hwire1
  have hm1 : DagTermAt S g pts (m1Clean cl1) 111 :=
    termAt_concat (id := 111) dag_nodes_ok (by decide) rfl hwire1 hmac1
  -- Encrypt 2
  have hseed2 : DagTermAt S g pts (kdfCk (stA1Clean cl1).cks).2 112 :=
    termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1 (dagN_2 hw)
  have hcks2 : DagTermAt S g pts (stA2Clean cl1 cl2).cks 113 :=
    termAt_kdf (id := 113) dag_nodes_ok (by decide) rfl hcks1 (dagN_3 hw)
  obtain ⟨tck2, tmk2, tiv2⟩ := termAt_trMsgKeys
    (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
    dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_23 hw) hseed2
  have hct2 := termAt_symEncPt (id := 120) dag_nodes_ok (by decide)
    (congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel) : dagOp 120 = .symEncPt 115 119 38 ev2.input)
    tck2 tiv2 hw.hpt2_mem hw.hσ_pt2 (by decide +kernel)
  have hwire2 := termAt_trWire (id := 121) dag_nodes_ok (by decide)
    (congrArg (DagOp.trWire messageVersion 73 1 0 120 24) (by decide +kernel) :
      dagOp 121 = .trWire messageVersion 73 1 0 120 24 cleanAddrBs)
    hdhsPk hct2 (dagN_24 hw) (hw.haddr _)
  have hmac2 := termAt_computeMac
    (c1_id := 122) (c2_id := 123) (h_id := 124) (t_id := 125)
    dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk2 (dagN_28 hw) (dagN_31 hw) hwire2
  have hm2 : DagTermAt S g pts (m2Clean cl1 cl2) 126 :=
    termAt_concat (id := 126) dag_nodes_ok (by decide) rfl hwire2 hmac2
  exact ⟨hrkA0, hdhsA, hcks0, hsid0, hcks1, hm1, hcks2, hm2⟩

theorem safeMemo2_aliceStates {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA0Clean⟩ : DY.PersistentLocalState.LocalState TRState)) ∧
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA1Clean cl1⟩ : DY.PersistentLocalState.LocalState TRState)) ∧
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA2Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  obtain ⟨_, _, _, hck0, hpqr0⟩ := dagTermAt_oClean hw
  obtain ⟨hrkA0, hdhsA, hcks0, hsid0, hcks1, _, hcks2, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  obtain ⟨hc1_safe, hc2_safe⟩ := safeMemo_coinsClean hw
  have hspqr0 : DagSafeMemo S g pts stA0Clean.spqr :=
    safeMemo_spqrInit hpqr0.safeMemo (safeMemo_lit_short (by decide))
  have hspqr1 : DagSafeMemo S g pts (stA1Clean cl1).spqr :=
    (safeMemo_spqrSend hspqr0 (hc1_safe cl1 hcl1)).1
  have hspqr2 : DagSafeMemo S g pts (stA2Clean cl1 cl2).spqr :=
    (safeMemo_spqrSend hspqr1 (hc2_safe cl2 hcl2)).1
  have hmyIk : DagSafeMemo S g pts stA0Clean.myIk := (dagN_28 hw).safeMemo
  have hpeerIk : DagSafeMemo S g pts stA0Clean.peerIk := (dagN_31 hw).safeMemo
  have hspkPk : DagSafeMemo S g pts oClean.spk := (dagN_33 hw).safeMemo
  have hs0 : SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA0Clean⟩ : DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := ⟨"alice", stA0Clean⟩)
      (cLast := { ratchetKey := oClean.spk, chainKey := oClean.keys.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqr0 ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmyIk
      · exact hpeerIk
      · exact hrkA0.safeMemo
      · exact hdhsA.safeMemo
      · exact hcks0.safeMemo
      · exact hsid0.safeMemo
    · intro c hc
      simp only [stA0Clean, localAliceStartState, List.mem_singleton] at hc
      subst hc; exact ⟨hspkPk, hck0.safeMemo⟩
  have hs1 : SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA1Clean cl1⟩ : DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := ⟨"alice", stA1Clean cl1⟩)
      (cLast := { ratchetKey := oClean.spk, chainKey := oClean.keys.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqr1 ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmyIk
      · exact hpeerIk
      · exact hrkA0.safeMemo
      · exact hdhsA.safeMemo
      · exact hcks1.safeMemo
      · exact hsid0.safeMemo
    · intro c hc
      simp only [stA1Clean, localEncState, stA0Clean, localAliceStartState, List.mem_singleton] at hc
      subst hc; exact ⟨hspkPk, hck0.safeMemo⟩
  have hs2 : SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", stA2Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := ⟨"alice", stA2Clean cl1 cl2⟩)
      (cLast := { ratchetKey := oClean.spk, chainKey := oClean.keys.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqr2 ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmyIk
      · exact hpeerIk
      · exact hrkA0.safeMemo
      · exact hdhsA.safeMemo
      · exact hcks2.safeMemo
      · exact hsid0.safeMemo
    · intro c hc
      simp only [stA2Clean, stA1Clean, localEncState, stA0Clean, localAliceStartState, List.mem_singleton] at hc
      subst hc; exact ⟨hspkPk, hck0.safeMemo⟩
  exact ⟨hs0, hs1, hs2⟩

end Step2CleanStateAndSafe
-- END PART2C CLEAN STATE AND SAFEMEMO

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
