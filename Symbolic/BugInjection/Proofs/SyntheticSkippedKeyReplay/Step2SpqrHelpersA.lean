/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2Trials

/-!
# Helper Congruence & Concrete Evaluation Lemmas for Alice SPQR Extraction
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

noncomputable section Step2Part2D

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.Composed
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
open ByteSpecs (hmacWith sha256With)
open _root_.Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

local macro "at?_localEncTr_tac" : tactic =>
  `(tactic| (dsimp only [localEncTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))


theorem dhPk_inj_loc {x y : DY.Bytes}
    (h : DY.DiffieHellman.dhPk x = DY.DiffieHellman.dhPk y) : x = y := by
  have hv := congrArg (fun t : DY.Bytes => t.view? DY.DiffieHellman.DhPk.SubF) h
  dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk] at hv
  simp only [_root_.DY.BytesView.view_pack, Option.some.injEq] at hv
  exact congrArg DY.DiffieHellman.DhPk.SubF.sk hv

theorem randTerm_inj_loc {t1 n1 t2 n2 : Nat}
    (h : randTerm t1 n1 = randTerm t2 n2) : t1 = t2 ∧ n1 = n2 := by
  have hv := congrArg (fun t : DY.Bytes => t.view? DY.Random.Random) h
  dsimp only [randTerm] at hv
  simp only [_root_.DY.BytesView.view_pack, Option.some.injEq] at hv
  exact ⟨congrArg DY.Random.Random.timestamp hv, congrArg DY.Random.Random.size hv⟩

theorem readVarint_paddedVarint_zero :
    ∀ (n : Nat) (rest : HwBytes),
      DY.Libsignal.Refinement.readVarint (DY.Libsignal.Refinement.paddedVarint n 0 ++ rest) =
        some (n, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rest
    rw [DY.Libsignal.Refinement.paddedVarint]
    by_cases hlt : n < 128
    · simp only [hlt, and_self, ↓reduceIte, List.singleton_append, DY.Libsignal.Refinement.readVarint]
      have hbv : (BitVec.ofNat 8 n).toNat = n := Nat.mod_eq_of_lt (by omega)
      simp [hbv, hlt]
    · simp only [hlt, false_and, ↓reduceIte, List.cons_append, DY.Libsignal.Refinement.readVarint]
      have hbv : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 :=
        Nat.mod_eq_of_lt (by omega)
      have hge : ¬ (n % 128 + 128) < 128 := by omega
      simp only [hbv, hge, ↓reduceIte, ih (n / 128) (Nat.div_lt_self (by omega) (by decide)) rest,
        Option.map_some]
      exact congrArg some (Prod.ext (by omega) rfl)

theorem trWireBytes_pq_inj {addr : HwBytes} {f : DY.Libsignal.Refinement.WireFields}
    {pq pq₀ : HwBytes} (hpq₀ : pq₀ ≠ [])
    (heq : DY.Libsignal.Refinement.trWireBytes addr DY.Libsignal.Refinement.canonicalVariation f pq =
           DY.Libsignal.Refinement.trWireBytes addr DY.Libsignal.Refinement.canonicalVariation f pq₀) :
    pq = pq₀ := by
  unfold DY.Libsignal.Refinement.trWireBytes DY.Libsignal.Refinement.trFields
    DY.Libsignal.Refinement.honestTrItems at heq
  have htl := (List.cons.inj heq).2
  simp only [↓reduceIte, List.flatMap_append] at htl
  have hpre : List.flatMap (DY.Libsignal.Refinement.trItemEncode addr DY.Libsignal.Refinement.canonicalVariation f pq)
      DY.Libsignal.Refinement.canonicalVariation.fields =
    List.flatMap (DY.Libsignal.Refinement.trItemEncode addr DY.Libsignal.Refinement.canonicalVariation f pq₀)
      DY.Libsignal.Refinement.canonicalVariation.fields := rfl
  have hsuf : List.flatMap (DY.Libsignal.Refinement.trItemEncode addr DY.Libsignal.Refinement.canonicalVariation f pq)
      (if addr = [] then [] else [DY.TrWire.FieldItem.known 6 0 0]) =
    List.flatMap (DY.Libsignal.Refinement.trItemEncode addr DY.Libsignal.Refinement.canonicalVariation f pq₀)
      (if addr = [] then [] else [DY.TrWire.FieldItem.known 6 0 0]) := by
    split <;> rfl
  rw [hpre, hsuf] at htl
  have hmid := List.append_cancel_right (List.append_cancel_left htl)
  by_cases hpq : pq = []
  · subst hpq
    simp only [↓reduceIte, hpq₀, List.flatMap_nil, List.flatMap_cons, List.append_nil,
      DY.Libsignal.Refinement.trItemEncode, DY.Libsignal.Refinement.encodeField] at hmid
    have h42 : DY.Libsignal.Refinement.paddedVarint 42 0 = [0x2a#8] := by
      rw [DY.Libsignal.Refinement.paddedVarint]; decide
    rw [h42] at hmid
    cases hmid
  · simp only [hpq, hpq₀, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      DY.Libsignal.Refinement.trItemEncode, DY.Libsignal.Refinement.encodeField, List.append_assoc] at hmid
    have hvar := List.append_cancel_left hmid
    have hr := congrArg DY.Libsignal.Refinement.readVarint hvar
    rw [readVarint_paddedVarint_zero, readVarint_paddedVarint_zero] at hr
    exact (Prod.mk.inj (Option.some.inj hr)).2

theorem gamma_computeMac_length {S : OpaqueSymbolSemantics} {g : Ghost}
    (mk a b w : DY.Bytes) :
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w)).length = 8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac gamma gamma'
  rw [show DY.Trunc.trunc8 (DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat a (DY.Concat.concat b w))) =
      ({ input := DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat a (DY.Concat.concat b w)) } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq DY.Libsignal.Composed.Refinement.concretizeTrunc (concretizeAll compI0 S g)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeTrunc, DY.Libsignal.Composed.Refinement.node]
  have hlen : (DY.Bytes.rec (concretizeAll compI0 S g)
      (DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat a (DY.Concat.concat b w)))).bytes.length = 32 := by
    change (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac mk _)).length = 32
    rw [gamma_hmac_compI0]
    exact Symbolic.BugInjection.Proofs.Common443.CompRTag.sha256With_length _ _
  rw [List.length_take, hlen]
  rfl

theorem gamma_dhPk_pack_eq_loc {S : OpaqueSymbolSemantics} {g : Ghost} (s : DY.Bytes) :
    gamma compI0 S g (({ sk := s } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack) =
      Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupPub
        (DY.Libsignal.Composed.Refinement.clamp (gamma compI0 S g s)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeDhPk compI0) (concretizeAll compI0 S g)]
  rfl

theorem gamma_dhPk_eq_loc {S : OpaqueSymbolSemantics} {g : Ghost} (s : DY.Bytes) :
    gamma compI0 S g (DY.DiffieHellman.dhPk s) =
      Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupPub
        (DY.Libsignal.Composed.Refinement.clamp (gamma compI0 S g s)) :=
  gamma_dhPk_pack_eq_loc s

theorem gamma_dhPk_congr_loc {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {s₁ s₂ : DY.Bytes}
    (hs : gamma compI0 S g₁ s₁ = gamma compI0 S g₂ s₂) :
    gamma compI0 S g₁ (DY.DiffieHellman.dhPk s₁) = gamma compI0 S g₂ (DY.DiffieHellman.dhPk s₂) := by
  rw [gamma_dhPk_eq_loc, gamma_dhPk_eq_loc, hs]

theorem gamma_dh_pack_eq_loc {S : OpaqueSymbolSemantics} {g : Ghost} (p s : DY.Bytes) :
    gamma compI0 S g (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupDh
        (DY.Libsignal.Composed.Refinement.clamp (gamma compI0 S g s)) (gamma compI0 S g p) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeDh compI0) (concretizeAll compI0 S g)]
  rfl

theorem gamma_dh_dhPk_eq_loc {S : OpaqueSymbolSemantics} {g : Ghost} (a b : DY.Bytes) :
    gamma compI0 S g (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) b) =
      Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupDh
        (DY.Libsignal.Composed.Refinement.clamp (gamma compI0 S g b))
        (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compLookupPub
          (DY.Libsignal.Composed.Refinement.clamp (gamma compI0 S g a))) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF (DY.DiffieHellman.dhPk a)
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i a' heq
    rw [heq] at hv; simp only at hv
    change DY.DiffieHellman.dhPk a' = DY.DiffieHellman.dhPk a at hv
    have ha' : a' = a := dhPk_inj_loc hv
    subst ha'
    split
    · rw [gamma_dh_pack_eq_loc, gamma_dhPk_pack_eq_loc]
    · rw [gamma_dh_pack_eq_loc, gamma_dhPk_pack_eq_loc,
          Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compLookupDh_comm]
  · rename_i hne
    rw [show DY.DiffieHellman.dhPk a = ({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
        _root_.DY.BytesView.view_pack] at hne
    cases hne

theorem gamma_dh_dhPk_congr_loc {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {a₁ b₁ a₂ b₂ : DY.Bytes}
    (ha : gamma compI0 S g₁ a₁ = gamma compI0 S g₂ a₂)
    (hb : gamma compI0 S g₁ b₁ = gamma compI0 S g₂ b₂) :
    gamma compI0 S g₁ (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a₁) b₁) =
      gamma compI0 S g₂ (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a₂) b₂) := by
  rw [gamma_dh_dhPk_eq_loc, gamma_dh_dhPk_eq_loc, ha, hb]

theorem gamma_hmac_congr_loc {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {k₁ m₁ k₂ m₂ : DY.Bytes}
    (hk : gamma compI0 S g₁ k₁ = gamma compI0 S g₂ k₂)
    (hm : gamma compI0 S g₁ m₁ = gamma compI0 S g₂ m₂) :
    gamma compI0 S g₁ (DY.Libsignal.TripleRatchet.hmac k₁ m₁) =
      gamma compI0 S g₂ (DY.Libsignal.TripleRatchet.hmac k₂ m₂) := by
  rw [gamma_hmac_compI0, gamma_hmac_compI0, hk, hm]

theorem gamma_kemEncap_snd_congr_loc {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost} {p₁ e₁ p₂ e₂ : DY.Bytes}
    (hp : gamma compI0 S g₁ p₁ = gamma compI0 S g₂ p₂)
    (he : gamma compI0 S g₁ e₁ = gamma compI0 S g₂ e₂) :
    gamma compI0 S g₁ (DY.PQKem.kemEncap p₁ e₁).2 = gamma compI0 S g₂ (DY.PQKem.kemEncap p₂ e₂).2 := by
  unfold gamma gamma' at hp he ⊢
  rw [show (DY.PQKem.kemEncap p₁ e₁).2 = ({ pk := p₁, entropy := e₁ } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
      show (DY.PQKem.kemEncap p₂ e₂).2 = ({ pk := p₂, entropy := e₂ } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemSS compI0 S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemSS compI0 S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeKemSS,
    DY.Libsignal.Composed.Refinement.node, DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hp, he]
  split <;> rfl

theorem gamma_symEnc_congr_loc {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {k₁ iv₁ m₁ k₂ iv₂ m₂ : DY.Bytes}
    (hk : gamma compI0 S g₁ k₁ = gamma compI0 S g₂ k₂)
    (hiv : gamma compI0 S g₁ iv₁ = gamma compI0 S g₂ iv₂)
    (hm : gamma compI0 S g₁ m₁ = gamma compI0 S g₂ m₂) :
    gamma compI0 S g₁ (DY.SymEnc.symEnc k₁ iv₁ m₁) =
      gamma compI0 S g₂ (DY.SymEnc.symEnc k₂ iv₂ m₂) := by
  unfold gamma gamma' at hk hiv hm ⊢
  rw [show DY.SymEnc.symEnc k₁ iv₁ m₁ = ({ key := k₁, iv := iv₁, msg := m₁ } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
      show DY.SymEnc.symEnc k₂ iv₂ m₂ = ({ key := k₂, iv := iv₂, msg := m₂ } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSym compI0) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSym compI0) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSym, DY.Libsignal.Composed.Refinement.node]
  simp only [hk, hiv, hm]

theorem gamma_trHonestWireMsg_eq {S : OpaqueSymbolSemantics} {g : Ghost}
    (pk : DY.Bytes) (ns pn : UInt32) (ct pq : DY.Bytes) :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.trHonestWireMsg pk ns pn ct pq) =
      DY.Libsignal.Refinement.trWireBytes
        (g.addr (DY.Libsignal.TripleRatchet.trHonestWireMsg pk ns pn ct pq))
        DY.Libsignal.Refinement.canonicalVariation
        { version := DY.Libsignal.TripleRatchet.messageVersion.toNat,
          ratchetKey := gamma compI0 S g pk,
          counter := ns.toNat,
          previousCounter := pn.toNat,
          ciphertext := gamma compI0 S g ct }
        (gamma compI0 S g pq) := by
  unfold gamma gamma'
  rw [show DY.Libsignal.TripleRatchet.trHonestWireMsg pk ns pn ct pq =
      ({ version := DY.Libsignal.TripleRatchet.messageVersion, senderRatchetKey := pk,
         counter := ns, previousCounter := pn, ciphertext := ct, pqRatchet := pq,
         encodingVariation := DY.TrWire.canonicalVariation } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeTrWire g) (concretizeAll compI0 S g)]
  rfl

theorem pqEv_append_other_loc {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E} {k : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.PQXDHEntry) = none)
    (h : ((tr.append e).at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev)) :
    (tr.at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) := by
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h0
  · rw [hnone] at hp; cases hp

theorem pqEv_append_same_loc {tr : ExecTrace} {ev₀ ev : DY.Libsignal.PQXDH.PQXDHEvent} {k : Nat}
    (h : ((tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.EvP ev₀)).at? k :
      Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev)) :
    (tr.at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) ∨
      (k = tr.length ∧ ev = ev₀) := by
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases h with ⟨_, h0⟩ | ⟨rfl, hp⟩
  · exact Or.inl h0
  · rw [Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq] at hp
    injection hp with heq
    injection heq with hev
    exact Or.inr ⟨rfl, hev.symm⟩

theorem pqEv_setupTrace_r0 {k : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (h : ((setupTrace r0).at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev)) :
    (k = 1 ∧ ev = .IdentityRegistered "alice" ikAPkClean (DY.Signature.vk ikASkClean) true) ∨
    (k = 6 ∧ ev = .IdentityRegistered "bob" ikBPkClean (DY.Signature.vk ikBSkClean) true) ∨
    (k = 12 ∧ (match ev with | .SignedPrekeyPublished .. => True | _ => False)) ∨
    (k = 18 ∧ (match ev with | .PQPrekeyPublished .. => True | _ => False)) := by
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr; simp [hl1]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr; simp [hl2]
  rw [setupTrace_r0_eq] at h
  unfold setupTr0 genPQPrekeyTr at h; dsimp only at h
  have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h))
  rcases pqEv_append_same_loc h with h | ⟨hk, rfl⟩
  · have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h)
    unfold setupTr3 genSignedPrekeyTr at h; dsimp only at h
    have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h))
    rcases pqEv_append_same_loc h with h | ⟨hk, rfl⟩
    · have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h)
      unfold setupTr2 registerIdentityTr at h; dsimp only at h
      have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h))
      rcases pqEv_append_same_loc h with h | ⟨hk, hev⟩
      · have h := pqEv_append_other_loc rfl h
        unfold setupTr1 registerIdentityTr at h; dsimp only at h
        have h := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl h))
        rcases pqEv_append_same_loc h with h | ⟨hk, hev⟩
        · have h := pqEv_append_other_loc rfl h
          rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])] at h
          cases h
        · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hev
          exact Or.inl ⟨by simpa [Symbolic.DYBridge.DY.Trace.length_eq_1, length_append_entry] using hk, hev⟩
      · rw [hl1] at hev
        have hk6 : k = 6 := by simp only [length_append_entry, hl1] at hk; exact hk
        exact Or.inr (Or.inl ⟨hk6, hev⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by simpa [hl2, length_append_entry] using hk, trivial⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa [hl3, length_append_entry] using hk, trivial⟩))

theorem forall₂_append_right_loc {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys₁ ys₂ : List β},
      List.Forall₂ R xs (ys₁ ++ ys₂) →
      ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂
  | xs, [], _, h => ⟨[], xs, rfl, .nil, h⟩
  | _, _ :: _, _, @List.Forall₂.cons _ _ _ x _ xs' _ hhd htl =>
    let ⟨xs₁, xs₂, heq, h1, h2⟩ := forall₂_append_right_loc htl
    ⟨x :: xs₁, xs₂, congrArg (x :: ·) heq, .cons hhd h1, h2⟩

theorem forall₂_kyberCoin_flatten {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {t1 : Nat} :
    ∀ (ps : List HwBytes) (js : List Nat) (rest : HwBytes),
      List.Forall₂ (fun p v => BytesMatchEntry compI0 r S g .rng p v) ps
        (js.map fun j => (⟨.rng, [randTerm t1 32], .kyberCoin j, none⟩ : VisEntry)) →
      ps.flatten.length = 4 * js.length ∧
      ∀ k < js.length, ∀ j, js[k]? = some j →
        (g.σ t1 32)[j]? = (ps.flatten ++ rest)[4 * k]?
  | [], [], _, _ => ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | p :: ps', j :: js, rest, .cons hhead htail => by
    obtain ⟨hplen, t, ht_eq, _, hphead⟩ := hhead.2
    injection ht_eq with ht1
    subst ht1
    have hγ_t1 : gamma compI0 S g (randTerm t1 32) = g.σ t1 32 := by
      unfold gamma; rw [gamma'_randTerm compI0 S g t1 32 (by decide)]
    rw [hγ_t1] at hphead
    obtain ⟨hlen', hget'⟩ := forall₂_kyberCoin_flatten ps' js rest htail
    refine ⟨by simp [List.flatten_cons, hplen, hlen']; omega, ?_⟩
    intro k hk j' hj'
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj'
      subst hj'
      simp only [Nat.mul_zero, List.flatten_cons, List.append_assoc]
      rcases p with _ | ⟨b0, p'⟩
      · cases hplen
      · exact hphead.symm
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hj'
      have hk' : k' < js.length := Nat.lt_of_succ_lt_succ hk
      have hih := hget' k' hk' j' hj'
      simp only [List.flatten_cons, List.append_assoc]
      have hidx : 4 * (k' + 1) = p.length + 4 * k' := by omega
      rw [hidx, List.getElem?_append_right (by omega)]
      simpa [Nat.add_sub_cancel_left] using hih

def ev0CoinsLit : HwBytes :=
  [0x88#8, 0xef#8, 0x4f#8, 0xeb#8, 0x90#8, 0xec#8, 0x69#8, 0xba#8, 0x4b#8, 0x03#8, 0x60#8, 0x2e#8, 0x85#8, 0x98#8, 0xde#8, 0x9c#8,
   0x67#8, 0x58#8, 0x68#8, 0x85#8, 0xaa#8, 0x24#8, 0xc6#8, 0x6e#8, 0x7f#8, 0xab#8, 0xfd#8, 0x4b#8, 0x50#8, 0xfe#8, 0x9f#8, 0xd4#8,
   0xff#8, 0x91#8, 0xd5#8, 0x72#8, 0x1b#8, 0xf8#8, 0x6f#8, 0x00#8, 0xfe#8, 0xcb#8, 0xae#8, 0x95#8, 0x09#8, 0x7d#8, 0xe4#8, 0x18#8,
   0x88#8, 0x2e#8, 0x16#8, 0x5d#8, 0xdd#8, 0xb4#8, 0x3f#8, 0x52#8, 0x3a#8, 0xb6#8, 0xa0#8, 0x64#8, 0xd0#8, 0x53#8, 0x2a#8, 0xe2#8,
   0x96#8, 0xac#8, 0x2d#8, 0xb9#8, 0xbf#8, 0xb5#8, 0x80#8, 0xa6#8, 0xd2#8, 0x7d#8, 0xfe#8, 0x18#8, 0x34#8, 0xfd#8, 0x21#8, 0x2e#8,
   0x60#8, 0xf6#8, 0xc9#8, 0x46#8, 0xb1#8, 0x51#8, 0x00#8, 0xbf#8, 0xd1#8, 0xf8#8, 0xed#8, 0xb4#8, 0xba#8, 0x40#8, 0xbf#8, 0x1e#8,
   0xd2#8, 0x30#8, 0x26#8, 0x69#8, 0x8c#8, 0x9c#8, 0x94#8, 0xe5#8, 0x0d#8, 0x3c#8, 0x44#8, 0xd7#8, 0xdd#8, 0x6d#8, 0xe1#8, 0xb1#8,
   0x6b#8, 0x8e#8, 0xf8#8, 0x7a#8, 0xb0#8, 0x0d#8, 0x18#8, 0x59#8, 0x68#8, 0xc0#8, 0xea#8, 0x13#8, 0x67#8, 0x95#8, 0x92#8, 0x54#8,
   0x2d#8, 0xc0#8, 0x69#8, 0x15#8, 0x5c#8, 0x69#8, 0xf9#8, 0x09#8, 0xd7#8, 0x89#8, 0x0a#8, 0xcd#8, 0x21#8, 0x48#8, 0xbd#8, 0x09#8,
   0xc8#8, 0x1f#8, 0x2e#8, 0xf6#8, 0x64#8, 0x1f#8, 0xeb#8, 0x39#8, 0x7c#8, 0x9d#8, 0x90#8, 0x22#8, 0xa1#8, 0xbb#8, 0x8e#8, 0xf7#8,
   0x25#8, 0x29#8, 0x06#8, 0x87#8, 0x7b#8, 0xd8#8, 0x90#8, 0x2b#8, 0x3e#8, 0x10#8, 0x9e#8, 0xf6#8, 0xa9#8, 0x06#8, 0x76#8, 0x99#8,
   0x94#8, 0xa8#8, 0x21#8, 0xad#8, 0xac#8, 0xd8#8, 0x27#8, 0xf6#8, 0xf2#8, 0x47#8, 0xec#8, 0xc4#8, 0x36#8, 0x15#8, 0x46#8, 0x12#8]

def ev0CoinsHexStr : String :=
  "88ef4feb90ec69ba4b03602e8598de9c67586885aa24c66e7fabfd4b50fe9fd4ff91d5721bf86f00fecbae95097de418882e165dddb43f523ab6a064d0532ae296ac2db9bfb580a6d27dfe1834fd212e60f6c946b15100bfd1f8edb4ba40bf1ed23026698c9c94e50d3c44d7dd6de1b16b8ef87ab00d185968c0ea13679592542dc069155c69f909d7890acd2148bd09c81f2ef6641feb397c9d9022a1bb8ef7252906877bd8902b3e109ef6a906769994a821adacd827f6f247ecc436154612"

theorem ev0_coins_eq_hex : ev0.coins = hexBytes ev0CoinsHexStr := rfl

def ev0CoinsWrap : HwBytes := hexBytes ev0CoinsHexStr
def ev0CoinsChars : List Char := chars_of_hex_def ev0CoinsWrap
theorem ev0CoinsHexStr_eq : ev0CoinsHexStr = String.ofList ev0CoinsChars := rfl
def ev0CoinsFast : HwBytes := hexBytes.go hexDigit ev0CoinsChars

theorem ev0_coins_eq_lit : ev0.coins = ev0CoinsLit := by
  rw [ev0_coins_eq_hex, ev0CoinsHexStr_eq, hexBytes_ofList]
  exact (by decide +kernel : ev0CoinsFast = ev0CoinsLit)

theorem ev0CoinsLit_kyber_byte :
    ∀ j < 32, (ev0CoinsLit.drop 32)[4 * j]? = (dagBytes 69)[j]? := by
  decide +kernel

theorem extract_aliceStart_draws {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {t0 t1 t2 : Nat} {anc : Option Nat}
    (hl0 : (g.σ t0 32).length = 32)
    (hl1 : (g.σ t1 32).length = 32)
    (hl2 : (g.σ t2 32).length = 32)
    (hdrs : DrawsMatch compI0 r S g
      (rngEntry (randTerm t0 32) ::
        (kyberCoinEntries (randTerm t1 32) ++
          [{ rngEntry (randTerm t2 32) with anchor := anc }]))
      ev0.coins) :
    g.σ t0 32 = dagBytes 67 ∧ g.σ t1 32 = dagBytes 69 ∧ g.σ t2 32 = dagBytes 72 := by
  obtain ⟨pieces, _, hpfx, hf2⟩ := hdrs
  obtain ⟨tail, hflat⟩ := hpfx
  rw [ev0_coins_eq_lit] at hflat
  cases hf2 with
  | @cons p0 _ ps_rest _ hm0 hf_rest =>
    have hp0_eq : p0 = g.σ t0 32 := by
      have hb := hm0.2
      simp only [rngEntry, List.map_cons, List.map_nil] at hb
      have hr : gamma compI0 S g (randTerm t0 32) = g.σ t0 32 := by
        unfold gamma; rw [gamma'_randTerm compI0 S g t0 32 (by decide)]
      rw [hr] at hb
      injection hb with h; exact h.symm
    obtain ⟨ps_kc, ps_dhs, rfl, hf_kc, hf_dhs⟩ := forall₂_append_right_loc hf_rest
    cases hf_dhs with
    | @cons p2 _ _ _ hm2 hf_nil =>
      cases hf_nil
      have hp2_eq : p2 = g.σ t2 32 := by
        have hb := hm2.2
        simp only [rngEntry, List.map_cons, List.map_nil] at hb
        have hr : gamma compI0 S g (randTerm t2 32) = g.σ t2 32 := by
          unfold gamma; rw [gamma'_randTerm compI0 S g t2 32 (by decide)]
        rw [hr] at hb
        injection hb with h; exact h.symm
      unfold kyberCoinEntries at hf_kc
      obtain ⟨hkc_len, hkc_get⟩ := forall₂_kyberCoin_flatten ps_kc (List.range 32) (p2 ++ tail) hf_kc
      simp only [List.length_range] at hkc_len hkc_get
      have hkc_len128 : ps_kc.flatten.length = 128 := hkc_len
      simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.nil_append, List.append_assoc] at hflat
      have hp0_len : p0.length = 32 := by rw [hp0_eq, hl0]
      have hp2_len : p2.length = 32 := by rw [hp2_eq, hl2]
      have ht0_res : g.σ t0 32 = dagBytes 67 := by
        have htake := congrArg (List.take 32) hflat
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), hp0_eq] at htake
        exact htake.trans (by decide +kernel)
      have hdrop32 : ps_kc.flatten ++ (p2 ++ tail) = ev0CoinsLit.drop 32 := by
        have hdrop := congrArg (List.drop p0.length) hflat
        rwa [List.drop_left, hp0_len] at hdrop
      have ht1_res : g.σ t1 32 = dagBytes 69 := by
        apply List.ext_getElem (hl1.trans (by decide +kernel : 32 = (dagBytes 69).length))
        intro j hj1 hj2
        have hj32 : j < 32 := by omega
        have hget := hkc_get j hj32 j (List.getElem?_range hj32)
        rw [hdrop32, List.getElem?_eq_getElem hj1] at hget
        have hcoin := (ev0CoinsLit_kyber_byte j hj32).trans (List.getElem?_eq_getElem hj2)
        exact Option.some.inj (hget.trans hcoin)
      have hdrop160 : p2 ++ tail = (ev0CoinsLit.drop 32).drop 128 := by
        have hdrop := congrArg (List.drop ps_kc.flatten.length) hdrop32
        rwa [List.drop_left, hkc_len128] at hdrop
      have ht2_res : g.σ t2 32 = dagBytes 72 := by
        have htake := congrArg (List.take 32) hdrop160
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), hp2_eq] at htake
        exact htake.trans (by decide +kernel)
      exact ⟨ht0_res, ht1_res, ht2_res⟩

theorem extract_enc_coins {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts tsClean cl : Nat} {coins : HwBytes}
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64)
    (hg_len : cl ≠ 0 → (g.σ ts cl).length = cl)
    (hclean : cl ≠ 0 → (gClean g).σ tsClean cl = coins.take cl)
    (hdrs : DrawsMatch compI0 r S g
      (([(randTerm ts cl, cl)].filter fun r => r.2 != 0).map fun r => rngEntry r.1) coins) :
    gamma compI0 S g (randTerm ts cl) = gamma compI0 S (gClean g) (randTerm tsClean cl) := by
  rcases hcl with rfl | hcl_pos
  · unfold gamma gamma' randTerm
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeRandom g) (concretizeAll compI0 S g),
        DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeRandom (gClean g)) (concretizeAll compI0 S (gClean g))]
    rfl
  · have hne0 : cl ≠ 0 := by rcases hcl_pos with rfl | rfl <;> decide
    have hbne : (cl != 0) = true := bne_iff_ne.mpr hne0
    simp only [List.filter_cons, List.filter_nil, hbne, ↓reduceIte, List.map_cons, List.map_nil] at hdrs
    obtain ⟨pieces, _, ⟨tail, hflat⟩, hf2⟩ := hdrs
    cases hf2 with
    | @cons p _ _ _ hm hf_nil =>
      cases hf_nil
      have hp_eq : p = g.σ ts cl := by
        have hb := hm.2
        simp only [rngEntry, List.map_cons, List.map_nil] at hb
        have hr : gamma compI0 S g (randTerm ts cl) = g.σ ts cl := by
          unfold gamma; rw [gamma'_randTerm compI0 S g ts cl hne0]
        rw [hr] at hb
        injection hb with h; exact h.symm
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hflat
      have hlen_p : p.length = cl := by rw [hp_eq, hg_len hne0]
      have htake := congrArg (List.take cl) hflat
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), hp_eq] at htake
      unfold gamma
      rw [gamma'_randTerm compI0 S g ts cl hne0, gamma'_randTerm compI0 S (gClean g) tsClean cl hne0]
      dsimp only
      rw [htake, hclean hne0]

theorem pqEv_tr0_of_localAliceStartTr {tr₀ tr₁ : ExecTrace} {pre0 : List Step}
    (hinv0 : ∀ x ∈ pre0, x.cls = .invisible) (htr₁ : tr₁ = runSteps pre0 tr₀)
    (me peer : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    {k : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hev : (localAliceStartTr tr₁ me peer o).EventLoggedAt ev k)
    (hne : ∀ a b ikA ikB spk pqpk opk ek ct keys,
      ev ≠ .AliceDone a b ikA ikB spk pqpk opk ek ct keys) :
    (tr₀.at? k : Option CompTrace.PQXDHEntry) = some (CompTrace.PQEvE ev) := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  dsimp only [localAliceStartTr] at hev
  have hev := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl hev))
  rcases pqEv_append_same_loc hev with hev | ⟨_, hEq⟩
  · have hev := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl
      (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl hev))))
    rwa [htr₁, at?_runSteps_invisible (fun _ => rfl) tr₀ hinv0 k] at hev
  · exact False.elim (hne _ _ _ _ _ _ _ _ _ _ hEq)

theorem step_of_fitsCmd_init {s : Step} {u} {b : String}
    (hf : s.FitsCmd (.init u b)) :
    ∃ me peer idS regB hb, s = .aliceStart me peer idS regB hb := by
  cases s <;> cases hf
  exact ⟨_, _, _, _, _, rfl⟩

theorem step_of_fitsCmd_send {s : Step} {u}
    (hf : s.FitsCmd (.send u)) :
    (∃ me stIdx cl pqIdx, s = .messageEncrypt me stIdx cl pqIdx) ∨
    (∃ me stIdx, s = .messageEncryptAbort me stIdx) := by
  cases s <;> cases hf
  · exact Or.inl ⟨_, _, _, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

theorem ev1_exit_eq : ev1.exit = some (0, ev4.input) :=
  ev1_exit_eq_fast.trans (congrArg (fun b => some (0, b)) ev4_input_eq_fast.symm)

theorem ev2_exit_eq : ev2.exit = some (0, ev3.input) :=
  ev2_exit_eq_fast.trans (congrArg (fun b => some (0, b)) ev3_input_eq_fast.symm)

end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
