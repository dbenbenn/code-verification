/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2AliceClean

/-!
# Clean Bob Responder & Out-of-Order Decrypt Steps (`tr4Clean`, `tr5Clean`)
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

def tr4Clean (cl1 cl2 : Nat) : ExecTrace :=
  let o := Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys
  let sInfo := (stB3Clean cl1 cl2).sessionInfo "bob"
  ((((((((((tr3Clean cl1 cl2).append (CompTrace.RndE 32)).append
    (CompTrace.NetE spqrKeyB3Clean)).append
    (CompTrace.PQEvE (.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (CompTrace.TREvE (.DHRatchet "bob" "alice" (DY.DiffieHellman.dhPk stA0Clean.dhs) (DY.DiffieHellman.dhPk dhsBClean)))).append
    (CompTrace.TREvE (.HonestDH sInfo dhsBClean 0))).append
    (CompTrace.CEvE (.HandshakeSession sInfo 47))).append
    (CompTrace.TREvE (.SkippedKeyStored sInfo (DY.DiffieHellman.dhPk stA0Clean.dhs) 0
      (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 2 54))).append
    (CompTrace.TREvE (.Received "bob" "alice" (DY.DiffieHellman.dhPk stA0Clean.dhs) 1 (randTerm 38 32)))).append
    (CompTrace.TREvE (.MessageKey sInfo .receiver
      (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 (salt2Clean cl1 cl2) 1 2 54))).append
    (CompTrace.TRStE "bob" (stB3Clean cl1 cl2))

theorem tr4Clean_len (cl1 cl2 : Nat) : (tr4Clean cl1 cl2).length = 55 := by
  have h := tr3Clean_len cl1 cl2
  simp only [tr4Clean, length_append_entry]
  omega

def tr5Clean (cl1 cl2 : Nat) : ExecTrace :=
  let sInfo := (stB3Clean cl1 cl2).sessionInfo "bob"
  (((((tr4Clean cl1 cl2).append (CompTrace.NetE (spqrKeyB4Clean cl1 cl2))).append
    (CompTrace.TREvE (.SkippedKeyUsed sInfo 51))).append
    (CompTrace.TREvE (.Received "bob" "alice" (DY.DiffieHellman.dhPk stA0Clean.dhs) 0 (randTerm 31 32)))).append
    (CompTrace.TREvE (.MessageKey sInfo .receiver
      (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 (salt1Clean cl1) 0 2 54))).append
    (CompTrace.TRStE "bob" (stB4Clean cl1 cl2))

theorem tr5Clean_len (cl1 cl2 : Nat) : (tr5Clean cl1 cl2).length = 60 := by
  have h := tr4Clean_len cl1 cl2
  simp only [tr5Clean, length_append_entry]
  omega

theorem normalizeX25519Key_dhPk (sk : DY.Bytes) :
    DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := by
  have hv_var : (DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  unfold DY.X25519.normalizeX25519Key
  rw [hv_var]

theorem x25519LowOrder_dhPk_false (sk : DY.Bytes) :
    DY.X25519.x25519LowOrder (DY.DiffieHellman.dhPk sk) = false := by
  have hv_lit : (DY.DiffieHellman.dhPk sk).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  unfold DY.X25519.x25519LowOrder
  rw [normalizeX25519Key_dhPk]
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [hv_lit]

theorem isCanonicalKey_dhPk_true (sk : DY.Bytes) :
    DY.Libsignal.PQXDH.isCanonicalKey (DY.DiffieHellman.dhPk sk) = true := by
  have hv_var : (DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  unfold DY.Libsignal.PQXDH.isCanonicalKey
  rw [hv_var]
  simp [x25519LowOrder_dhPk_false]

theorem spqrEmptyMsg_sendMsg_false (st coins : DY.Bytes) :
    DY.Spqr.spqrEmptyMsg (DY.Spqr.spqrSend st coins).2.2 = false := by
  have hv : ((DY.Spqr.spqrSend st coins).2.2).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ st := st, coins := coins } : DY.Spqr.SendMsg.SubF DY.Bytes)
  unfold DY.Spqr.spqrEmptyMsg
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [hv]

theorem s3Clean_runs (cl1 cl2 : Nat) :
    s3Clean.ok (tr3Clean cl1 cl2) = true ∧ s3Clean.next (tr3Clean cl1 cl2) = tr4Clean cl1 cl2 := by
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr; simp [hl1]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr; simp [hl2]
  have lift03 : ∀ {E : Type} [DY.ExecTraceTypes.Has E] {i : Nat} {e : E},
      ((setupTrace r0).at? i : Option E) = some e →
      ((tr3Clean cl1 cl2).at? i : Option E) = some e := by
    intro E _ i e h
    unfold tr3Clean tr2Clean tr1Clean localEncTr localAliceStartTr
    exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
            (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
              (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
                (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
                  (at?_append_of_some_loc (at?_append_of_some_loc h))))))))))))))))))))))
  have hat1 : (tr3Clean cl1 cl2).at? 1 =
      some (Runs.EvP (.IdentityRegistered "alice" ikAPkClean (DY.Signature.vk ikASkClean) true)) := by
    refine lift03 ?_
    rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 registerIdentityTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl1, length_append_entry]; omega)])
    unfold setupTr1 registerIdentityTr; dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, length_append_entry]; omega)])
    exact at?_append_eq_of_eq _ _ (by simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, length_append_entry])
  have hat9 : (tr3Clean cl1 cl2).at? 9 =
      some (Runs.StP "bob" { kind := .identity, sk := ikBSkClean }) := by
    refine lift03 ?_
    rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl2, length_append_entry]; omega)])
    unfold setupTr2 registerIdentityTr; dsimp only; rw [hl1]
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; omega)
  have hat13 : (tr3Clean cl1 cl2).at? 13 =
      some (Runs.StP "bob" { kind := .signedPrekey, sk := spkBSkClean }) := by
    refine lift03 ?_
    rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)])
    unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; omega)
  have hat19 : (tr3Clean cl1 cl2).at? 19 =
      some (Runs.StP "bob" { kind := .pqPrekey, sk := pqskBClean }) := by
    refine lift03 ?_
    rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; omega)
  have hat25 : (tr3Clean cl1 cl2).at? 25 = some (Runs.NetE oClean.ek) := by
    unfold tr3Clean tr2Clean localEncTr
    refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
            (at?_append_of_some_loc (at?_append_of_some_loc ?_)))))))))))))
    unfold tr1Clean localAliceStartTr
    refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc ?_))))
    exact at?_append_eq_of_eq _ _ (by have h := setupTrace_r0_len; simp only [length_append_entry]; omega)
  have hat26 : (tr3Clean cl1 cl2).at? 26 = some (Runs.NetE oClean.ct) := by
    unfold tr3Clean tr2Clean localEncTr
    refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
            (at?_append_of_some_loc (at?_append_of_some_loc ?_)))))))))))))
    unfold tr1Clean localAliceStartTr
    refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc ?_)))
    exact at?_append_eq_of_eq _ _ (by have h := setupTrace_r0_len; simp only [length_append_entry]; omega)
  have hat44 : (tr3Clean cl1 cl2).at? 44 = some (Runs.NetE (m2Clean cl1 cl2)) := by
    have h44 : 44 = (tr2Clean cl1).length + 6 := by rw [tr2Clean_len]
    rw [h44]; unfold tr3Clean m2Clean coins2Clean
    have h39 : 39 = (tr2Clean cl1).length + 1 := by rw [tr2Clean_len]
    have h38 : 38 = (tr2Clean cl1).length := (tr2Clean_len cl1).symm
    rw [h39, h38]; unfold localEncTr
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry])
  have hat40 : (((tr3Clean cl1 cl2).append (Runs.RndE 32)).append (Runs.NetE spqrKeyB3Clean)).at? 40 =
      some (Runs.NetE (salt2Clean cl1 cl2)) := by
    refine at?_append_of_some_loc (at?_append_of_some_loc ?_)
    have h40 : 40 = (tr2Clean cl1).length + 2 := by rw [tr2Clean_len]
    rw [h40]; unfold tr3Clean salt2Clean coins2Clean
    have h39 : 39 = (tr2Clean cl1).length + 1 := by rw [tr2Clean_len]
    rw [h39]; at?_localEncTr_tac
  have hcan : DY.Libsignal.PQXDH.isCanonicalKey oClean.ek = true :=
    isCanonicalKey_dhPk_true (randTerm ((setupTrace r0).length + 0) 32)
  have hagree : DY.Libsignal.PQXDH.bobAgreement ikBSkClean spkBSkClean pqskBClean none ikAPkClean
      oClean.ek oClean.ct = some oClean.keys :=
    Runs.bobAgreement_honest ikASkClean (randTerm ((setupTrace r0).length + 0) 32)
      ikBSkClean spkBSkClean pqskBClean (randTerm ((setupTrace r0).length + 1) 32)
  have hlow : DY.X25519.x25519LowOrder (msg2Clean cl1 cl2).ratchetKey = false :=
    x25519LowOrder_dhPk_false stA0Clean.dhs
  set c0 : DY.Libsignal.TripleRatchet.RecvChain :=
    { ratchetKey := DY.DiffieHellman.dhPk stA0Clean.dhs,
      chainKey := stA0Clean.cks,
      index := 0,
      rIdx := 2 }
  set st' : DY.Libsignal.TripleRatchet.TRState :=
    { stB3Clean cl1 cl2 with recv := [c0], spqr := spqrB0Clean }
  have hrs : Runs.ratchetState
      (Runs.bobSt0 "alice" ikBSkClean spkBSkClean ikAPkClean oClean.keys (msg2Clean cl1 cl2))
      (msg2Clean cl1 cl2).ratchetKey (Runs.rnd (tr3Clean cl1 cl2).length 32) = (st', c0) := by
    rw [tr3Clean_len]
    unfold Runs.ratchetState Runs.bobSt0
    dsimp only
    have hrk : (msg2Clean cl1 cl2).ratchetKey = DY.DiffieHellman.dhPk stA0Clean.dhs := rfl
    rw [hrk, normalizeX25519Key_dhPk, Runs.createChain_comm oClean.keys.rk stA0Clean.dhs spkBSkClean]
    rfl
  have hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c0 (msg2Clean cl1 cl2).counter =
      some ((DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2, recvChainB3Clean cl1 cl2) := rfl
  have hrecv : DY.Spqr.spqrRecv st'.spqr (msg2Clean cl1 cl2).pqRatchet 1 =
      some (spqrB3Clean cl1 cl2, spqrKeyB3Clean) := by
    change DY.Spqr.spqrRecv spqrB0Clean (pqm2Clean cl1 cl2) 1 = _
    unfold DY.Spqr.spqrRecv spqrB0Clean DY.Spqr.spqrInit pqm2Clean
    rw [spqrEmptyMsg_sendMsg_false]
    simp only [Bool.false_eq_true, ↓reduceIte, _root_.DY.BytesView.view_pack]
    have hdir : DY.Spqr.spqrParamsDir? DY.Libsignal.TripleRatchet.spqrB2A = some .b2a := by
      simp [DY.Spqr.spqrParamsDir?, DY.Libsignal.TripleRatchet.spqrB2A,
        DY.Spqr.encodeSpqrDirectionParams, DY.Literal.bytesToLiteral,
        DY.Literal.CanMkLiteral.bytesToLiteral, DY.Literal.literalToBytes,
        DY.Literal.CanMkLiteral.literalToBytes, _root_.DY.BytesView.view_pack,
        DY.Spqr.Direction.toByte]
    rw [hdir]
    rfl
  have hout : Eq (α := DY.Libsignal.TripleRatchet.TRState)
      { st' with recv := DY.Libsignal.TripleRatchet.setRecvChain st'.recv (recvChainB3Clean cl1 cl2), spqr := spqrB3Clean cl1 cl2 }
      (stB3Clean cl1 cl2) := by
    simp [st', c0, stB3Clean, recvChainB3Clean, DY.Libsignal.TripleRatchet.setRecvChain]
  have hrun := Runs.Runs.bobStart (kh := ⟨9, 13, 19, none⟩) (mh := ⟨25, 26, 44⟩)
    hat9 hat13 hat19 rfl hat1 hat25 hat26 hcan hagree hat44
    (parse_m2Clean cl1 cl2) rfl hlow hrs hcons hrecv hat40
    (Runs.mac_ok rfl rfl rfl) (Runs.dec_ok rfl) hout
  have hok_eq := stepIn_ok DY.Libsignal.Composed.bobStart.reachability
    ("bob", "alice", (⟨9, 13, 19, none⟩ : DY.Libsignal.PQXDH.BobKeyHandles), 1,
      (⟨25, 26, 44⟩ : DY.Libsignal.PQXDH.PreKeyMsgHandles), 40, (1 : UInt32))
    (tr3Clean cl1 cl2)
  have hnext_eq := stepIn_next DY.Libsignal.Composed.bobStart.reachability
    ("bob", "alice", (⟨9, 13, 19, none⟩ : DY.Libsignal.PQXDH.BobKeyHandles), 1,
      (⟨25, 26, 44⟩ : DY.Libsignal.PQXDH.PreKeyMsgHandles), 40, (1 : UInt32))
    (tr3Clean cl1 cl2)
  have h1 : ((DY.Libsignal.Composed.bobStart "bob" "alice" ⟨9, 13, 19, none⟩ 1 ⟨25, 26, 44⟩ 40 1).run
      (tr3Clean cl1 cl2)).1.isSome = true := by
    rw [hrun.1]; rfl
  refine ⟨hok_eq.trans h1, hnext_eq.trans (hrun.2.trans ?_)⟩
  dsimp only [Runs.skipTr]
  have hsinfo : st'.sessionInfo "bob" = (stB3Clean cl1 cl2).sessionInfo "bob" := rfl
  have hc_cnt : (msg2Clean cl1 cl2).counter.toNat - c0.index.toNat = 1 := rfl
  set tr51 : ExecTrace :=
    ((((((tr3Clean cl1 cl2).append (Runs.RndE 32)).append (Runs.NetE spqrKeyB3Clean)).append
      (Runs.EvP (.BobDone "bob" "alice"
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).ikB
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).ikA
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).spk
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).pqpk
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).opk
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).ek
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).ct
        (Runs.bobOut ikBSkClean spkBSkClean pqskBClean ikAPkClean oClean.ek oClean.ct oClean.keys).keys))).append
      (Runs.EvT (.DHRatchet "bob" st'.peer (msg2Clean cl1 cl2).ratchetKey (DY.DiffieHellman.dhPk st'.dhs)))).append
      (Runs.EvT (.HonestDH (st'.sessionInfo "bob") st'.dhs (st'.rIdx - 2)))).append
      (Runs.EvC (.HandshakeSession (st'.sessionInfo "bob")
        (((tr3Clean cl1 cl2).append (Runs.RndE 32)).append (Runs.NetE spqrKeyB3Clean)).length))
  rw [hc_cnt]
  have hlog : ((DY.Libsignal.TripleRatchet.logSkippedKeys (st'.sessionInfo "bob")
      (msg2Clean cl1 cl2).ratchetKey c0.rIdx (tr51.length + 1 + 2) c0.chainKey c0.index 1).run tr51).2 =
      tr51.append (Runs.EvT (.SkippedKeyStored (st'.sessionInfo "bob")
        (msg2Clean cl1 cl2).ratchetKey c0.index (DY.Libsignal.TripleRatchet.kdfCk c0.chainKey).2
        c0.rIdx (tr51.length + 1 + 2))) := by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact (Runs.Runs.bind (Runs.Runs.logEvent _ _)
      (by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Runs.Runs.pure _ _)).2
  rw [hlog]
  dsimp only [tr51]
  simp only [length_append_entry, tr3Clean_len, hsinfo]
  rfl

theorem anyEventOnTrace_append_false {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) (pred : DY.Libsignal.TripleRatchet.TREvent → Bool)
    (htr : DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent tr pred = false)
    (he : match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option CompTrace.TREntry) with
      | some entry => pred entry.ev = false
      | none => True) :
    DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent (tr.append e) pred = false := by
  unfold DY.Libsignal.TripleRatchet.anyEventOnTrace at htr ⊢
  rw [List.any_eq_false] at htr ⊢
  intro i hi
  have hlen : (tr.append e : ExecTrace).length = tr.length + 1 := length_append_entry tr e
  have hlt : i < tr.length + 1 := by rw [← hlen]; exact List.mem_range.mp hi
  by_cases hi_lt : i < tr.length
  · have := htr i (List.mem_range.mpr hi_lt)
    rwa [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hi_lt,
      ← Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  · have hi_eq : i = tr.length := by omega
    subst hi_eq
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TREntry) with
    | none => simp
    | some entry =>
      rw [hproj] at he
      dsimp only at he ⊢
      rw [he]
      decide

theorem skippedKeyUsedB_tr4Clean_false (cl1 cl2 : Nat) :
    DY.Libsignal.TripleRatchet.skippedKeyUsedB (tr4Clean cl1 cl2) 51 = false := by
  unfold DY.Libsignal.TripleRatchet.skippedKeyUsedB tr4Clean tr3Clean tr2Clean tr1Clean
    localEncTr localAliceStartTr
  dsimp only
  rw [setupTrace_r0_eq]
  unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
  dsimp only
  repeat refine anyEventOnTrace_append_false _ _ _ ?_ (by first | trivial | rfl)
  unfold DY.Libsignal.TripleRatchet.anyEventOnTrace
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

theorem hat37_tr4Clean (cl1 cl2 : Nat) :
    ((tr4Clean cl1 cl2).at? 37 : Option DY.Network.ExecEntryT) = some (Runs.NetE (m1Clean cl1)) := by
  have hat37_2 : ((tr2Clean cl1).at? 37 : Option DY.Network.ExecEntryT) =
      some (Runs.NetE (m1Clean cl1)) := by
    have h37 : 37 = tr1Clean.length + 6 := by rw [tr1Clean_len]
    have hm1 : m1Clean cl1 = localEncMsg stA0Clean (randTerm (tr1Clean.length + 1) cl1)
        (salt1Clean cl1) (randTerm tr1Clean.length 32) := by
      unfold m1Clean coins1Clean
      rw [tr1Clean_len]
    rw [h37, hm1]
    unfold tr2Clean localEncTr
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry])
  unfold tr4Clean tr3Clean localEncTr; dsimp only
  exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
    (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
            (at?_append_of_some_loc (at?_append_of_some_loc hat37_2))))))))))))))))

theorem s4Clean_runs (cl1 cl2 : Nat) :
    s4Clean.ok (tr4Clean cl1 cl2) = true ∧ s4Clean.next (tr4Clean cl1 cl2) = tr5Clean cl1 cl2 := by
  have hat54 : (tr4Clean cl1 cl2).at? 54 = some (Runs.StT "bob" (stB3Clean cl1 cl2)) := by
    unfold tr4Clean; dsimp only
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])
  have hat37 := hat37_tr4Clean cl1 cl2
  have hat51 : (tr4Clean cl1 cl2).at? 51 =
      some (Runs.EvT (.SkippedKeyStored ((stB3Clean cl1 cl2).sessionInfo "bob")
        (DY.DiffieHellman.dhPk stA0Clean.dhs) 0
        (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 2 54)) := by
    unfold tr4Clean; dsimp only
    refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc ?_))
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])
  have hat33 : ((tr4Clean cl1 cl2).append (Runs.NetE (spqrKeyB4Clean cl1 cl2))).at? 33 =
      some (Runs.NetE (salt1Clean cl1)) := by
    have hat33_2 : ((tr2Clean cl1).at? 33 : Option DY.Network.ExecEntryT) =
        some (Runs.NetE (salt1Clean cl1)) := by
      have h33 : 33 = tr1Clean.length + 2 := by rw [tr1Clean_len]
      rw [h33]; unfold tr2Clean salt1Clean coins1Clean
      have h32 : 32 = tr1Clean.length + 1 := by rw [tr1Clean_len]
      rw [h32]; at?_localEncTr_tac
    refine at?_append_of_some_loc ?_
    unfold tr4Clean tr3Clean localEncTr; dsimp only
    exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
      (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
            (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
              (at?_append_of_some_loc (at?_append_of_some_loc hat33_2))))))))))))))))
  have heq : (stB3Clean cl1 cl2).sessionInfo "bob" = (stB3Clean cl1 cl2).sessionInfo "bob" ∧
      DY.DiffieHellman.dhPk stA0Clean.dhs = (msg1Clean cl1).ratchetKey ∧
      (0 : UInt32) = (msg1Clean cl1).counter ∧
      (DY.Libsignal.TripleRatchet.findRecvChain (stB3Clean cl1 cl2).recv
        (DY.DiffieHellman.dhPk stA0Clean.dhs)).isSome = true :=
    ⟨rfl, rfl, rfl, by simp [stB3Clean, recvChainB3Clean, DY.Libsignal.TripleRatchet.findRecvChain]⟩
  have hunused : (!DY.Libsignal.TripleRatchet.skippedKeyUsedB (tr4Clean cl1 cl2) 51) = true := by
    rw [skippedKeyUsedB_tr4Clean_false]; rfl
  have hrecv : DY.Spqr.spqrRecv (stB3Clean cl1 cl2).spqr (msg1Clean cl1).pqRatchet 1 =
      some (spqrB4Clean cl1 cl2, spqrKeyB4Clean cl1 cl2) := by
    change DY.Spqr.spqrRecv (spqrB3Clean cl1 cl2) (pqm1Clean cl1) 1 = _
    have hni : (spqrB3Clean cl1 cl2).view? DY.Spqr.InitState.SubF = none :=
      Runs.notInit_recv spqrB0Clean (pqm2Clean cl1 cl2)
    unfold DY.Spqr.spqrRecv pqm1Clean
    rw [spqrEmptyMsg_sendMsg_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hni]
    rfl
  have hrun := Runs.Runs.messageDecryptSkipped hat54 hat37 (parse_m1Clean cl1) rfl hat51
    heq hunused hrecv hat33 (Runs.mac_ok rfl rfl rfl) (Runs.dec_ok rfl)
    (stOut := stB4Clean cl1 cl2) rfl
  have hok_eq := stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    ("bob", 54, 37, 51, 33, (1 : UInt32)) (tr4Clean cl1 cl2)
  have hnext_eq := stepIn_next DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    ("bob", 54, 37, 51, 33, (1 : UInt32)) (tr4Clean cl1 cl2)
  have h1 : ((DY.Libsignal.TripleRatchet.messageDecryptSkipped "bob" 54 37 51 33 1).run
      (tr4Clean cl1 cl2)).1.isSome = true := by
    rw [hrun.1]; rfl
  exact ⟨hok_eq.trans h1, hnext_eq.trans hrun.2⟩

theorem runTrace_ss4Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    runTrace r (ss4Clean cl1 cl2) = tr4Clean cl1 cl2 := by
  unfold runTrace ss4Clean
  rw [setupTrace_eq_of_fits hp]
  dsimp only [runSteps]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2, (s2Clean_runs cl1 cl2).2, (s3Clean_runs cl1 cl2).2]

theorem runTrace_ss5Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    runTrace r (ss5Clean cl1 cl2) = tr5Clean cl1 cl2 := by
  unfold runTrace ss5Clean
  rw [setupTrace_eq_of_fits hp]
  dsimp only [runSteps]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2, (s2Clean_runs cl1 cl2).2,
      (s3Clean_runs cl1 cl2).2, (s4Clean_runs cl1 cl2).2]

theorem honestSaltsOf_ss4Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    honestSaltsOf r (ss4Clean cl1 cl2) = [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2] := by
  have heq : ss4Clean cl1 cl2 = ss3Clean cl1 cl2 ++ [s3Clean] := rfl
  unfold honestSaltsOf at *
  rw [setupTrace_eq_of_fits hp]
  unfold ss4Clean
  rw [honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_1]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2, (s2Clean_runs cl1 cl2).2]
  have hp0 : s0Clean.publishedSpqrKey? (setupTrace r0) = none := rfl
  have hp3 : s3Clean.publishedSpqrKey? (tr3Clean cl1 cl2) = none := rfl
  have hs3 := honestSaltsOf_ss3Clean hp cl1 cl2
  unfold honestSaltsOf ss3Clean at hs3
  rw [setupTrace_eq_of_fits hp, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2,
      honestKeysOf.eq_1, s0Clean_runs.2, (s1Clean_runs cl1).2] at hs3
  simpa [hp0, hp3] using hs3

theorem honestSaltsOf_ss5Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    honestSaltsOf r (ss5Clean cl1 cl2) = [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2] := by
  unfold honestSaltsOf ss5Clean
  rw [setupTrace_eq_of_fits hp]
  rw [honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2,
      honestKeysOf.eq_2, honestKeysOf.eq_1]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2, (s2Clean_runs cl1 cl2).2, (s3Clean_runs cl1 cl2).2]
  have hp0 : s0Clean.publishedSpqrKey? (setupTrace r0) = none := rfl
  have hp3 : s3Clean.publishedSpqrKey? (tr3Clean cl1 cl2) = none := rfl
  have hp4 : s4Clean.publishedSpqrKey? (tr4Clean cl1 cl2) = none := rfl
  have hs3 := honestSaltsOf_ss3Clean hp cl1 cl2
  unfold honestSaltsOf ss3Clean at hs3
  rw [setupTrace_eq_of_fits hp, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2,
      honestKeysOf.eq_1, s0Clean_runs.2, (s1Clean_runs cl1).2] at hs3
  simpa [hp0, hp3, hp4] using hs3

noncomputable def vis4Clean (cl1 cl2 : Nat) : List VisEntry :=
  vis3Clean cl1 cl2 ++ stepView s3Clean (tr3Clean cl1 cl2) (runWrapped ev3)

noncomputable def vis5Clean (cl1 cl2 : Nat) : List VisEntry :=
  vis4Clean cl1 cl2 ++ stepView s4Clean (tr4Clean cl1 cl2) (runWrapped ev4)

theorem isCurrentSnapshot_tr4Clean (cl1 cl2 : Nat) :
    DY.Libsignal.TripleRatchet.isCurrentSnapshot (tr4Clean cl1 cl2) 54 = true := by
  rw [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  have hst : ((tr4Clean cl1 cl2).at? 54 : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE "bob" (stB3Clean cl1 cl2)) := by
    unfold tr4Clean; dsimp only
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])
  rw [hst, tr4Clean_len]
  rfl

theorem stepsWF_ss4Clean {r : ProtocolSetup} (hp : FitsPins r)
    {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    StepsWF (ss4Clean cl1 cl2) (setupTrace r) := by
  rw [setupTrace_eq_of_fits hp]
  unfold ss4Clean
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles))
    (setupTrace r0) trivial, trivial, ?_⟩
  rw [s0Clean_runs.2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    ("alice", 30, cl1, 33) tr1Clean isCurrentSnapshot_tr1Clean, localOk_s1Clean hcl1, ?_⟩
  rw [(s1Clean_runs cl1).2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    ("alice", 36, cl2, 40) (tr2Clean cl1) (isCurrentSnapshot_tr2Clean cl1), localOk_s2Clean cl1 hcl2, ?_⟩
  rw [(s2Clean_runs cl1 cl2).2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.Composed.bobStart.reachability
    ("bob", "alice", (⟨9, 13, 19, none⟩ : DY.Libsignal.PQXDH.BobKeyHandles), 1,
      (⟨25, 26, 44⟩ : DY.Libsignal.PQXDH.PreKeyMsgHandles), 40, (1 : UInt32))
    (tr3Clean cl1 cl2) trivial, trivial, trivial⟩

theorem stepsWF_ss5Clean {r : ProtocolSetup} (hp : FitsPins r)
    {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    StepsWF (ss5Clean cl1 cl2) (setupTrace r) := by
  rw [setupTrace_eq_of_fits hp]
  unfold ss5Clean
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles))
    (setupTrace r0) trivial, trivial, ?_⟩
  rw [s0Clean_runs.2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    ("alice", 30, cl1, 33) tr1Clean isCurrentSnapshot_tr1Clean, localOk_s1Clean hcl1, ?_⟩
  rw [(s1Clean_runs cl1).2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    ("alice", 36, cl2, 40) (tr2Clean cl1) (isCurrentSnapshot_tr2Clean cl1), localOk_s2Clean cl1 hcl2, ?_⟩
  rw [(s2Clean_runs cl1 cl2).2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.Composed.bobStart.reachability
    ("bob", "alice", (⟨9, 13, 19, none⟩ : DY.Libsignal.PQXDH.BobKeyHandles), 1,
      (⟨25, 26, 44⟩ : DY.Libsignal.PQXDH.PreKeyMsgHandles), 40, (1 : UInt32))
    (tr3Clean cl1 cl2) trivial, trivial, ?_⟩
  rw [(s3Clean_runs cl1 cl2).2]
  refine ⟨Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
    DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    ("bob", 54, 37, 51, 33, (1 : UInt32))
    (tr4Clean cl1 cl2) (isCurrentSnapshot_tr4Clean cl1 cl2), trivial, trivial⟩

theorem stepsStateFaithful_ss4Clean (r : ProtocolSetup) (cl1 cl2 : Nat) :
    StepsStateFaithful r (ss4Clean cl1 cl2) := by
  intro i j si sj p k b hij hsi hsj hl1 _ hl2
  have hj_lt : j < 4 := by
    by_contra hge
    rw [List.getElem?_eq_none (by simp [ss4Clean]; omega)] at hsj
    cases hsj
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi_cases with rfl | rfl | rfl
  · simp [ss4Clean, s0Clean, Step.stateLoad?] at hsi hl1; subst hsi; cases hl1
  · have hj_cases : j = 2 ∨ j = 3 := by omega
    rcases hj_cases with rfl | rfl
    · simp only [ss4Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi hsj
      subst hsi hsj; simp [s1Clean, s2Clean, Step.stateLoad?] at hl1 hl2; omega
    · simp only [ss4Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsj
      subst hsj; simp [s3Clean, Step.stateLoad?] at hl2
  · have hj3 : j = 3 := by omega
    subst hj3
    simp only [ss4Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsj
    subst hsj; simp [s3Clean, Step.stateLoad?] at hl2

theorem stepsStateFaithful_ss5Clean (r : ProtocolSetup) (cl1 cl2 : Nat) :
    StepsStateFaithful r (ss5Clean cl1 cl2) := by
  intro i j si sj p k b hij hsi hsj hl1 _ hl2
  have hj_lt : j < 5 := by
    by_contra hge
    rw [List.getElem?_eq_none (by simp [ss5Clean]; omega)] at hsj
    cases hsj
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl
  · simp [ss5Clean, s0Clean, Step.stateLoad?] at hsi hl1; subst hsi; cases hl1
  · have hj_cases : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj_cases with rfl | rfl | rfl
    · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi hsj
      subst hsi hsj; simp [s1Clean, s2Clean, Step.stateLoad?] at hl1 hl2; omega
    · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsj
      subst hsj; simp [s3Clean, Step.stateLoad?] at hl2
    · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi hsj
      subst hsi hsj; simp [s1Clean, s4Clean, Step.stateLoad?] at hl1 hl2
      exact absurd (hl1.1.trans hl2.1.symm) (by decide)
  · have hj_cases : j = 3 ∨ j = 4 := by omega
    rcases hj_cases with rfl | rfl
    · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsj
      subst hsj; simp [s3Clean, Step.stateLoad?] at hl2
    · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi hsj
      subst hsi hsj; simp [s2Clean, s4Clean, Step.stateLoad?] at hl1 hl2
      exact absurd (hl1.1.trans hl2.1.symm) (by decide)
  · simp only [ss5Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi
    subst hsi; simp [s3Clean, Step.stateLoad?] at hl1

theorem hat37_tr5Clean (cl1 cl2 : Nat) :
    ((tr5Clean cl1 cl2).at? 37 : Option DY.Network.ExecEntryT) = some (Runs.NetE (m1Clean cl1)) := by
  unfold tr5Clean; dsimp only
  exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
    (at?_append_of_some_loc (at?_append_of_some_loc (hat37_tr4Clean cl1 cl2)))))

theorem attackerKnows_c1_tr4Clean (cl1 cl2 : Nat) :
    (m1Clean cl1).AttackerKnows (tr4Clean cl1 cl2) :=
  DY.Trace.MessageSentAt_implies_AttackerKnows _ _ 37
    (by rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact hat37_tr4Clean cl1 cl2)

theorem attackerKnows_c1_tr5Clean (cl1 cl2 : Nat) :
    (m1Clean cl1).AttackerKnows (tr5Clean cl1 cl2) :=
  DY.Trace.MessageSentAt_implies_AttackerKnows _ _ 37
    (by rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact hat37_tr5Clean cl1 cl2)

theorem storedSecrets_tr4Clean_eq (cl1 cl2 : Nat) :
    storedSecrets (tr4Clean cl1 cl2) = storedSecrets (tr3Clean cl1 cl2) := by
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      storedSecrets (tr.append (CompTrace.RndE n)) = storedSecrets tr := by
    intro tr n; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      storedSecrets (tr.append (CompTrace.NetE m)) = storedSecrets tr := by
    intro tr m; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevp : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      storedSecrets (tr.append (CompTrace.PQEvE ev)) = storedSecrets tr := by
    intro tr ev; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevt : ∀ (tr : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent),
      storedSecrets (tr.append (CompTrace.TREvE ev)) = storedSecrets tr := by
    intro tr ev; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevc : ∀ (tr : ExecTrace) (ev : DY.Libsignal.Composed.ComposedEvent),
      storedSecrets (tr.append (CompTrace.CEvE ev)) = storedSecrets tr := by
    intro tr ev; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hstt : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.TripleRatchet.TRState),
      storedSecrets (tr.append (CompTrace.TRStE me s)) = storedSecrets tr := by
    intro tr me s; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  unfold tr4Clean; dsimp only
  simp only [hrnd, hnet, hevp, hevt, hevc, hstt]

theorem storedSecrets_tr5Clean_eq (cl1 cl2 : Nat) :
    storedSecrets (tr5Clean cl1 cl2) = storedSecrets (tr3Clean cl1 cl2) := by
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      storedSecrets (tr.append (CompTrace.NetE m)) = storedSecrets tr := by
    intro tr m; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevt : ∀ (tr : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent),
      storedSecrets (tr.append (CompTrace.TREvE ev)) = storedSecrets tr := by
    intro tr ev; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hstt : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.TripleRatchet.TRState),
      storedSecrets (tr.append (CompTrace.TRStE me s)) = storedSecrets tr := by
    intro tr me s; unfold storedSecrets; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  unfold tr5Clean; dsimp only
  simp only [hnet, hevt, hstt, storedSecrets_tr4Clean_eq]

theorem storedStates_tr4Clean_eq (cl1 cl2 : Nat) :
    storedStates r0 (tr4Clean cl1 cl2) =
      [⟨"alice", stA0Clean⟩, ⟨"alice", stA1Clean cl1⟩, ⟨"alice", stA2Clean cl1 cl2⟩,
       ⟨"bob", stB3Clean cl1 cl2⟩] := by
  have hstep : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
      (h : (setupTrace r0).length ≤ tr.length),
      storedStates r0 (tr.append e) = storedStates r0 tr ++
        match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.TRStEntry) with
        | none => []
        | some entry => [entry.st] :=
    fun tr e h => filterMap_newIndices_trSt_append (setupTrace r0) tr e h
  have htrst : ∀ p st,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TRStE p st) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [⟨p, st⟩] := fun _ _ => rfl
  have hrnd : ∀ n,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.RndE n) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have hnet : ∀ m,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.NetE m) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have hpq : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.PQEvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have htr : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TREvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have hce : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.CEvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have hle3 : (setupTrace r0).length ≤ (tr3Clean cl1 cl2).length := by
    rw [setupTrace_r0_len, tr3Clean_len]; decide
  unfold tr4Clean; dsimp only
  repeat rw [hstep _ _ (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
  rw [storedStates_tr3Clean_eq]
  simp only [htrst, hrnd, hnet, hpq, htr, hce, List.append_nil]
  rfl

theorem storedStates_tr5Clean_eq (cl1 cl2 : Nat) :
    storedStates r0 (tr5Clean cl1 cl2) =
      [⟨"alice", stA0Clean⟩, ⟨"alice", stA1Clean cl1⟩, ⟨"alice", stA2Clean cl1 cl2⟩,
       ⟨"bob", stB3Clean cl1 cl2⟩, ⟨"bob", stB4Clean cl1 cl2⟩] := by
  have hstep : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
      (h : (setupTrace r0).length ≤ tr.length),
      storedStates r0 (tr.append e) = storedStates r0 tr ++
        match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.TRStEntry) with
        | none => []
        | some entry => [entry.st] :=
    fun tr e h => filterMap_newIndices_trSt_append (setupTrace r0) tr e h
  have htrst : ∀ p st,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TRStE p st) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [⟨p, st⟩] := fun _ _ => rfl
  have hnet : ∀ m,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.NetE m) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have htr : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TREvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => [] | some entry => [entry.st]) = [] := fun _ => rfl
  have hle4 : (setupTrace r0).length ≤ (tr4Clean cl1 cl2).length := by
    rw [setupTrace_r0_len, tr4Clean_len]; decide
  unfold tr5Clean; dsimp only
  repeat rw [hstep _ _ (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
  rw [storedStates_tr4Clean_eq]
  simp only [htrst, hnet, htr, List.append_nil]
  rfl

theorem availableStates_tr4Clean_mem (cl1 cl2 : Nat) :
    ∀ st ∈ availableStates r0 (tr4Clean cl1 cl2),
      st = stA0Clean ∨ st = stA1Clean cl1 ∨ st = stA2Clean cl1 cl2 ∨
      st = stB3Clean cl1 cl2 ∨ st = stB4Clean cl1 cl2 := by
  intro st hmem
  unfold availableStates at hmem
  rw [storedStates_tr4Clean_eq] at hmem
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem availableStates_tr5Clean_mem (cl1 cl2 : Nat) :
    ∀ st ∈ availableStates r0 (tr5Clean cl1 cl2),
      st = stA0Clean ∨ st = stA1Clean cl1 ∨ st = stA2Clean cl1 cl2 ∨
      st = stB3Clean cl1 cl2 ∨ st = stB4Clean cl1 cl2 := by
  intro st hmem
  unfold availableStates at hmem
  rw [storedStates_tr5Clean_eq] at hmem
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact hmem

theorem skippedKeyStored_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hother : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TREntry) = none)
    (htr : ∀ i, i < tr.length → ∀ s pk n seed rIdx srcIdx,
      tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2) :
    ∀ i, i < (tr.append e : ExecTrace).length → ∀ s pk n seed rIdx srcIdx,
      (tr.append e).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 := by
  intro i hi s pk n seed rIdx srcIdx hev
  have hlen : (tr.append e : ExecTrace).length = tr.length + 1 := length_append_entry tr e
  by_cases hi_lt : i < tr.length
  · rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hi_lt,
        ← Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
    exact htr i hi_lt s pk n seed rIdx srcIdx hev
  · have hi_eq : i = tr.length := by omega
    subst hi_eq
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        at?_append_other_eq _ _ hother,
        Symbolic.Swarm.CREF.at?_ge_length tr (Nat.le_refl _)] at hev
    cases hev

theorem skippedKeyStored_append_trEv (tr : ExecTrace)
    (ev : DY.Libsignal.TripleRatchet.TREvent)
    (hev_ok : ∀ s pk n seed rIdx srcIdx,
      ev = .SkippedKeyStored s pk n seed rIdx srcIdx →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2)
    (htr : ∀ i, i < tr.length → ∀ s pk n seed rIdx srcIdx,
      tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2) :
    ∀ i, i < (tr.append (CompTrace.TREvE ev) : ExecTrace).length → ∀ s pk n seed rIdx srcIdx,
      (tr.append (CompTrace.TREvE ev)).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 := by
  intro i hi s pk n seed rIdx srcIdx hev
  have hlen : (tr.append (CompTrace.TREvE ev) : ExecTrace).length = tr.length + 1 :=
    length_append_entry tr _
  by_cases hi_lt : i < tr.length
  · rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hi_lt,
        ← Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
    exact htr i hi_lt s pk n seed rIdx srcIdx hev
  · have hi_eq : i = tr.length := by omega
    subst hi_eq
    have hat : ((tr.append (CompTrace.TREvE ev)).at? tr.length : Option CompTrace.TREntry) =
        some (CompTrace.TREvE ev) := at?_append_eq_of_eq _ _ rfl
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat] at hev
    dsimp only [Option.map, CompTrace.TREvE] at hev
    injection hev with hev_eq
    exact hev_ok s pk n seed rIdx srcIdx hev_eq

theorem skippedKeyStored_tr3Clean_only (cl1 cl2 : Nat) :
    ∀ i, i < (tr3Clean cl1 cl2).length → ∀ s pk n seed rIdx srcIdx,
      (tr3Clean cl1 cl2).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 := by
  unfold tr3Clean tr2Clean tr1Clean localEncTr localAliceStartTr
  dsimp only
  rw [setupTrace_r0_eq]
  unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
  dsimp only
  repeat (first
    | refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
    | refine skippedKeyStored_append_other _ _ rfl ?_)
  intro i hi
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hi
  omega

theorem skippedKeyStored_tr4Clean_only (cl1 cl2 : Nat) :
    ∀ i, i < (tr4Clean cl1 cl2).length → ∀ s pk n seed rIdx srcIdx,
      (tr4Clean cl1 cl2).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 := by
  unfold tr4Clean; dsimp only
  refine skippedKeyStored_append_other _ _ rfl ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_trEv _ _
    (fun _ _ _ _ _ _ h => by injection h with _ h1 h2 h3; exact ⟨h1.symm, h2.symm, h3.symm⟩) ?_
  refine skippedKeyStored_append_other _ _ rfl ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_other _ _ rfl ?_
  refine skippedKeyStored_append_other _ _ rfl ?_
  refine skippedKeyStored_append_other _ _ rfl ?_
  exact skippedKeyStored_tr3Clean_only cl1 cl2

theorem skippedKeyStored_tr5Clean_only (cl1 cl2 : Nat) :
    ∀ i, i < (tr5Clean cl1 cl2).length → ∀ s pk n seed rIdx srcIdx,
      (tr5Clean cl1 cl2).getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 := by
  unfold tr5Clean; dsimp only
  refine skippedKeyStored_append_other _ _ rfl ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_trEv _ _ (fun _ _ _ _ _ _ h => nomatch h) ?_
  refine skippedKeyStored_append_other _ _ rfl ?_
  exact skippedKeyStored_tr4Clean_only cl1 cl2

theorem newIndices_append_loc {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  unfold newIndices
  have hsub : (tr.append e : ExecTrace).length - tr0.length = (tr.length - tr0.length) + 1 := by
    rw [length_append_entry]; omega
  rw [hsub, List.range'_concat]
  simp [Nat.add_sub_of_le hle]

theorem newRandoms_append_loc {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr ++
      match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option DY.Random.ExecEntryT) with
      | none => []
      | some entry => [(randTerm tr.length entry.length, entry.length)] := by
  unfold newRandoms
  rw [newIndices_append_loc tr0 tr e hle, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  · refine filterMap_congr_loc fun i hi => ?_
    unfold newIndices at hi
    simp only [List.mem_range'_1] at hi
    have hlt : i < tr.length := by omega
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hlt]
  · simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) <;> rfl

theorem findSome?_congr_loc {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.findSome?_cons, h x (.head _)]
    cases g x with
    | some _ => rfl
    | none => exact findSome?_congr_loc (fun y hy => h y (.tail _ hy))

theorem find?_congr_loc {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.find? f = l.find? g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x (.head _)]
    cases g x with
    | true => rfl
    | false => exact find?_congr_loc (fun y hy => h y (.tail _ hy))

theorem receivedPlaintext_append_loc {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length) :
    receivedPlaintext tr0 (tr.append e) =
      (receivedPlaintext tr0 tr).or
        (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.TREntry) with
         | some entry =>
           match entry.ev with
           | .Received _ _ _ _ m => some m
           | _ => none
         | none => none) := by
  unfold receivedPlaintext
  rw [newIndices_append_loc tr0 tr e hle, List.findSome?_append, List.findSome?_cons, List.findSome?_nil]
  refine congrArg₂ Option.or (findSome?_congr_loc fun i hi => ?_) ?_
  · have hlt : i < tr.length := by unfold newIndices at hi; simp only [List.mem_range'_1] at hi; omega
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hlt,
        ← Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  · rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TREntry) with
    | none => rfl
    | some entry => dsimp only [Option.map]; cases entry.ev <;> rfl

theorem eventIdx_isBobDone_append_loc {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length) :
    eventIdx isBobDone tr0 (tr.append e) =
      (eventIdx isBobDone tr0 tr).or
        (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.PQXDHEntry) with
         | some entry => if isBobDone entry.ev then some tr.length else none
         | none => none) := by
  unfold eventIdx
  rw [newIndices_append_loc tr0 tr e hle, List.find?_append, List.find?_cons, List.find?_nil]
  refine congrArg₂ Option.or (find?_congr_loc fun i hi => ?_) ?_
  · have hlt : i < tr.length := by unfold newIndices at hi; simp only [List.mem_range'_1] at hi; omega
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
        Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hlt,
        ← Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  · rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases hproj : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.PQXDHEntry) with
    | none => rfl
    | some entry => dsimp only [Option.map, Option.getD]; cases isBobDone entry.ev <;> rfl

theorem proj_inj_netE (m : DY.Bytes) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.NetE m) : ExecTrace.Entry) :
      Option DY.Network.ExecEntryT) = some ⟨m⟩ := rfl

theorem proj_inj_pqEvE (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.PQEvE ev) : ExecTrace.Entry) :
      Option CompTrace.PQXDHEntry) = some ⟨ev⟩ := rfl

theorem proj_inj_cEvE (ev : DY.Libsignal.Composed.ComposedEvent) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.CEvE ev) : ExecTrace.Entry) :
      Option CompTrace.CEntry) = some ⟨ev⟩ := rfl

theorem proj_inj_trStE (p : DY.Participant) (st : DY.Libsignal.TripleRatchet.TRState) :
    (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TRStE p st) : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) = some (CompTrace.TRStE p st) := rfl

theorem getLocalStateAt_trStE {tr : ExecTrace} {i : Nat}
    {p : DY.Participant} {st : DY.Libsignal.TripleRatchet.TRState}
    (h : (tr.at? i : Option CompTrace.TRStEntry) = some (CompTrace.TRStE p st)) :
    ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState tr i = some ⟨p, st⟩ := by
  unfold ExecTrace.getLocalStateAt; rw [h]; rfl

theorem bobOut_eq (ikB spk pqsk ikAPk ek ct : DY.Bytes)
    (keys : DY.Libsignal.PQXDH.HandshakeKeys) :
    Runs.bobOut ikB spk pqsk ikAPk ek ct keys =
      { ikB := DY.DiffieHellman.dhPk ikB,
        ikA := ikAPk,
        spk := DY.DiffieHellman.dhPk spk,
        spkSk := spk,
        pqpk := DY.PQKem.kemPk pqsk,
        opk := none,
        ek := ek,
        ct := ct,
        keys := keys } := rfl

theorem eventIdx_isBobDone_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length)
    (hr : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.PQXDHEntry) = none) :
    eventIdx isBobDone tr0 (tr.append e) = eventIdx isBobDone tr0 tr := by
  rw [eventIdx_isBobDone_append_loc tr0 tr e hle, hr, Option.or_none]

theorem eventIdx_isBobDone_append_bobDone (tr0 tr : ExecTrace)
    (b a : DY.Participant) (ikB ikA spk pqpk : DY.Bytes) (opk : Option DY.Bytes)
    (ek ct : DY.Bytes) (keys : DY.Libsignal.PQXDH.HandshakeKeys)
    (hle : tr0.length ≤ tr.length) :
    eventIdx isBobDone tr0 (tr.append (CompTrace.PQEvE (.BobDone b a ikB ikA spk pqpk opk ek ct keys))) =
      (eventIdx isBobDone tr0 tr).or (some tr.length) := by
  rw [eventIdx_isBobDone_append_loc tr0 tr _ hle, proj_inj_pqEvE]
  rfl

theorem exposures_tr3_tr4_eq (cl1 cl2 : Nat) :
    exposures (tr3Clean cl1 cl2) (tr4Clean cl1 cl2) = [] := by
  unfold exposures
  have hni : newIndices (tr3Clean cl1 cl2) (tr4Clean cl1 cl2) = [45, 46, 47, 48, 49, 50, 51, 52, 53, 54] := by
    unfold newIndices; rw [tr3Clean_len, tr4Clean_len]; rfl
  rw [hni, List.append_eq_nil_iff]
  have hpq : ∀ j ∈ ([45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat),
      pqExposureAt (tr4Clean cl1 cl2) j = none := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    unfold pqExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    unfold tr4Clean; dsimp only
    repeat rw [at?_append_other_eq _ _ rfl]
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      repeat rw [at?_append_other_eq _ _ rfl]
      rw [Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr3Clean_len])]
    · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      repeat rw [at?_append_other_eq _ _ rfl]
      rw [Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr3Clean_len]; omega)]
    · rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len]), proj_inj_pqEvE]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
  have htr : ∀ j ∈ ([45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat),
      trExposureAt (tr4Clean cl1 cl2) j = none := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    unfold trExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    unfold tr4Clean; dsimp only
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · repeat (first | rw [at?_append_other_eq _ _ rfl] | rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)])
      rw [Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr3Clean_len])]
    · repeat (first | rw [at?_append_other_eq _ _ rfl] | rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)])
      rw [Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr3Clean_len]; omega)]
    · repeat (first | rw [at?_append_other_eq _ _ rfl] | rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)])
      rw [Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr3Clean_len]; omega)]
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr3Clean_len]; omega)]
  exact ⟨List.filterMap_eq_nil_iff.mpr hpq, List.filterMap_eq_nil_iff.mpr htr⟩

theorem exposures_tr4_tr5_eq (cl1 cl2 : Nat) :
    exposures (tr4Clean cl1 cl2) (tr5Clean cl1 cl2) = [] := by
  unfold exposures
  have hni : newIndices (tr4Clean cl1 cl2) (tr5Clean cl1 cl2) = [55, 56, 57, 58, 59] := by
    unfold newIndices; rw [tr4Clean_len, tr5Clean_len]; rfl
  rw [hni, List.append_eq_nil_iff]
  have hpq : ∀ j ∈ ([55, 56, 57, 58, 59] : List Nat),
      pqExposureAt (tr5Clean cl1 cl2) j = none := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    unfold pqExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    unfold tr5Clean; dsimp only
    repeat rw [at?_append_other_eq _ _ rfl]
    have hge : (tr4Clean cl1 cl2).length ≤ j := by
      rw [tr4Clean_len]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
    rw [Symbolic.Swarm.CREF.at?_ge_length _ hge]
  have htr : ∀ j ∈ ([55, 56, 57, 58, 59] : List Nat),
      trExposureAt (tr5Clean cl1 cl2) j = none := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    unfold trExposureAt
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    unfold tr5Clean; dsimp only
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr4Clean_len]; omega)]
      rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.CREF.at?_ge_length _ (by rw [tr4Clean_len])]
    · rw [at?_append_other_eq _ _ rfl]
      repeat rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr4Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr4Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry, tr4Clean_len]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr4Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr4Clean_len])]; rfl
    · rw [at?_append_other_eq _ _ rfl, Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry, tr4Clean_len]; omega)]
  exact ⟨List.filterMap_eq_nil_iff.mpr hpq, List.filterMap_eq_nil_iff.mpr htr⟩


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
