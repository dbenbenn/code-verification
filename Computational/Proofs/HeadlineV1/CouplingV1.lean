/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.ProbeBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.SpqrV1Sync.SendTotalExtras -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecvEqual
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Assembly
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidPhi
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvCt
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidRecvEk
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSendClosed
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidSize
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainDir
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainPrev
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainSmall
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Erasure
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecAdd
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ErasureDecMsg
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopBytesSize
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import ProofLib.BV.WidthNorm
import ProofLib.SepLogic.WP.StateNorm
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables

/-!
# Hidden-Salt Coupling and SPQR V1 No-Wrong-Salt Bridge

Connects the `KemFailTrackState` candidate validity invariant, multi-step `Corr.SpqrReachFrom`
receive-salt invariance (`spqrV1WitnessEvalSalt`), and `SpqrHistoryInv` to exclude
`EvictedDeliverForgeEvent` on evicted honest wires under `spqrV1SessionUniformCoins`.
-/

public section

set_option autoImplicit true

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-! ## `KemFailTrackState` candidate validity -/

/-- Invariant that any candidate pair `(s, r)` recorded in `tr.cand` satisfies
`K.honestExchangeFails s r = true`. -/
@[expose] def KemCandValid {F : ShaCompress} (K : MlKem) (tr : KemFailTrackState F) : Prop :=
  ∀ p, tr.cand = some p → K.honestExchangeFails p.1 p.2 = true

@[simp]
theorem stepKemFailSend_cand_eq (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    (stepKemFailSend F K tr Q r).cand =
      match tr.cand with
      | some p => some p
      | none =>
        if ekSide tr.e != kemBraidParty Q then
          match tr.c, tr.st Q with
          | .seed s, .headerReceived _ =>
            if K.honestExchangeFails s (encRandOf r) then some (s, encRandOf r) else none
          | _, _ => none
        else none := by
  unfold stepKemFailSend
  dsimp only
  cases (tr.st Q).send K (coinBytes r) <;> rfl

@[simp]
theorem stepKemFailDeliver_cand_eq (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    (stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  unfold stepKemFailDeliver
  rcases h1 : tr.sentB[j]? with _ | ⟨m, _⟩
  · rfl
  · dsimp only
    rcases h2 : (tr.st Q).recv K m with _ | out
    · rfl
    · dsimp only
      split_ifs
      · rcases h3 : tr.c with _ | _ | ⟨s, r⟩ <;> rfl
      · rfl

/-! ## Multi-step SPQR receive-salt invariance -/

section SendRecvSaltEq

open CryptoVerification.SpqrV1Sync.TopSync
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.SendTotal

theorem topStateW_braidOf (F : ShaCompress) (K : MlKem) {bytes : Bytes} {w : TopWitness F}
    (hw : TopStateW F K bytes w) :
    braidOf F K bytes = some w.st := by
  have hsize : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 :=
    hw.htop.hbytes ▸ topStateW_length_lt F K hw
  rw [hw.htop.hbytes]
  exact braidOf_topBytes F K w.st w.vn? w.ch? hsize (st_bCodec F w.st hw.hbok)

theorem topStateW_send_braid_eq (F : ShaCompress) (K : MlKem)
    {bytes bytes' : Bytes} {r : BitVec 512} {salt : Salt} {msg : Bytes}
    {w w' : TopWitness F} (hw : TopStateW F K bytes w) (hw' : TopStateW F K bytes' w')
    (hsend : (spqrV1SessionUniformCoins F K).send bytes r = some (bytes', salt, msg)) :
    ∃ m_out key tape',
      w.st.send K (coinBytes r) = .ok ({ msg := m_out, key := key, state := w'.st }, tape') := by
  have hsize : bytes.length < 2 ^ 64 := topStateW_length_lt F K hw
  have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 := hw.htop.hbytes ▸ hsize
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) w.st.into_pb = .ok w.st :=
    st_bCodec F w.st hw.hbok
  let tape := coinBytes r
  rcases hsendB : w.st.send K tape with err | ⟨⟨m, key, st'⟩, tape'⟩
  · exfalso
    change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes] at hsend
    unfold CryptoVerification.LibsignalSpqrV1.send at hsend
    rw [decodeState_topBytes F K w.st w.vn? w.ch? hsize'] at hsend
    rcases err with e | p <;> simp [topPb, spqrDeps, hcodec, liftStatesResult, hsendB] at hsend
  · have hep_pos : 1 ≤ w.st.epoch.toNat := by have := hw.htop.hsendLe; omega
    obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts F K w.st st' tape tape' m key hsendB
    have htop := send_topBytes F K w.st st' w.vn? w.ch? tape tape' m key hsize' hcodec hsendB
    let secret' : ℕ → Bytes :=
      match key with
      | none => w.secret
      | some es => Function.update w.secret (chainCur w.st + 1) es.secret
    have hsec_eq : ∀ e, 1 ≤ e → e ≤ w.chE.currentEpoch.toNat → secret' e = w.secret e := by
      intro e _ he
      have hcur := hw.htop.hcur
      cases key with
      | none => rfl
      | some es => exact Function.update_of_ne (by omega) _ _
    have hok' : ChainOk F w.authKey w.dir secret' w.sendCtr w.recvSet w.chE :=
      chainOk_congr F w.authKey w.dir w.secret secret' w.sendCtr w.recvSet w.chE hw.htop.hok hsec_eq
    have hsec : ∀ es, key = some es → es.secret = secret' es.epoch.toNat := by
      intro es hk
      subst hk
      obtain ⟨hes_ep, -⟩ := chainCur_send_key F K w.st st' tape tape' m es hep_pos hsendB
      change es.secret = Function.update w.secret (chainCur w.st + 1) es.secret es.epoch.toNat
      rw [hes_ep, Function.update_self]
    obtain ⟨chain1, hadd, hok1, _, hsend1, hle1⟩ :=
      tsnd_send_addEpoch F K w.authKey w.dir secret' w.st st' w.sendCtr w.recvSet w.chE hok'
        hw.htop.hcur hep_pos tape tape' m key hsendB hsec
    have he_ne0 : (m.epoch == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
      rw [hm_ep] at this
      omega
    have hebv_nat : (m.epoch - 1#64).toNat = w.st.epoch.toNat - 1 := by
      rw [hm_ep, BitVec.toNat_sub_of_le]
      · rfl
      · show 1 ≤ w.st.epoch.toNat
        exact hep_pos
    have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
      rw [hsend1, hw.htop.hsendEp, hebv_nat]
      have := hw.htop.hsendLe
      omega
    have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
      rw [hebv_nat]
      exact (epoch_sub_one_le_chainCur w.st).trans hle1
    have hctr_lt : w.sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 := by
      by_contra hge
      have herr := sendKey_err_of_ge F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1
        (m.epoch - 1#64) hlo hhi hge
      have hafter := sendAfterStates_err_of_sendKey_err F K w.authKey w.dir secret' w.st st'
        w.sendCtr w.recvSet w.vn? w.ch? w.chE chain1 hw.htop.hch hok' m key hadd he_ne0 herr
      change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
      rw [spqrV1_eq, toSpqrModel] at hsend
      dsimp only at hsend
      rw [hw.htop.hbytes, htop, hafter] at hsend
      nomatch hsend
    obtain ⟨chain2, hsk, _, _, _⟩ :=
      sendKey_ok F w.authKey w.dir secret' w.sendCtr w.recvSet chain1 hok1 (m.epoch - 1#64)
        hlo hhi hctr_lt
    rw [hebv_nat] at hsk
    have hafter := tsnd_sendAfterStates_ok F K w.authKey w.dir secret' w.st st' w.sendCtr w.recvSet
      w.vn? w.ch? w.chE chain1 chain2 hw.htop.hch hok' m key hadd he_ne0
      (BitVec.ofNat 32 (w.sendCtr (w.st.epoch.toNat - 1) + 1))
      (w.sendCtr (w.st.epoch.toNat - 1))
      (seedAt F w.authKey secret' w.dir (w.st.epoch.toNat - 1)) hsk
    change (spqrV1 F K).send bytes tape = some (bytes', salt, msg) at hsend
    rw [spqrV1_eq, toSpqrModel] at hsend
    dsimp only at hsend
    rw [hw.htop.hbytes, htop, hafter] at hsend
    dsimp only at hsend
    rw [tsnd_messageKeyToSalt_keyAt] at hsend
    simp only [Option.some.injEq, Prod.mk.injEq] at hsend
    obtain ⟨hbytes', -, -⟩ := hsend
    have hbok' : BOk st' :=
      st_bSendClosed F K st_encNew st_encNext w.st st' tape tape' m key hw.hbok hsendB
    have hbr1 : braidOf F K bytes' = some st' := by
      have hsize1 : (topBytes F K st' w.vn? (some chain2)).length < 2 ^ 64 :=
        hbytes'.symm ▸ topStateW_length_lt F K hw'
      rw [← hbytes']
      exact braidOf_topBytes F K st' w.vn? (some chain2) hsize1 (st_bCodec F st' hbok')
    have hbr2 : braidOf F K bytes' = some w'.st := topStateW_braidOf F K hw'
    rw [hbr1] at hbr2
    injection hbr2 with hst_eq
    subst hst_eq
    exact ⟨m, key, tape', rfl⟩

/-- Computes the SPQR V1 message salt of `msg` directly from a `TopWitness` without send coins. -/
@[expose] def spqrV1WitnessEvalSalt (F : ShaCompress) (w : TopWitness F) (msg : Bytes) : Salt :=
  match msgPreamble msg with
  | .ok pre =>
    evalSaltFromSeed F pre (seedAt F w.authKey w.secret w.dir.switch (msgChainEpoch pre))
  | .error _ => none

/-- Any successful `recv` of `msg` along `Corr.SpqrReachFrom` with
`msgChainEpoch pre ≤ w0.chE.currentEpoch.toNat` yields `spqrV1WitnessEvalSalt F w0 msg`. -/
theorem spqrV1_reachFrom_recv_salt_eq_of_epoch_le (F : ShaCompress) (K : MlKem)
    {pq0 pq1 pq2 msg : Bytes} {w0 : TopWitness F} {pre : MsgPreamble}
    {salt : Salt}
    (hw0 : TopStateW F K pq0 w0)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq0 pq1)
    (hparse : msgPreamble msg = .ok pre)
    (hle : msgChainEpoch pre ≤ w0.chE.currentEpoch.toNat)
    (hrecv : (spqrV1SessionUniformCoins F K).recv pq1 msg = .ok (pq2, salt)) :
    salt = spqrV1WitnessEvalSalt F w0 msg := by
  obtain ⟨w1, hw1, hauth, hdir, _, hseed⟩ := spqrReachFrom_topStateW F K hw0 hreach
  obtain ⟨pre', _, hparse', _, hsalt, _, _, _, _, _⟩ := topStateW_recv F K hw1 hrecv
  have hpre : pre = pre' := by
    rw [hparse] at hparse'
    exact Except.ok.inj hparse'
  subst hpre
  have hseed_eq := hseed (msgChainEpoch pre) hle
  rw [hauth, hdir] at hsalt hseed_eq
  simp [spqrV1WitnessEvalSalt, hparse, hsalt, hseed_eq]

/-! ## Prior-accept SPQR salt invariance and evicted forge exclusion -/

theorem topStateW_send_msgChainEpoch (F : ShaCompress) (K : MlKem)
    {bytes bytes' : Bytes} {r : BitVec 512} {salt : Salt} {msg : Bytes}
    {w w' : TopWitness F} (hw : TopStateW F K bytes w) (hw' : TopStateW F K bytes' w')
    (hsend : (spqrV1SessionUniformCoins F K).send bytes r = some (bytes', salt, msg)) :
    w'.st.epoch = w.st.epoch ∧
      ∃ pre : MsgPreamble,
        msgPreamble msg = .ok pre ∧
        msgChainEpoch pre = w.st.epoch.toNat - 1 := by
  obtain ⟨m, key, tape', hsendB⟩ := topStateW_send_braid_eq F K hw hw' hsend
  obtain ⟨hm_ep, hst'_ep, hpay, -⟩ := send_facts F K w.st w'.st (coinBytes r) tape' m key hsendB
  have hep_pos : 1 ≤ w.st.epoch.toNat := by have := hw.htop.hsendLe; omega
  have he_ne : m.epoch ≠ 0#64 := by
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    rw [hm_ep] at this
    omega
  have hsize' : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 :=
    hw.htop.hbytes ▸ topStateW_length_lt F K hw
  have htop := send_topBytes F K w.st w'.st w.vn? w.ch? (coinBytes r) tape' m key hsize'
    (st_bCodec F w.st hw.hbok) hsendB
  change (spqrV1 F K).send bytes (coinBytes r) = some (bytes', salt, msg) at hsend
  rw [spqrV1_eq, toSpqrModel] at hsend
  dsimp only at hsend
  rw [hw.htop.hbytes, htop] at hsend
  rcases hsas : sendAfterStates (spqrDeps F K) (spqrHkdfWith F)
      (topPb w.st w.vn? w.ch?) m key w'.st with _ | s
  · rw [hsas] at hsend; cases hsend
  · rw [hsas] at hsend
    dsimp only at hsend
    rcases hk : messageKeyToSalt? s.key with _ | salt'
    · rw [hk] at hsend; cases hsend
    · rw [hk] at hsend
      simp only [Option.some.injEq, Prod.mk.injEq] at hsend
      obtain ⟨_, _, rfl⟩ := hsend
      obtain ⟨idx, hmsg_eq⟩ := sendAfterStates_msg_eq _ _ _ _ _ _ hsas
      change s.msg = Message.serialize m idx at hmsg_eq
      obtain ⟨rem, hpre, -⟩ := msg_roundtrip F K m idx he_ne hpay
      rw [← hmsg_eq] at hpre
      refine ⟨hst'_ep, _, hpre, ?_⟩
      have hsub : (m.epoch - 1#64).toNat = w.st.epoch.toNat - 1 := by
        rw [hm_ep, BitVec.toNat_sub_of_le]
        · rfl
        · show 1 ≤ w.st.epoch.toNat
          exact hep_pos
      simp [msgChainEpoch, hsub]
theorem topStateW_recv_epoch_le (F : ShaCompress) (K : MlKem)
    {bytes msg bytes' : Bytes} {salt : Salt} {w w' : TopWitness F}
    (hw : TopStateW F K bytes w) (hw' : TopStateW F K bytes' w')
    (hrecv : (spqrV1SessionUniformCoins F K).recv bytes msg = .ok (bytes', salt)) :
    w.st.epoch.toNat ≤ w'.st.epoch.toNat := by
  have hsize : (topBytes F K w.st w.vn? w.ch?).length < 2 ^ 64 :=
    hw.htop.hbytes ▸ topStateW_length_lt F K hw
  obtain ⟨pre, _, hpre, -⟩ := topStateW_recv F K hw hrecv
  change (spqrV1 F K).recv bytes msg = .ok (bytes', salt) at hrecv
  rw [spqrV1_eq, toSpqrModel] at hrecv
  dsimp only at hrecv
  cases hr : CryptoVerification.LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) bytes msg with
  | error e => rw [hr] at hrecv; cases e <;> contradiction
  | ok r =>
    rw [hr] at hrecv
    dsimp only at hrecv
    cases hs : recvKeyToSalt? r.key with
    | none => rw [hs] at hrecv; contradiction
    | some s =>
      rw [hs] at hrecv
      injection hrecv with hpair
      have hstate : r.state = bytes' := (Prod.mk.inj hpair).1
      rw [hw.htop.hbytes] at hr
      by_cases hver : pre.version = 1#8
      · rw [recv_topBytes F K w.authKey w.dir w.st w.vn? w.ch? msg pre
          hsize hw.htop.hvn hpre hver] at hr
        unfold recvEqual at hr
        cases hdes : (spqrDeps F K).msgDeserialize pre.epoch pre.remaining with
        | error _ => rw [hdes] at hr; contradiction
        | ok m =>
          rw [hdes, treq_spqrDeps_statesFromPb F K w.st (st_bCodec F w.st hw.hbok)] at hr
          dsimp [bind, Except.bind] at hr
          cases hsr : (spqrDeps F K).statesRecv w.st m with
          | error _ => rw [hsr] at hr; contradiction
          | ok ks =>
            rcases ks with ⟨key, st'⟩
            rw [hsr] at hr
            dsimp [bind, Except.bind] at hr
            have hrecvB := treq_statesRecv_ok F K w.st st' m key hsr
            split_ifs at hr
            cases hcf : SpqrApiResult.ofError
                (chainFrom (spqrHkdfWith F) (w.ch?.map Chain.intoPb) w.vn?) with
            | error _ => rw [hcf] at hr; contradiction
            | ok chain0 =>
              rw [hcf] at hr
              obtain ⟨chain2, hstate'⟩ :
                  ∃ chain2 : Chain, r.state = topBytes F K st' none (some chain2) := by
                cases key with
                | none =>
                  dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, pure, Except.pure,
                    bind, Except.bind] at hr
                  cases hrk : chain0.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                  | error _ => rw [hrk] at hr; contradiction
                  | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, rfl⟩
                | some es =>
                  dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, bind, Except.bind] at hr
                  cases hadd : SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) es) with
                  | error _ => rw [hadd] at hr; contradiction
                  | ok chain1 =>
                    rw [hadd] at hr; dsimp at hr
                    cases hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
                    | error _ => rw [hrk] at hr; contradiction
                    | ok cm => rw [hrk] at hr; cases hr; exact ⟨cm.1, rfl⟩
              have hstate_eq : topBytes F K st' none (some chain2) = bytes' :=
                hstate'.symm.trans hstate
              have hbok' : BOk st' := by
                cases hek : isEkSide w.st
                · exact st_bRecvCt F K st_decFresh st_decAdd st_decMsg st_encNew
                    w.st st' m key hek hw.hbok hrecvB
                · exact st_bRecvEk F K st_decFresh st_decAdd st_decMsg st_encNew
                    w.st st' m key hek hw.hbok hrecvB
              have hbr1 : braidOf F K bytes' = some st' := by
                have hsize' : (topBytes F K st' none (some chain2)).length < 2 ^ 64 :=
                  hstate_eq.symm ▸ topStateW_length_lt F K hw'
                rw [← hstate_eq]
                exact braidOf_topBytes F K st' none (some chain2) hsize' (st_bCodec F st' hbok')
              have hbr2 : braidOf F K bytes' = some w'.st := topStateW_braidOf F K hw'
              rw [hbr1] at hbr2
              injection hbr2 with hst_eq
              rw [← hst_eq]
              exact treq_recv_epoch_le F K w.st st' m key hrecvB
      · rcases hw.htop.hvn with hvn | hvn
        · rw [hvn] at hsize hr
          unfold CryptoVerification.LibsignalSpqrV1.recv at hr
          rw [hpre, decodeState_topBytes F K w.st none w.ch? hsize] at hr
          dsimp only [spqrDeps, SpqrApiResult.ofError, bind, Except.bind, topPb, stateVersion,
            Version.toU8] at hr
          have hbne : (pre.version != 1#8) = true := bne_iff_ne.mpr hver
          by_cases hlt : pre.version < 1#8 <;> simp [hlt, hbne] at hr
        · rw [hvn] at hsize hr
          unfold CryptoVerification.LibsignalSpqrV1.recv at hr
          rw [hpre, decodeState_topBytes F K w.st (some (vnOf w.dir w.authKey)) w.ch? hsize] at hr
          by_cases hlt : pre.version < 1#8
          · change (if pre.version < 1#8 then
              Except.error (SpqrApiError.err Error.minimumVersion) else _) = Except.ok r at hr
            simp only [hlt, ↓reduceIte] at hr; contradiction
          · have hgt : pre.version > 1#8 := by
              simp only [gt_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat] at hlt ⊢
              have hne : pre.version.toNat ≠ 1 := fun h => hver (BitVec.eq_of_toNat_eq h)
              omega
            change (if pre.version < 1#8 then _
              else if (pre.version != 1#8 && !true) = true then _
              else if (1#8 == 0#8) = true then _
              else if pre.version > 1#8 then
                do
                  let chain0 ← SpqrApiResult.ofError
                    (chainFrom (spqrHkdfWith F) (w.ch?.map Chain.intoPb)
                      (some (vnOf w.dir w.authKey)))
                  let __x ← SpqrApiResult.ofChainResult
                    (chain0.recvKey (spqrHkdfWith F) 0#64 pre.index)
                  Except.ok {
                    key := some __x.2
                    state := topBytes F K w.st (some (vnOf w.dir w.authKey)) (some __x.1)
                  }
              else _) = Except.ok r at hr
            simp only [hlt, hgt, Bool.not_true, Bool.and_false, ↓reduceIte] at hr
            cases hcf : SpqrApiResult.ofError
                (chainFrom (spqrHkdfWith F) (w.ch?.map Chain.intoPb)
                  (some (vnOf w.dir w.authKey))) with
            | error _ => rw [hcf] at hr; contradiction
            | ok chain0 =>
              rw [hcf] at hr; dsimp [bind, Except.bind] at hr
              cases hrk : SpqrApiResult.ofChainResult
                  (chain0.recvKey (spqrHkdfWith F) 0#64 pre.index) with
              | error _ => rw [hrk] at hr; contradiction
              | ok cm =>
                rw [hrk] at hr; cases hr
                change topBytes F K w.st (some (vnOf w.dir w.authKey)) (some cm.1) =
                  bytes' at hstate
                have hbr1 : braidOf F K bytes' = some w.st := by
                  have hsize' :
                      (topBytes F K w.st (some (vnOf w.dir w.authKey))
                        (some cm.1)).length < 2 ^ 64 :=
                    hstate.symm ▸ topStateW_length_lt F K hw'
                  rw [← hstate]
                  exact braidOf_topBytes F K w.st (some (vnOf w.dir w.authKey)) (some cm.1)
                    hsize' (st_bCodec F w.st hw.hbok)
                have hbr2 : braidOf F K bytes' = some w'.st := topStateW_braidOf F K hw'
                rw [hbr1] at hbr2
                injection hbr2 with hst_eq
                rw [← hst_eq]
theorem topStateW_reachFrom_epoch_le (F : ShaCompress) (K : MlKem)
    {pq₀ pq₁ : Bytes} {w₀ : TopWitness F} (hw₀ : TopStateW F K pq₀ w₀)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq₀ pq₁) :
    ∃ w₁ : TopWitness F, TopStateW F K pq₁ w₁ ∧ w₀.st.epoch.toNat ≤ w₁.st.epoch.toNat := by
  induction hreach with
  | refl => exact ⟨w₀, hw₀, le_rfl⟩
  | send _ hsend ih =>
    obtain ⟨w, hw, hle⟩ := ih
    obtain ⟨w', hw', -⟩ := topStateW_send F K hw hsend
    obtain ⟨heq, -⟩ := topStateW_send_msgChainEpoch F K hw hw' hsend
    exact ⟨w', hw', by rw [heq]; exact hle⟩
  | recv _ hrecv ih =>
    obtain ⟨w, hw, hle⟩ := ih
    obtain ⟨_, w', -, -, -, hw', -⟩ := topStateW_recv F K hw hrecv
    exact ⟨w', hw', hle.trans (topStateW_recv_epoch_le F K hw hw' hrecv)⟩

theorem spqrV1_sender_reachFrom_msgChainEpoch_le (F : ShaCompress) (K : MlKem)
    {pq_s₀ pq_s₀' pq_s₁ pq_s₁' msg₀ msg₁ : Bytes}
    {r₀ r₁ : BitVec 512} {salt₀ salt₁ : Salt} {w_s₀ : TopWitness F}
    (hw_s₀ : TopStateW F K pq_s₀ w_s₀)
    (hsend₀ : (spqrV1SessionUniformCoins F K).send pq_s₀ r₀ = some (pq_s₀', salt₀, msg₀))
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq_s₀ pq_s₁)
    (hsend₁ : (spqrV1SessionUniformCoins F K).send pq_s₁ r₁ = some (pq_s₁', salt₁, msg₁)) :
    ∃ pre₀ pre₁ : MsgPreamble,
      msgPreamble msg₀ = .ok pre₀ ∧
      msgPreamble msg₁ = .ok pre₁ ∧
      msgChainEpoch pre₀ ≤ msgChainEpoch pre₁ := by
  obtain ⟨w_s₀', hw_s₀', -⟩ := topStateW_send F K hw_s₀ hsend₀
  obtain ⟨-, pre₀, hpre₀, hmce₀⟩ := topStateW_send_msgChainEpoch F K hw_s₀ hw_s₀' hsend₀
  obtain ⟨w_s₁, hw_s₁, hep_le⟩ := topStateW_reachFrom_epoch_le F K hw_s₀ hreach
  obtain ⟨w_s₁', hw_s₁', -⟩ := topStateW_send F K hw_s₁ hsend₁
  obtain ⟨-, pre₁, hpre₁, hmce₁⟩ := topStateW_send_msgChainEpoch F K hw_s₁ hw_s₁' hsend₁
  exact ⟨pre₀, pre₁, hpre₀, hpre₁, by omega⟩

/-- Prior acceptance of `msg_acc` with `msgChainEpoch pre ≤ msgChainEpoch pre_acc` fixes the
receive salt of `msg` along all later reachable states to `spqrV1WitnessEvalSalt F w_acc msg`. -/
theorem spqrV1_prior_accept_reachFrom_recv_salt_eq (F : ShaCompress) (K : MlKem)
    {pq_acc pq_acc' pq₀ pq₁ pq₂ msg msg_acc : Bytes}
    {w_acc w₀ : TopWitness F} {pre pre_acc : MsgPreamble} {salt_acc salt : Salt}
    (hw_acc : TopStateW F K pq_acc w_acc)
    (hw₀ : TopStateW F K pq₀ w₀)
    (hrecv_acc : (spqrV1SessionUniformCoins F K).recv pq_acc msg_acc = .ok (pq_acc', salt_acc))
    (hpre_acc : msgPreamble msg_acc = .ok pre_acc)
    (hpre : msgPreamble msg = .ok pre)
    (hle_acc : msgChainEpoch pre ≤ msgChainEpoch pre_acc)
    (hreach₀ : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq_acc pq₀)
    (hreach₁ : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq₀ pq₁)
    (hrecv : (spqrV1SessionUniformCoins F K).recv pq₁ msg = .ok (pq₂, salt)) :
    msgChainEpoch pre ≤ w₀.chE.currentEpoch.toNat ∧
      salt = spqrV1WitnessEvalSalt F w₀ msg ∧
      salt = spqrV1WitnessEvalSalt F w_acc msg := by
  obtain ⟨pre_acc', _, hpre_acc', hmce_acc, -, -, -, -, -, -⟩ := topStateW_recv F K hw_acc hrecv_acc
  have heq_acc : pre_acc = pre_acc' := by
    rw [hpre_acc] at hpre_acc'
    exact Except.ok.inj hpre_acc'
  subst heq_acc
  have hle_w_acc : msgChainEpoch pre ≤ w_acc.chE.currentEpoch.toNat := hle_acc.trans hmce_acc
  obtain ⟨w₀', hw₀', -, -, hcur₀, -⟩ := spqrReachFrom_topStateW F K hw_acc hreach₀
  have hbr1 : braidOf F K pq₀ = some w₀.st := topStateW_braidOf F K hw₀
  have hbr2 : braidOf F K pq₀ = some w₀'.st := topStateW_braidOf F K hw₀'
  rw [hbr1] at hbr2
  injection hbr2 with hst_eq
  have hcur_eq : w₀.chE.currentEpoch.toNat = w₀'.chE.currentEpoch.toNat := by
    rw [hw₀.htop.hcur, hw₀'.htop.hcur, hst_eq]
  have hle_w₀ : msgChainEpoch pre ≤ w₀.chE.currentEpoch.toNat := by omega
  have hsalt₀ := spqrV1_reachFrom_recv_salt_eq_of_epoch_le F K hw₀ hreach₁ hpre hle_w₀ hrecv
  have hreach_all : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) pq_acc pq₁ := by
    clear hrecv hsalt₀ hle_w₀ hcur_eq hst_eq hbr1 hcur₀ hw₀' hw₀
    induction hreach₁ with
    | refl => exact hreach₀
    | send _ hs ih => exact .send ih hs
    | recv _ hr ih => exact .recv ih hr
  have hsalt_acc :=
    spqrV1_reachFrom_recv_salt_eq_of_epoch_le F K hw_acc hreach_all hpre hle_w_acc hrecv
  exact ⟨hle_w₀, hsalt₀, hsalt_acc⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [SampleableType PQC] in
/-- Pre-draw candidate triples `(w, salt, epExp₀ t)` derived from an acceptance witness `w_acc`
and honest-wire list `honest`. -/
@[expose] def evictedSpurCandList (P : Params Bytes PQC) (epExp₀ : ℕ → BitVec 256)
    (w_acc : TopWitness P.C.F) (honest : List (List (BitVec 8) × Fig8C Pt)) :
    List (List (BitVec 8) × Salt × BitVec 256) :=
  honest.filterMap fun wc =>
    match (signalWireCodec P.codec).parse (wc.1.take (wc.1.length - 8)) with
    | some (h, _) =>
      some (wc.1, spqrV1WitnessEvalSalt P.C.F w_acc h.pqRatchet, epExp₀ wc.2.1.1)
    | none => none

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [SampleableType PQC] in
theorem evictedSpurCandList_length_le (P : Params Bytes PQC) (epExp₀ : ℕ → BitVec 256)
    (w_acc : TopWitness P.C.F) (honest : List (List (BitVec 8) × Fig8C Pt)) :
    (evictedSpurCandList P epExp₀ w_acc honest).length ≤ honest.length :=
  List.length_filterMap_le _ _

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [SampleableType PQC] in
theorem mem_evictedSpurCandList_of_honest
    (P : Params Bytes PQC) (epExp₀ epExp : ℕ → BitVec 256)
    (w_acc : TopWitness P.C.F) (honest : List (List (BitVec 8) × Fig8C Pt))
    (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (hc_mem : (w, c) ∈ honest)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hep_eq : epExp c.1.1 = epExp₀ c.1.1) :
    (w, spqrV1WitnessEvalSalt P.C.F w_acc h.pqRatchet, epExp c.1.1) ∈
      evictedSpurCandList P epExp₀ w_acc honest := by
  unfold evictedSpurCandList
  rw [List.mem_filterMap]
  refine ⟨(w, c), hc_mem, ?_⟩
  simp [hparse, hep_eq]

/-- History invariant recording `TopStateW` witnesses and `Corr.SpqrReachFrom` paths for past
honest SPQR sends, same-sender epoch orderings, and active receiving-chain acceptances. -/
structure SpqrHistoryInv (P : Params Bytes (BitVec 512)) (K : MlKem)
    (s : SimState Bytes Pt ℓ) : Prop where
  hhon_send :
    ∀ w c h body, (w, c) ∈ s.honest →
      (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
      ∃ pq_s pq_s' r₀ salt₀ w_s,
        TopStateW P.C.F K pq_s w_s ∧
        (spqrV1SessionUniformCoins P.C.F K).send pq_s r₀ = some (pq_s', salt₀, h.pqRatchet) ∧
        Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) pq_s (s.pq (Party.senderOf c.1.1))
  hhon_ord :
    ∀ w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁,
      (w₀, c₀) ∈ s.honest → (w₁, c₁) ∈ s.honest →
      Party.senderOf c₀.1.1 = Party.senderOf c₁.1.1 →
      c₀.1.1 < c₁.1.1 →
      (signalWireCodec P.codec).parse (w₀.take (w₀.length - 8)) = some (h₀, body₀) →
      (signalWireCodec P.codec).parse (w₁.take (w₁.length - 8)) = some (h₁, body₁) →
      ∃ pq_s₀ pq_s₀' pq_s₁ pq_s₁' r₀ r₁ salt₀ salt₁ w_s₀,
        TopStateW P.C.F K pq_s₀ w_s₀ ∧
        (spqrV1SessionUniformCoins P.C.F K).send pq_s₀ r₀ = some (pq_s₀', salt₀, h₀.pqRatchet) ∧
        Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) pq_s₀ pq_s₁ ∧
        (spqrV1SessionUniformCoins P.C.F K).send pq_s₁ r₁ = some (pq_s₁', salt₁, h₁.pqRatchet)
  hchain_acc :
    ∀ (Q : Party) (t_acc : ℕ),
      t_acc ∈ (s.chains Q).map (·.epoch) → 1 ≤ t_acc →
      ∃ w_acc_wire c_acc h_acc body_acc pq_acc pq_acc' salt_acc w_acc,
        (w_acc_wire, c_acc) ∈ s.honest ∧
        c_acc.1.1 = t_acc ∧
        Party.senderOf c_acc.1.1 = Q.other ∧
        (signalWireCodec P.codec).parse (w_acc_wire.take (w_acc_wire.length - 8)) =
          some (h_acc, body_acc) ∧
        TopStateW P.C.F K pq_acc w_acc ∧
        (spqrV1SessionUniformCoins P.C.F K).recv pq_acc h_acc.pqRatchet = .ok (pq_acc', salt_acc) ∧
        Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) pq_acc (s.pq Q)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrReachFrom_trans {F : ShaCompress} {K : MlKem}
    {s₀ s₁ s₂ : Bytes} (h₀₁ : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) s₀ s₁)
    (h₁₂ : Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) s₁ s₂) :
    Corr.SpqrReachFrom (spqrV1SessionUniformCoins F K) s₀ s₂ := by
  induction h₁₂ with
  | refl => exact h₀₁
  | send _ hsend ih => exact .send ih hsend
  | recv _ hrecv ih => exact .recv ih hrecv

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_init (P : Params Bytes (BitVec 512)) (K : MlKem) (pqA pqB : Bytes) :
    SpqrHistoryInv P K (initSim pqA pqB : SimState Bytes Pt ℓ) ∧
      SpqrHistoryInv P K (initSimC pqA pqB : LibsignalToModularSchemeSimState Bytes Pt ℓ).base := by
  have h0 : SpqrHistoryInv P K (initSim pqA pqB : SimState Bytes Pt ℓ) :=
    ⟨by intro _ _ _ _ hmem; simp [initSim] at hmem,
     by intro _ _ _ _ _ _ _ _ hmem; simp [initSim] at hmem,
     by intro Q _ hmem hge1; cases Q <;> { simp [initSim] at hmem; try omega }⟩
  exact ⟨h0, h0⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_preserve_of_sub
    {P : Params Bytes (BitVec 512)} {K : MlKem}
    {s s' : SimState Bytes Pt ℓ}
    (hhist : SpqrHistoryInv P K s)
    (hhon : s'.honest = s.honest)
    (hreach : ∀ Q, Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) (s'.pq Q))
    (hchains : ∀ Q t, t ∈ (s'.chains Q).map (·.epoch) → t ∈ (s.chains Q).map (·.epoch)) :
    SpqrHistoryInv P K s' where
  hhon_send w c h body hmem hparse := by
    obtain ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hsend, hr₀⟩ :=
      hhist.hhon_send w c h body (hhon ▸ hmem) hparse
    exact ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hsend,
      spqrReachFrom_trans hr₀ (hreach (Party.senderOf c.1.1))⟩
  hhon_ord w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁ hm₀ hm₁ hsend_eq hlt hp₀ hp₁ :=
    hhist.hhon_ord w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁ (hhon ▸ hm₀) (hhon ▸ hm₁) hsend_eq hlt hp₀ hp₁
  hchain_acc Q t_acc hmem hge1 := by
    obtain ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
        hm_a, heq_a, hsend_a, hp_a, hw_a, hrecv_a, hr_a⟩ :=
      hhist.hchain_acc Q t_acc (hchains Q t_acc hmem) hge1
    exact ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
      hhon.symm ▸ hm_a, heq_a, hsend_a, hp_a, hw_a, hrecv_a,
      spqrReachFrom_trans hr_a (hreach Q)⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_preserve_new_chain
    {P : Params Bytes (BitVec 512)} {K : MlKem}
    {s s' : SimState Bytes Pt ℓ}
    {P_party : Party} {w_new : List (BitVec 8)} {c_new : Fig8C Pt}
    {h_new : SignalHeader} {body_new : List (BitVec 8)}
    {pq' : Bytes} {salt_new : Salt} {w_top : TopWitness P.C.F}
    (hhist : SpqrHistoryInv P K s)
    (hhon : s'.honest = s.honest)
    (hpq : s'.pq = Function.update s.pq P_party pq')
    (hc_mem : (w_new, c_new) ∈ s.honest)
    (hc_sender : Party.senderOf c_new.1.1 = P_party.other)
    (hparse : (signalWireCodec P.codec).parse (w_new.take (w_new.length - 8)) =
      some (h_new, body_new))
    (hw_top : TopStateW P.C.F K (s.pq P_party) w_top)
    (hrecv : (spqrV1SessionUniformCoins P.C.F K).recv (s.pq P_party) h_new.pqRatchet = .ok (pq', salt_new))
    (hchains : ∀ Q t, t ∈ (s'.chains Q).map (·.epoch) →
      t ∈ (s.chains Q).map (·.epoch) ∨ (Q = P_party ∧ t = c_new.1.1)) :
    SpqrHistoryInv P K s' := by
  have hreach : ∀ Q, Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) (s'.pq Q) := by
    intro Q
    rw [hpq]
    by_cases hQ : Q = P_party
    · subst hQ; rw [Function.update_self]; exact .recv (.refl _) hrecv
    · rw [Function.update_of_ne hQ]; exact .refl _
  refine ⟨?_, ?_, ?_⟩
  · intro w c h body hmem hp
    obtain ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hsend, hr₀⟩ :=
      hhist.hhon_send w c h body (hhon ▸ hmem) hp
    exact ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hsend,
      spqrReachFrom_trans hr₀ (hreach (Party.senderOf c.1.1))⟩
  · intro w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁ hm₀ hm₁ hsend_eq hlt hp₀ hp₁
    exact hhist.hhon_ord w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁
      (hhon ▸ hm₀) (hhon ▸ hm₁) hsend_eq hlt hp₀ hp₁
  · intro Q t_acc hmem hge1
    rcases hchains Q t_acc hmem with hold | ⟨rfl, rfl⟩
    · obtain ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
          hm_a, heq_a, hsend_a, hp_a, hw_a, hrecv_a, hr_a⟩ :=
        hhist.hchain_acc Q t_acc hold hge1
      exact ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
        hhon.symm ▸ hm_a, heq_a, hsend_a, hp_a, hw_a, hrecv_a,
        spqrReachFrom_trans hr_a (hreach Q)⟩
    · exact ⟨w_new, c_new, h_new, body_new, s.pq Q, pq', salt_new, w_top,
        hhon.symm ▸ hc_mem, rfl, hc_sender, hparse, hw_top, hrecv, hreach Q⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_preserve_send
    {P : Params Bytes (BitVec 512)} {K : MlKem}
    {s s' : SimState Bytes Pt ℓ}
    {P_party : Party} {w_new : List (BitVec 8)} {c_new : Fig8C Pt}
    {pq' pqMsg : Bytes} {rq : BitVec 512} {salt : Salt} {w_top : TopWitness P.C.F}
    (hhist : SpqrHistoryInv P K s)
    (hhon : s'.honest = (w_new, c_new) :: s.honest)
    (hpq : s'.pq = Function.update s.pq P_party pq')
    (hchains : ∀ Q t, t ∈ (s'.chains Q).map (·.epoch) → t ∈ (s.chains Q).map (·.epoch))
    (hsender : Party.senderOf c_new.1.1 = P_party)
    (hw_top : TopStateW P.C.F K (s.pq P_party) w_top)
    (hsend : (spqrV1SessionUniformCoins P.C.F K).send (s.pq P_party) rq = some (pq', salt, pqMsg))
    (hpqmsg : ∀ h body,
      (signalWireCodec P.codec).parse (w_new.take (w_new.length - 8)) = some (h, body) →
      h.pqRatchet = pqMsg)
    (hord_old : ∀ w₀ c₀, (w₀, c₀) ∈ s.honest →
      Party.senderOf c₀.1.1 = P_party → c₀.1.1 ≤ c_new.1.1) :
    SpqrHistoryInv P K s' := by
  have hreach : ∀ Q, Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) (s'.pq Q) := by
    intro Q
    rw [hpq]
    by_cases hQ : Q = P_party
    · subst hQ; rw [Function.update_self]; exact .send (.refl _) hsend
    · rw [Function.update_of_ne hQ]; exact .refl _
  refine ⟨?_, ?_, ?_⟩
  · intro w c h body hmem hp
    rw [hhon] at hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · rcases Prod.mk.inj hhead with ⟨rfl, rfl⟩
      refine ⟨s.pq P_party, pq', rq, salt, w_top, hw_top, ?_, ?_⟩
      · rwa [hpqmsg h body hp]
      · rw [hsender]; exact hreach P_party
    · obtain ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hs₀, hr₀⟩ :=
        hhist.hhon_send w c h body htail hp
      exact ⟨pq_s, pq_s', r₀, salt₀, w_s, hw_s, hs₀,
        spqrReachFrom_trans hr₀ (hreach (Party.senderOf c.1.1))⟩
  · intro w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁ hm₀ hm₁ hsend_eq hlt hp₀ hp₁
    rw [hhon] at hm₀ hm₁
    rcases List.mem_cons.mp hm₀ with hhead₀ | htail₀ <;>
      rcases List.mem_cons.mp hm₁ with hhead₁ | htail₁
    · rcases Prod.mk.inj hhead₀ with ⟨_, rfl⟩
      rcases Prod.mk.inj hhead₁ with ⟨_, rfl⟩
      omega
    · rcases Prod.mk.inj hhead₀ with ⟨_, rfl⟩
      have hle := hord_old w₁ c₁ htail₁ (hsend_eq.symm.trans hsender)
      omega
    · rcases Prod.mk.inj hhead₁ with ⟨rfl, rfl⟩
      obtain ⟨pq_s₀, pq_s₀', r₀, salt₀, w_s₀, hw_s₀, hs₀, hr₀⟩ :=
        hhist.hhon_send w₀ c₀ h₀ body₀ htail₀ hp₀
      rw [hsend_eq, hsender] at hr₀
      refine ⟨pq_s₀, pq_s₀', s.pq P_party, pq', r₀, rq, salt₀, salt, w_s₀,
        hw_s₀, hs₀, hr₀, ?_⟩
      rwa [hpqmsg h₁ body₁ hp₁]
    · exact hhist.hhon_ord w₀ c₀ h₀ body₀ w₁ c₁ h₁ body₁ htail₀ htail₁ hsend_eq hlt hp₀ hp₁
  · intro Q t_acc hmem hge1
    obtain ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
        hm_a, heq_a, hsend_a, hp_a, hw_a, hrecv_a, hr_a⟩ :=
      hhist.hchain_acc Q t_acc (hchains Q t_acc hmem) hge1
    refine ⟨w_a, c_a, h_a, body_a, pq_a, pq_a', salt_a, w_acc,
      ?_, heq_a, hsend_a, hp_a, hw_a, hrecv_a, spqrReachFrom_trans hr_a (hreach Q)⟩
    rw [hhon]
    exact List.mem_cons_of_mem _ hm_a

theorem ghostChain_accept_epoch (g : GhostChain) (i : ℕ) :
    (g.accept i).epoch = g.epoch := by
  unfold GhostChain.accept
  split <;> rfl

theorem map_epoch_modify_accept (cs : List GhostChain) (ci i : ℕ) :
    (cs.modify ci (·.accept i)).map (·.epoch) = cs.map (·.epoch) := by
  induction cs generalizing ci with
  | nil => simp
  | cons hd tl ih =>
    cases ci with
    | zero => simp [ghostChain_accept_epoch]
    | succ n => simp [ih n]

theorem mem_map_epoch_pushChain {cs : List GhostChain} {g : GhostChain} {t : ℕ}
    (h : t ∈ (pushChain cs g).map (·.epoch)) :
    t = g.epoch ∨ t ∈ cs.map (·.epoch) := by
  unfold pushChain at h
  rcases List.mem_map.mp h with ⟨c, hc_drop, rfl⟩
  rcases List.mem_append.mp (List.mem_of_mem_drop hc_drop) with hc | hc
  · exact Or.inr (List.mem_map_of_mem hc)
  · rw [List.mem_singleton.mp hc]
    exact Or.inl rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_onAcceptPure_some {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w_wire : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci : ℕ) (k_ratchet : PublicKey) (pq' : Bytes)
    (s : SimState Bytes Pt ℓ)
    (hhist : SpqrHistoryInv P K s)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq') :
    SpqrHistoryInv P K (onAcceptPure qep Q w_wire isDel t i m (some ci) k_ratchet pq' s).2 := by
  have hmod : ∀ mir', SpqrHistoryInv P K
      { s with
        mir := mir'
        chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i))
        pq := Function.update s.pq Q pq'
        unackA := s.unackA && Q != Party.A } := fun mir' =>
    spqrHistoryInv_preserve_of_sub hhist rfl
      (fun R => by
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self]; exact hreach
        · simp [Function.update_of_ne hR]; exact .refl _)
      (fun R t' ht' => by
        by_cases hR : R = Q
        · subst hR
          simpa [Function.update_self, map_epoch_modify_accept] using ht'
        · simpa [Function.update_of_ne hR] using ht')
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w_wire with
    | none => exact hhist
    | some r => exact hmod _
  · split
    · exact hhist
    · split
      · exact hmod _
      · exact spqrHistoryInv_preserve_of_sub hhist rfl (fun _ => .refl _) (fun _ _ h => h)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spqrHistoryInv_onAcceptPure_none {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w_wire : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (k_ratchet : PublicKey) (pq' : Bytes)
    (s : SimState Bytes Pt ℓ)
    (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (salt : Salt) (w_acc : TopWitness P.C.F)
    (hhist : SpqrHistoryInv P K s)
    (hc_mem : (w, c) ∈ s.honest)
    (ht_eq : t = c.1.1)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw_acc : TopStateW P.C.F K (s.pq Q) w_acc)
    (hrecv : (spqrV1SessionUniformCoins P.C.F K).recv (s.pq Q) h.pqRatchet = .ok (pq', salt)) :
    SpqrHistoryInv P K (onAcceptPure qep Q w_wire isDel t i m none k_ratchet pq' s).2 := by
  have hnew : ∀ mir', SpqrHistoryInv P K
      { s with
        mir := mir'
        chains := Function.update s.chains Q
          (pushChain (s.chains Q) (GhostChain.accept ⟨some k_ratchet, t, 0, []⟩ i))
        pq := Function.update s.pq Q pq'
        unackA := s.unackA && Q != Party.A } := fun mir' =>
    spqrHistoryInv_preserve_new_chain hhist rfl rfl hc_mem hc_sender hparse hw_acc hrecv
      (fun R t' ht' => by
        dsimp only at ht'
        by_cases hR : R = Q
        · subst hR
          rw [Function.update_self] at ht'
          rcases mem_map_epoch_pushChain ht' with heq | hmem
          · rw [ghostChain_accept_epoch] at heq
            exact Or.inr ⟨rfl, heq.trans ht_eq⟩
          · exact Or.inl hmem
        · rw [Function.update_of_ne hR] at ht'
          exact Or.inl ht')
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w_wire with
    | none => exact hhist
    | some r => exact hnew _
  · split
    · exact hhist
    · split
      · exact hnew _
      · exact spqrHistoryInv_preserve_of_sub hhist rfl (fun _ => .refl _) (fun _ _ h => h)

/-- Most recent receiving-chain acceptance epoch for `Q` (`mir.epoch Q` in a receive-only epoch,
else `mir.epoch Q - 1`). -/
@[expose] def evictAccEpoch {ℓ : ℕ} (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party) : ℕ :=
  if inReceiveOnlyEpoch mir Q then mir.epoch Q else mir.epoch Q - 1

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
/-- Honest wires sent at DR epochs strictly before `t_bound`. -/
@[expose] def honestBeforeEpoch (honest : List (List (BitVec 8) × Fig8C Pt)) (t_bound : ℕ) :
    List (List (BitVec 8) × Fig8C Pt) :=
  honest.filter fun wc => decide (wc.2.1.1 < t_bound)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestBeforeEpoch_cons_of_le (honest : List (List (BitVec 8) × Fig8C Pt))
    (w : List (BitVec 8)) (c : Fig8C Pt) (t_bound : ℕ) (hle : t_bound ≤ c.1.1) :
    honestBeforeEpoch ((w, c) :: honest) t_bound = honestBeforeEpoch honest t_bound := by
  unfold honestBeforeEpoch
  have hnot : ¬ (c.1.1 < t_bound) := by omega
  simp [hnot]

end SendRecvSaltEq

end CryptoGames.LibsignalSM.Proofs.Refinement
