/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.DYBridge.DY.Bytes.Basic
import DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Clean-Prefix Foundations Part A (`CleanPrefixA.lean`)

1. `SpqrStateAgree`, `StateBytesAgree`, `stateBytesAgree_aliceStartOpk`, and `stateBytesAgree_encrypt`.
2. Canonical `encMsg` protobuf inversion (`encMsg_tryFrom_inv`, `encMsg_faithfulInner`).
3. Front-to-back peeling (`PeeledCall`, `PeeledValid`, `clsOfCalls`) and trace invariants.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.PQXDH (serializedIk pqxdhKdf pqxdhIkm agree)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg SessionInfo kdfCk createChain trMsgKeys computeMac trHonestWireMsg
   spqrA2B messageVersion isCurrentSnapshot)
open DY.Libsignal.Refinement
  (aesCbcEncryptSymbol WireFields canonicalVariation)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost PreKeyFields Step VisEntry BundlePreKeyIds
   runSteps StepsWF RunMatches MatchesEventsAt nextBundleIds stepIn
   gamma gamma' concretizeAll concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey
   concretizeSpqrSendMsg trWireBytes spqrKeyBytes spqrHeaded FaithfulInner)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0 (keepOpkI0)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws (keepOpkI0_cryptoEquationsHold)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (trace0 ev ev_not_rejected trace0_take_succ)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace (ValidCoinLens)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encSig encMsg parse_encMsg aliceOutOpk aliceOutOpt aliceSt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB spkB pqskB opkB)
open Symbolic.Swarm.CREF.TR
  (gamma_concat gamma_hmac gamma_dhPk gamma_kemEncap_fst gamma_kemEncap_snd gamma_spqrChainKey
   gamma_serializedIk gamma_trMsgKeys_cipherKey gamma_trMsgKeys_iv gamma_trMsgKeys_macKey
   gamma_computeMac gamma_agree gamma_pqxdhIkm gamma_pqxdhKdf gamma_createChain_snd
   gamma_kdfCk_fst gamma_kdfCk_snd gamma_hkdfBlock1 gamma_whisperRatchet
   gamma_spqrParams_a2b gamma_spqrIdx)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound (ms_pack_trWire ms_pack_sym)

attribute [local irreducible] WitnessParse.ev

/-! ## 1. `SpqrStateAgree`, `StateBytesAgree`, and Step Congruence -/

theorem gamma_spqrInitE (S : OpaqueSymbolSemantics) (g : Ghost) (a p : Bytes) :
    gamma keepOpkI0 S g (DY.Spqr.spqrInit a p) =
      S.init (gamma keepOpkI0 S g a) (gamma keepOpkI0 S g p) := by
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll keepOpkI0 S g)]; rfl

theorem gamma_spqrSendStateE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma keepOpkI0 S g (({ st, coins := c } : DY.Spqr.SendState.SubF Bytes).pack) =
      S.sendState (gamma keepOpkI0 S g st) (gamma keepOpkI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll keepOpkI0 S g)]; rfl

theorem gamma_spqrSendKeyE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma keepOpkI0 S g (({ st, coins := c } : DY.Spqr.SendKey.SubF Bytes).pack) =
      spqrKeyBytes (S.sendKey (gamma keepOpkI0 S g st) (gamma keepOpkI0 S g c)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll keepOpkI0 S g)]; rfl

theorem gamma_spqrSendMsgE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma keepOpkI0 S g (({ st, coins := c } : DY.Spqr.SendMsg.SubF Bytes).pack) =
      S.sendMsg (gamma keepOpkI0 S g st) (gamma keepOpkI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll keepOpkI0 S g)]; rfl

theorem gamma_symEncE (S : OpaqueSymbolSemantics) (g : Ghost) (k iv m : Bytes) :
    gamma keepOpkI0 S g (DY.SymEnc.symEnc k iv m) =
      (keepOpkI0 aesCbcEncryptSymbol
        [gamma keepOpkI0 S g m, gamma keepOpkI0 S g k, (gamma keepOpkI0 S g iv).take 16]).getD [] := by
  unfold gamma
  have hpack : DY.SymEnc.symEnc k iv m =
      (({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF Bytes).pack) := rfl
  rw [hpack, ms_pack_sym keepOpkI0 S g ⟨k, iv, m⟩]; rfl

theorem gamma_trHonestWireMsgE (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk : Bytes) (ns pn : UInt32) (ct pq : Bytes) :
    let w := trHonestWireMsg rk ns pn ct pq
    gamma keepOpkI0 S g w =
      trWireBytes (g.addr w) canonicalVariation
        { version := 4, ratchetKey := gamma keepOpkI0 S g rk,
          counter := ns.toNat, previousCounter := pn.toNat,
          ciphertext := gamma keepOpkI0 S g ct }
        (gamma keepOpkI0 S g pq) := by
  intro w
  have hpack : w =
      (({ version := messageVersion, senderRatchetKey := rk, counter := ns,
          previousCounter := pn, ciphertext := ct, pqRatchet := pq,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := rfl
  unfold gamma
  rw [hpack, ms_pack_trWire keepOpkI0 S g ⟨messageVersion, rk, ns, pn, ct, pq, canonicalVariation⟩]
  rfl

def SpqrStateAgree (S : OpaqueSymbolSemantics) (g g' : Ghost) (spqr spqr' : Bytes) : Prop :=
  gamma keepOpkI0 S g spqr = gamma keepOpkI0 S g' spqr' ∧
    ((∃ k k' p, spqr = DY.Spqr.spqrInit k p ∧ spqr' = DY.Spqr.spqrInit k' p ∧
        gamma keepOpkI0 S g k = gamma keepOpkI0 S g' k' ∧
        gamma keepOpkI0 S g p = gamma keepOpkI0 S g' p) ∨
     (spqr.view? DY.Spqr.InitState.SubF = none ∧ spqr'.view? DY.Spqr.InitState.SubF = none))

structure StateBytesAgree (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (st st' : TRState) : Prop where
  myIk_eq : gamma keepOpkI0 S g st.myIk = gamma keepOpkI0 S g' st'.myIk
  peerIk_eq : gamma keepOpkI0 S g st.peerIk = gamma keepOpkI0 S g' st'.peerIk
  rk_eq : gamma keepOpkI0 S g st.rk = gamma keepOpkI0 S g' st'.rk
  cks_eq : gamma keepOpkI0 S g st.cks = gamma keepOpkI0 S g' st'.cks
  dhs_eq : gamma keepOpkI0 S g st.dhs = gamma keepOpkI0 S g' st'.dhs
  spqr_agree : SpqrStateAgree S g g' st.spqr st'.spqr
  ns_eq : st.ns = st'.ns
  pn_eq : st.pn = st'.pn

theorem spqrStateAgree_init {S : OpaqueSymbolSemantics} {g g' : Ghost} {k k' : Bytes} (p : Bytes)
    (hk : gamma keepOpkI0 S g k = gamma keepOpkI0 S g' k')
    (hp : gamma keepOpkI0 S g p = gamma keepOpkI0 S g' p) :
    SpqrStateAgree S g g' (DY.Spqr.spqrInit k p) (DY.Spqr.spqrInit k' p) := by
  refine ⟨?_, Or.inl ⟨k, k', p, rfl, rfl, hk, hp⟩⟩
  rw [gamma_spqrInitE, gamma_spqrInitE, hk, hp]

theorem spqrSend_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {spqr spqr' c c' : Bytes}
    (hsp : SpqrStateAgree S g g' spqr spqr')
    (hc : gamma keepOpkI0 S g c = gamma keepOpkI0 S g' c') :
    SpqrStateAgree S g g' (DY.Spqr.spqrSend spqr c).1 (DY.Spqr.spqrSend spqr' c').1 ∧
    gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr c).2.1 =
      gamma keepOpkI0 S g' (DY.Spqr.spqrSend spqr' c').2.1 ∧
    gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma keepOpkI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
  have hst1 : gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr c).1 =
      gamma keepOpkI0 S g' (DY.Spqr.spqrSend spqr' c').1 := by
    unfold DY.Spqr.spqrSend; rw [gamma_spqrSendStateE, gamma_spqrSendStateE, hsp.1, hc]
  have hmsg : gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma keepOpkI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
    unfold DY.Spqr.spqrSend; rw [gamma_spqrSendMsgE, gamma_spqrSendMsgE, hsp.1, hc]
  have hnone1 : (DY.Spqr.spqrSend spqr c).1.view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr, coins := c } : DY.Spqr.SendState.SubF Bytes)
  have hnone2 : (DY.Spqr.spqrSend spqr' c').1.view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr', coins := c' } : DY.Spqr.SendState.SubF Bytes)
  refine ⟨⟨hst1, Or.inr ⟨hnone1, hnone2⟩⟩, ?_, hmsg⟩
  rcases hsp.2 with ⟨k, k', p, rfl, rfl, hk, hp⟩ | ⟨hn1, hn2⟩
  · unfold DY.Spqr.spqrSend DY.Spqr.spqrInit
    rw [DY.BytesView.view_pack, DY.BytesView.view_pack]; dsimp only
    rw [gamma_spqrChainKey, gamma_spqrChainKey, hk, hp, gamma_spqrIdx, gamma_spqrIdx]
  · unfold DY.Spqr.spqrSend; rw [hn1, hn2]; dsimp only
    rw [gamma_spqrSendKeyE, gamma_spqrSendKeyE, hsp.1, hc]

theorem createChain_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {rk rk' theirPk theirPk' ourSk ourSk' : Bytes}
    (hrk : gamma keepOpkI0 S g rk = gamma keepOpkI0 S g' rk')
    (hpk : gamma keepOpkI0 S g theirPk = gamma keepOpkI0 S g' theirPk')
    (hsk : gamma keepOpkI0 S g ourSk = gamma keepOpkI0 S g' ourSk') :
    gamma keepOpkI0 S g (createChain rk theirPk ourSk).1 =
      gamma keepOpkI0 S g' (createChain rk' theirPk' ourSk').1 ∧
    gamma keepOpkI0 S g (createChain rk theirPk ourSk).2 =
      gamma keepOpkI0 S g' (createChain rk' theirPk' ourSk').2 := by
  have hEq := keepOpkI0_cryptoEquationsHold
  refine ⟨?_, ?_⟩
  · have h1a : (createChain rk theirPk ourSk).1 =
        DY.Libsignal.TripleRatchet.hkdfBlock1
          (DY.Libsignal.TripleRatchet.hmac rk (agree theirPk ourSk))
          (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
    have h1b : (createChain rk' theirPk' ourSk').1 =
        DY.Libsignal.TripleRatchet.hkdfBlock1
          (DY.Libsignal.TripleRatchet.hmac rk' (agree theirPk' ourSk'))
          (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
    rw [h1a, h1b, gamma_hkdfBlock1, gamma_hkdfBlock1, gamma_hmac, gamma_hmac,
        gamma_agree keepOpkI0 hEq, gamma_agree keepOpkI0 hEq,
        gamma_whisperRatchet, gamma_whisperRatchet, hrk, hpk, hsk]
  · rw [gamma_createChain_snd keepOpkI0 hEq, gamma_createChain_snd keepOpkI0 hEq, hrk, hpk, hsk]

theorem stateBytesAgree_aliceStartOpk {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {tr trClean : ExecTrace} {ik_a ik_b_pk spk_pk pq_pk opk_pk dhs_a dhs_clean : Bytes}
    (hikA : gamma keepOpkI0 S g ik_a = gamma keepOpkI0 S g' ikA)
    (hikB : gamma keepOpkI0 S g ik_b_pk = gamma keepOpkI0 S g' (dhPk ikB))
    (hspk : gamma keepOpkI0 S g spk_pk = gamma keepOpkI0 S g' (dhPk spkB))
    (hpq : gamma keepOpkI0 S g pq_pk = gamma keepOpkI0 S g' (DY.PQKem.kemPk pqskB))
    (hopk : gamma keepOpkI0 S g opk_pk = gamma keepOpkI0 S g' (dhPk opkB))
    (hek : gamma keepOpkI0 S g (rnd tr.length 32) = gamma keepOpkI0 S g' (rnd trClean.length 32))
    (he : gamma keepOpkI0 S g (rnd (tr.length + 1) 32) =
          gamma keepOpkI0 S g' (rnd (trClean.length + 1) 32))
    (hdhs : gamma keepOpkI0 S g dhs_a = gamma keepOpkI0 S g' dhs_clean) :
    let o_ss := aliceOutOpk tr ik_a ik_b_pk spk_pk pq_pk opk_pk
    let o_cl := aliceOutOpk trClean ikA (dhPk ikB) (dhPk spkB) (DY.PQKem.kemPk pqskB) (dhPk opkB)
    gamma keepOpkI0 S g o_ss.ek = gamma keepOpkI0 S g' o_cl.ek ∧
    gamma keepOpkI0 S g o_ss.ct = gamma keepOpkI0 S g' o_cl.ct ∧
    StateBytesAgree S g g' (aliceSt "bob" o_ss dhs_a) (aliceSt "bob" o_cl dhs_clean) := by
  intro o_ss o_cl
  have hEq := keepOpkI0_cryptoEquationsHold
  have hek_pk : gamma keepOpkI0 S g o_ss.ek = gamma keepOpkI0 S g' o_cl.ek := by
    show gamma keepOpkI0 S g (dhPk (rnd tr.length 32)) =
      gamma keepOpkI0 S g' (dhPk (rnd trClean.length 32))
    rw [gamma_dhPk, gamma_dhPk, hek]
  have hct_eq : gamma keepOpkI0 S g o_ss.ct = gamma keepOpkI0 S g' o_cl.ct := by
    show gamma keepOpkI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).1 =
      gamma keepOpkI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd (trClean.length + 1) 32)).1
    rw [gamma_kemEncap_fst, gamma_kemEncap_fst, hpq, he]
  have hss_eq : gamma keepOpkI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2 =
      gamma keepOpkI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd (trClean.length + 1) 32)).2 := by
    rw [gamma_kemEncap_snd, gamma_kemEncap_snd, hpq, he]
  have hikm : gamma keepOpkI0 S g
      (pqxdhIkm (agree spk_pk ik_a)
        (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32))
        (some (agree opk_pk (rnd tr.length 32)))
        (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2) =
      gamma keepOpkI0 S g'
      (pqxdhIkm (agree (dhPk spkB) ikA)
        (agree (dhPk ikB) (rnd trClean.length 32)) (agree (dhPk spkB) (rnd trClean.length 32))
        (some (agree (dhPk opkB) (rnd trClean.length 32)))
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd (trClean.length + 1) 32)).2) := by
    rw [gamma_pqxdhIkm, gamma_pqxdhIkm]; dsimp only [Option.map]
    rw [gamma_agree keepOpkI0 hEq, gamma_agree keepOpkI0 hEq,
        gamma_agree keepOpkI0 hEq, gamma_agree keepOpkI0 hEq,
        gamma_agree keepOpkI0 hEq, gamma_agree keepOpkI0 hEq,
        gamma_agree keepOpkI0 hEq, gamma_agree keepOpkI0 hEq,
        hikA, hikB, hspk, hopk, hek, hss_eq]
  have hkdf1 := gamma_pqxdhKdf keepOpkI0 S g
    (pqxdhIkm (agree spk_pk ik_a)
      (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32))
      (some (agree opk_pk (rnd tr.length 32)))
      (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2)
  have hkdf2 := gamma_pqxdhKdf keepOpkI0 S g'
    (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd trClean.length 32)) (agree (dhPk spkB) (rnd trClean.length 32))
      (some (agree (dhPk opkB) (rnd trClean.length 32)))
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd (trClean.length + 1) 32)).2)
  rw [hikm] at hkdf1
  have hrk0 : gamma keepOpkI0 S g o_ss.keys.rk = gamma keepOpkI0 S g' o_cl.keys.rk :=
    hkdf1.1.trans hkdf2.1.symm
  have hpqr0 : gamma keepOpkI0 S g o_ss.keys.pqr = gamma keepOpkI0 S g' o_cl.keys.pqr :=
    hkdf1.2.2.trans hkdf2.2.2.symm
  have hcc := createChain_gamma_congr hrk0 hspk hdhs
  refine ⟨hek_pk, hct_eq, ?_⟩
  refine ⟨?_, ?_, hcc.1, hcc.2, hdhs, ?_, rfl, rfl⟩
  · show gamma keepOpkI0 S g (serializedIk (dhPk ik_a)) =
      gamma keepOpkI0 S g' (serializedIk (dhPk ikA))
    rw [gamma_serializedIk, gamma_serializedIk, gamma_dhPk, gamma_dhPk, hikA]
  · show gamma keepOpkI0 S g (serializedIk ik_b_pk) =
      gamma keepOpkI0 S g' (serializedIk (dhPk ikB))
    rw [gamma_serializedIk, gamma_serializedIk, hikB]
  · refine spqrStateAgree_init spqrA2B hpqr0 ?_
    unfold spqrA2B; rw [gamma_spqrParams_a2b, gamma_spqrParams_a2b]

theorem stateBytesAgree_encrypt {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {st st' : TRState} {coins coins' pt pt' : Bytes}
    (hst : StateBytesAgree S g g' st st')
    (hc : gamma keepOpkI0 S g coins = gamma keepOpkI0 S g' coins')
    (hpt : gamma keepOpkI0 S g pt = gamma keepOpkI0 S g' pt')
    (haddr : g.addr (encSig st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt).wire =
             g'.addr (encSig st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt').wire) :
    StateBytesAgree S g g' (encSt st coins) (encSt st' coins') ∧
    gamma keepOpkI0 S g (encMsg st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt) =
      gamma keepOpkI0 S g' (encMsg st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt') := by
  obtain ⟨hsp1, hpqKey, hpqMsg⟩ := spqrSend_gamma_congr hst.spqr_agree hc
  have hck1 : gamma keepOpkI0 S g (kdfCk st.cks).1 = gamma keepOpkI0 S g' (kdfCk st'.cks).1 := by
    rw [gamma_kdfCk_fst, gamma_kdfCk_fst, hst.cks_eq]
  have hseed : gamma keepOpkI0 S g (kdfCk st.cks).2 = gamma keepOpkI0 S g' (kdfCk st'.cks).2 := by
    rw [gamma_kdfCk_snd, gamma_kdfCk_snd, hst.cks_eq]
  have hstNext : StateBytesAgree S g g' (encSt st coins) (encSt st' coins') :=
    ⟨hst.myIk_eq, hst.peerIk_eq, hst.rk_eq, hck1, hst.dhs_eq, hsp1,
     congrArg (· + 1) hst.ns_eq, hst.pn_eq⟩
  refine ⟨hstNext, ?_⟩
  let pq1 := (DY.Spqr.spqrSend st.spqr coins).2.1
  let pq2 := (DY.Spqr.spqrSend st'.spqr coins').2.1
  have hckey : gamma keepOpkI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey =
      gamma keepOpkI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey := by
    rw [gamma_trMsgKeys_cipherKey, gamma_trMsgKeys_cipherKey, hpqKey, hseed]
  have hiv : gamma keepOpkI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).iv =
      gamma keepOpkI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).iv := by
    rw [gamma_trMsgKeys_iv, gamma_trMsgKeys_iv, hpqKey, hseed]
  have hmkey : gamma keepOpkI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).macKey =
      gamma keepOpkI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).macKey := by
    rw [gamma_trMsgKeys_macKey, gamma_trMsgKeys_macKey, hpqKey, hseed]
  have hct : gamma keepOpkI0 S g
      (DY.SymEnc.symEnc (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey
        (trMsgKeys pq1 (kdfCk st.cks).2).iv pt) =
      gamma keepOpkI0 S g'
      (DY.SymEnc.symEnc (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey
        (trMsgKeys pq2 (kdfCk st'.cks).2).iv pt') := by
    rw [gamma_symEncE, gamma_symEncE, hckey, hiv, hpt]
  have hrk : gamma keepOpkI0 S g (dhPk st.dhs) = gamma keepOpkI0 S g' (dhPk st'.dhs) := by
    rw [gamma_dhPk, gamma_dhPk, hst.dhs_eq]
  have hwire : gamma keepOpkI0 S g (encSig st coins pq1 pt).wire =
      gamma keepOpkI0 S g' (encSig st' coins' pq2 pt').wire := by
    dsimp only [encSig]
    rw [gamma_trHonestWireMsgE, gamma_trHonestWireMsgE]
    change trWireBytes (g.addr (encSig st coins pq1 pt).wire) canonicalVariation _ _ =
      trWireBytes (g'.addr (encSig st' coins' pq2 pt').wire) canonicalVariation _ _
    rw [haddr, hrk, hst.ns_eq, hst.pn_eq, hct, hpqMsg]
  unfold encMsg
  rw [gamma_concat, gamma_concat]
  change gamma keepOpkI0 S g (encSig st coins pq1 pt).wire ++
      gamma keepOpkI0 S g (computeMac (trMsgKeys pq1 (kdfCk st.cks).2).macKey
        st.myIk st.peerIk (encSig st coins pq1 pt).wire) =
    gamma keepOpkI0 S g' (encSig st' coins' pq2 pt').wire ++
      gamma keepOpkI0 S g' (computeMac (trMsgKeys pq2 (kdfCk st'.cks).2).macKey
        st'.myIk st'.peerIk (encSig st' coins' pq2 pt').wire)
  rw [gamma_computeMac, gamma_computeMac, hmkey, hst.myIk_eq, hst.peerIk_eq, hwire]

/-! ## 2. Step Projections, Front-to-Back Peeling of `trace0.take k`, and `clsOfCalls` -/

theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

theorem runSteps_append (xs ys : List Step) (tr : ExecTrace) :
    runSteps (xs ++ ys) tr = runSteps ys (runSteps xs tr) := by
  induction xs generalizing tr with
  | nil => rfl
  | cons s xs ih => exact ih (s.next tr)

theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

theorem preCond_of_stepIn (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : reachability.PreCond (stepIn c x) tr) :
    c.PreCond x tr :=
  (inst.pf_pre x tr).mpr h

theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

/-- One peeled party step `(pre, s, v)` matching `ev j`. -/
structure PeeledCall where
  pre : List Step
  s : Step
  v : List VisEntry

/-- Suffix `trace0[j..k]` written recursively from the front for `peel_evsRange`. -/
def evsRange (j k : Nat) : List CliEvent :=
  if _ : j < k then .run (ev j) :: evsRange (j + 1) k else []
termination_by k - j

theorem evsRange_self (k : Nat) : evsRange k k = [] := by
  unfold evsRange; simp

theorem evsRange_lt {j k : Nat} (h : j < k) :
    evsRange j k = .run (ev j) :: evsRange (j + 1) k := by
  conv => lhs; unfold evsRange
  simp [h]

theorem evsRange_snoc {j k : Nat} (h : j ≤ k) :
    evsRange j (k + 1) = evsRange j k ++ [.run (ev k)] := by
  by_cases hlt : j < k
  · rw [evsRange_lt (by omega), evsRange_lt hlt, List.cons_append, evsRange_snoc hlt]
  · have heq : j = k := by omega
    subst heq
    rw [evsRange_self, List.nil_append, evsRange_lt (by omega), evsRange_self]
termination_by k - j

theorem trace0_take_eq_evsRange : ∀ {k : Nat}, k ≤ 6 → trace0.take k = evsRange 0 k
  | 0, _ => by simp [evsRange_self]
  | k + 1, hk => by
    rw [trace0_take_succ (by omega), trace0_take_eq_evsRange (by omega),
        evsRange_snoc (Nat.zero_le k)]

/-- Inductive validity of a peeled call sequence `cs` for `evsRange j (j + cs.length)`. -/
inductive PeeledValid (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (visAll : List VisEntry) :
    Nat → Option BundlePreKeyIds → ExecTrace → List PeeledCall → List Step → Prop where
  | nil {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {tail : List Step} :
      (∀ x ∈ tail, ∃ msg, x = .network msg) →
      PeeledValid r S g visAll j initIds tr [] tail
  | cons {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {c : PeeledCall} {cs : List PeeledCall} {rest : List Step} :
      (∀ x ∈ c.pre, ∃ msg, x = .network msg) →
      c.s.PreCond (runSteps c.pre tr) →
      c.s.LocalOk (runSteps c.pre tr) →
      RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s (ev j) c.v initIds →
      (∀ w ∈ c.v, w ∈ visAll) →
      PeeledValid r S g visAll (j + 1) (nextBundleIds initIds (ev j))
        (c.s.next (runSteps c.pre tr)) cs rest →
      PeeledValid r S g visAll j initIds tr (c :: cs) (c.pre ++ c.s :: rest)

theorem peel_evsRange {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ (n j : Nat) {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {ss : List Step} {vis : List VisEntry},
      j + n ≤ 6 →
      StepsWF ss tr →
      MatchesEventsAt keepOpkI0 r S g initIds tr ss (evsRange j (j + n)) vis →
      (∀ w ∈ vis, w ∈ visAll) →
      ∃ cs : List PeeledCall, cs.length = n ∧ PeeledValid r S g visAll j initIds tr cs ss
  | 0, j, initIds, tr, ss, vis, _, _, hm, _ => by
    rw [Nat.add_zero, evsRange_self] at hm
    cases hm with
    | nil hinv =>
      exact ⟨[], rfl, .nil (fun x hx => step_invisible_eq_network (hinv x hx))⟩
  | n + 1, j, initIds, tr, ss, vis, hjn, hwf, hm, hsub => by
    have hlt : j < j + (n + 1) := by omega
    rw [evsRange_lt hlt] at hm
    have hj6 : j < 6 := by omega
    cases hm with
    | run0 _ hrej _ => exact False.elim (ev_not_rejected j hj6 hrej)
    | @run1 _ _ pre s ss' _ _ v vs hinv hrm hrest =>
      obtain ⟨hpre, hlok, hwf_tail⟩ := stepsWF_append_right pre hwf
      have hnet : ∀ x ∈ pre, ∃ msg, x = .network msg :=
        fun x hx => step_invisible_eq_network (hinv x hx)
      have hv_sub : ∀ w ∈ v, w ∈ visAll := fun w hw => hsub w (List.mem_append_left _ hw)
      have hvs_sub : ∀ w ∈ vs, w ∈ visAll := fun w hw => hsub w (List.mem_append_right _ hw)
      rw [show j + (n + 1) = (j + 1) + n by omega] at hrest
      obtain ⟨cs, hlen, hpv⟩ := peel_evsRange n (j + 1) (by omega) hwf_tail hrest hvs_sub
      exact ⟨⟨pre, s, v⟩ :: cs, by simp [hlen], .cons hnet hpre hlok hrm hv_sub hpv⟩

/-- Maps send index `0 -> 1` (`ev 1`) and `1 -> 4` (`ev 4`). -/
def sendCallOf : Nat → Nat
  | 0 => 1
  | _ => 4

def stepCoinLen : Step → Nat
  | .messageEncrypt _ _ cl _ => cl
  | _ => 0

def clsOfCalls (cs : List PeeledCall) (s : Nat) : Nat :=
  match cs[sendCallOf s]? with
  | some c => stepCoinLen c.s
  | none => 0

theorem peeledValid_localOk_at {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {cs : List PeeledCall} {ss : List Step},
      PeeledValid r S g visAll j initIds tr cs ss →
      ∀ (i : Nat) (c : PeeledCall), cs[i]? = some c → ∃ tr_i, c.s.LocalOk tr_i
  | _, _, _, _, _, .nil _, _, _, hget => by simp at hget
  | _, _, _, _, _, .cons _ _ hlok _ _ _, 0, _, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget; exact ⟨_, hlok⟩
  | _, _, _, _, _, .cons _ _ _ _ _ hpv, i + 1, c, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact peeledValid_localOk_at hpv i c hget

theorem validCoinLens_clsOfCalls {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {cs : List PeeledCall} {ss : List Step}
    (hpv : PeeledValid r S g visAll j initIds tr cs ss) :
    ValidCoinLens (clsOfCalls cs) := by
  have hAt : ∀ s : Nat, clsOfCalls cs s = 0 ∨ clsOfCalls cs s = 32 ∨ clsOfCalls cs s = 64 := by
    intro s; unfold clsOfCalls
    rcases hget : cs[sendCallOf s]? with _ | c
    · exact Or.inl rfl
    · dsimp only
      obtain ⟨tr_i, hlok⟩ := peeledValid_localOk_at hpv (sendCallOf s) c hget
      cases hs : c.s with
      | messageEncrypt me idx cl pq => rw [hs] at hlok; exact hlok.1
      | _ => exact Or.inl rfl
  exact ⟨hAt 0, hAt 1⟩

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA
