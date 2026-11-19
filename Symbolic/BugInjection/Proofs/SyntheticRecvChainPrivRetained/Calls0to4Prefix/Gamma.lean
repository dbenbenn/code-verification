/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Schedule
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Clean Ghost `gClean`, `StateBytesAgree`, and Concrete Alice Call-4 Keys (`Calls0to4Prefix/Gamma.lean`)

Provides:
1. Canonical clean `Ghost` `gClean r cls` and public `gClean_sigma_*` / `gClean_addr_*` lemmas.
2. `ghostAndSemMatchSetup_gClean`, `gamma_dhPk_ratchetTs`, and `gamma_ratchetKeyTimestamps_inj`.
3. `SpqrStateAgree`, `StateBytesAgree` (including `recvCk_eq`), and step congruence across Calls `0..4`.
4. Reducible 32-byte constants `rcprAliceRk4`, `rcprAliceDhs4`, `rcprAliceCks4`, `rcprAliceCk0`,
   `rcprAliceCk1` and their exact `gamma` evaluations on `stA4Clean cls`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (serializedIk pqxdhKdf pqxdhIkm agree)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg RecvChain kdfCk createChain setRecvChain trMsgKeys computeMac
   trHonestWireMsg spqrA2B spqrB2A messageVersion)
open DY.Libsignal.Refinement (x25519PublicKeySymbol aesCbcEncryptSymbol canonicalVariation)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost
   gamma gamma' concretizeAll concretizeKemPk concretizeSign
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey
   concretizeSpqrSendMsg concretizeSpqrRecvState
   trWireBytes spqrKeyBytes clamp slice randTerm
   setupRandomsAt setupPublic secretBytes GhostAndSemMatchSetup)
open DY.Libsignal.Composed.Refinement.Cli (serializeAddresses aliceUuid bobUuid)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encSig encMsg aliceOut aliceOutOpt aliceSt bobSt0 ratchetState recvSt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (t4 t4_length ikA ikB spkB pqskB dhsA o1 keys1 stA0)
open Symbolic.Swarm.CREF.TR
  (gamma_rand gamma_lit gamma_litByte gamma_concat gamma_hmac gamma_dhPk
   gamma_kemEncap_fst gamma_kemEncap_snd gamma_spqrChainKey gamma_serializedIk
   gamma_trMsgKeys_cipherKey gamma_trMsgKeys_iv gamma_trMsgKeys_macKey gamma_computeMac
   gamma_agree gamma_pqxdhIkm gamma_pqxdhKdf gamma_createChain_snd gamma_kdfCk_fst gamma_kdfCk_snd
   gamma_hkdfBlock1 gamma_hkdfBlock2 gamma_whisperRatchet gamma_spqrParams_a2b gamma_spqrIdx)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound (ms_pack_trWire ms_pack_sym)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprLeakKey1 rcprI0 rcprHooks0 rcprCompFitsPinned
   rcprSecretIdx rcprPubOfIdx rcprLookupPub rcprPubOfOpt rcprLookupDh rcprDhByIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
  (rcprI0_publicKey rcprI0_agreement rcprI0_kyberEncaps rcprI0_cryptoEquationsHold
   rcprPubOfOpt_not_lowOrder rcprPointIdx_rcprPubOfOpt)

attribute [local irreducible] ev

/-! ## 1. Clean Ghost `gClean` and Public Lookup Equations -/

/-- Serialized `(alice, bob)` protocol address pair on `PreKeySignalMessage` sends. -/
abbrev pqAddrBytes : HwBytes :=
  serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩

/-- Canonical clean `Ghost` aligned with the compact timestamps of `ssClean cls`. -/
def gClean (r : ProtocolSetup) (cls : Nat → Nat) : Ghost where
  σ ts n :=
    if ts < 22 then r.fresh ts n
    else if ts = 22 then slice (ev 0).coins 0 32
    else if ts = 23 then ev0KyberEnt
    else if ts = 24 then slice (ev 0).coins 160 32
    else if ts = 31 then (ev 1).input
    else if ts = 32 then (ev 1).coins.take n
    else if ts = 38 then (ev 2).coins.take 32
    else if ts = 47 then (ev 3).input
    else if ts = 48 then (ev 3).coins.take n
    else if ts = 54 then (ev 4).coins.take 32
    else r.fresh ts n
  addr t :=
    if t == (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).wire then
      pqAddrBytes
    else []

theorem gClean_sigma_lt22 (r : ProtocolSetup) (cls : Nat → Nat) {ts n : Nat} (h : ts < 22) :
    (gClean r cls).σ ts n = r.fresh ts n := by simp [gClean, h]
theorem gClean_sigma_22 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 22 n = slice (ev 0).coins 0 32 := rfl
theorem gClean_sigma_23 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 23 n = ev0KyberEnt := rfl
theorem gClean_sigma_24 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 24 n = slice (ev 0).coins 160 32 := rfl
theorem gClean_sigma_31 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 31 n = (ev 1).input := rfl
theorem gClean_sigma_32 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 32 n = (ev 1).coins.take n := rfl
theorem gClean_sigma_38 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 38 n = (ev 2).coins.take 32 := rfl
theorem gClean_sigma_47 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 47 n = (ev 3).input := rfl
theorem gClean_sigma_48 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 48 n = (ev 3).coins.take n := rfl
theorem gClean_sigma_54 (r : ProtocolSetup) (cls : Nat → Nat) (n : Nat) : (gClean r cls).σ 54 n = (ev 4).coins.take 32 := rfl

theorem trHonestWireMsg_rk_inj {rk1 rk2 ct1 ct2 pq1 pq2 : Bytes} {ns1 pn1 ns2 pn2 : UInt32}
    (h : trHonestWireMsg rk1 ns1 pn1 ct1 pq1 = trHonestWireMsg rk2 ns2 pn2 ct2 pq2) :
    rk1 = rk2 := by
  have hpack :
      (({ version := messageVersion, senderRatchetKey := rk1, counter := ns1,
          previousCounter := pn1, ciphertext := ct1, pqRatchet := pq1,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) =
      (({ version := messageVersion, senderRatchetKey := rk2, counter := ns2,
          previousCounter := pn2, ciphertext := ct2, pqRatchet := pq2,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := h
  exact congrArg DY.TrWire.TrWireMsg.SubF.senderRatchetKey
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp hpack)

theorem dhPk_rnd_inj {ts1 ts2 n1 n2 : Nat}
    (h : dhPk (rnd ts1 n1) = dhPk (rnd ts2 n2)) : ts1 = ts2 := by
  have hsk := congrArg DY.DiffieHellman.DhPk.SubF.sk
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp
      (h : (({ sk := rnd ts1 n1 } : DY.DiffieHellman.DhPk.SubF Bytes).pack) =
           (({ sk := rnd ts2 n2 } : DY.DiffieHellman.DhPk.SubF Bytes).pack)))
  exact congrArg DY.Random.Random.timestamp
    (Symbolic.DYBridge.DY.BytesView.pack_inj.mp
      (hsk : (({ timestamp := ts1, size := n1 } : DY.Random.Random Bytes).pack) =
             (({ timestamp := ts2, size := n2 } : DY.Random.Random Bytes).pack)))

theorem gClean_addr_m0 (r : ProtocolSetup) (cls : Nat → Nat) :
    (gClean r cls).addr (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).wire =
      pqAddrBytes := by unfold gClean; simp

theorem gClean_addr_whisper (r : ProtocolSetup) (cls : Nat → Nat)
    {stSend : TRState} {coins pqKey pt : Bytes} {tsSend : Nat}
    (hdhs : stSend.dhs = rnd tsSend 32) (hne : tsSend ≠ 24) :
    (gClean r cls).addr (encSig stSend coins pqKey pt).wire = [] := by
  have hne1 : (encSig stSend coins pqKey pt).wire ≠
      (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).wire := fun heq => by
    have hrk := trHonestWireMsg_rk_inj heq; rw [hdhs] at hrk; exact hne (dhPk_rnd_inj hrk)
  unfold gClean; simp [hne1]

theorem gClean_addr_m1 (r : ProtocolSetup) (cls : Nat → Nat) :
    (gClean r cls).addr (encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean).wire =
      [] := gClean_addr_whisper r cls rfl (by decide)

/-! ## 2. `GhostAndSemMatchSetup` Transfer and Honest Ratchet Public Key Lemmas -/

theorem gamma_KemPk (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk : Bytes) :
    gamma i S g (DY.PQKem.kemPk sk) = S.kemPk (gamma i S g sk) := by
  unfold gamma gamma'
  show ((({ sk } : DY.PQKem.Pk.SubF Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g)]; rfl

theorem gamma_Sign (i : CryptoProofLib.Refinement.ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (sk n m : Bytes) :
    gamma i S g (DY.Signature.sign sk n m) =
      S.sign (gamma i S g sk) (gamma i S g n) (gamma i S g m) := by
  unfold gamma gamma'
  show ((({ sk, nonce := n, msg := m } : DY.Signature.Sign.SubF Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]; rfl

theorem setupRandomsAt_of_fit {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  have hnames := r_names_of_fit hfit
  have h := Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r (by rw [hnames.1, hnames.2]; decide)
  rw [hfit.1.1.2.1] at h; simpa using h

theorem ghostAndSemMatchSetup_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g) :
    GhostAndSemMatchSetup rcprI0 r S (gClean r cls) := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  have hrandAt := setupRandomsAt_of_fit hfit
  have hc1 : ∀ p ∈ setupRandomsAt r, (gClean r cls).σ p.1 p.2 = r.fresh p.1 p.2 := by
    rw [hrandAt]; intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact gClean_sigma_lt22 r cls (by decide)
  have hsig_eq : ∀ ts n, (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] →
      n ≠ 0 → gamma rcprI0 S (gClean r cls) (randTerm ts n) = gamma rcprI0 S g (randTerm ts n) := by
    intro ts n hmem hn; have hmem' : (ts, n) ∈ setupRandomsAt r := hrandAt ▸ hmem
    unfold randTerm; rw [gamma_rand, gamma_rand]; simp only [hn, ↓reduceIte]
    exact (hc1 (ts, n) hmem').trans (hCompat.1 (ts, n) hmem').symm
  refine ⟨hc1, ?_, hCompat.2.2⟩
  intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [← hCompat.2.1 r.spkSigTerm (by simp)]
    dsimp only [ProtocolSetup.spkSigTerm]
    rw [Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]
    unfold DY.Libsignal.PQXDH.encodeEC
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_dhPk, gamma_dhPk, hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 11 64 (by decide) (by decide), hsig_eq 10 32 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkPubTerm (by simp)]
    dsimp only [ProtocolSetup.pqpkPubTerm]
    rw [Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe,
        gamma_KemPk, gamma_KemPk, hsig_eq 16 64 (by decide) (by decide)]
  · rw [← hCompat.2.1 r.pqpkSigTerm (by simp)]
    dsimp only [ProtocolSetup.pqpkSigTerm]
    rw [Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]
    unfold DY.Libsignal.PQXDH.encodeKEM
    rw [gamma_Sign, gamma_Sign, gamma_concat, gamma_concat, gamma_litByte, gamma_litByte,
        gamma_KemPk, gamma_KemPk, hsig_eq 5 32 (by decide) (by decide),
        hsig_eq 17 64 (by decide) (by decide), hsig_eq 16 64 (by decide) (by decide)]

theorem gamma_setup_rnd_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (cls : Nat → Nat) (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    {ts n : Nat} (hmem : (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)])
    (hn : n ≠ 0) :
    gamma rcprI0 S g (rnd ts n) = gamma rcprI0 S (gClean r cls) (rnd ts n) := by
  have hmem' : (ts, n) ∈ setupRandomsAt r := (setupRandomsAt_of_fit hfit) ▸ hmem
  unfold rnd; rw [gamma_rand, gamma_rand]; simp only [hn, ↓reduceIte]
  exact (hCompat.1 (ts, n) hmem').trans (gClean_sigma_lt22 r cls (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h <;> cases h <;> decide)).symm

theorem gamma_kemPk_pqskB_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g) :
    gamma rcprI0 S (gClean r cls) (DY.PQKem.kemPk pqskB) = rcprSetup.kyberPk := by
  have hNe : r.alice ≠ r.bob := by rw [hfit.1.2.2.2.1.1, hfit.1.2.2.2.1.2]; decide
  have hCg := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have h6 : gamma rcprI0 S (gClean r cls) (setupPublic r 6) = rcprSetup.kyberPk := by
    have h6' := hCg.2.1 r.pqpkPubTerm (by simp)
    dsimp only [ProtocolSetup.pqpkPubTerm] at h6'
    exact h6'.trans hfit.1.1.2.2.2.2.2.2.2.2.2.2.1
  rwa [Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe] at h6

/-- Exact `Fin 7` secret index of each timestamp in `ratchetKeyTimestamps` (`[10, 24, 38, 54]`). -/
def ratchetTsSecretIdx : Nat → Fin 7
  | 10 => ⟨2, by decide⟩
  | 24 => ⟨4, by decide⟩
  | 38 => ⟨5, by decide⟩
  | _ => ⟨6, by decide⟩

private theorem spkSec_idx : rcprSecretIdx (clamp rcprSetup.spk) = some ⟨2, by decide⟩ := by
  decide +kernel

theorem gamma_dhPk_ratchetTs {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {ts : Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hts : ts ∈ ratchetKeyTimestamps) :
    gamma rcprI0 S (gClean r cls) (dhPk (rnd ts 32)) =
      rcprPubOfIdx (ratchetTsSecretIdx ts) := by
  have hsecIdx : rcprSecretIdx (clamp ((gClean r cls).σ ts 32)) =
      some (ratchetTsSecretIdx ts) := by
    simp only [ratchetKeyTimestamps, List.mem_cons, List.not_mem_nil, or_false] at hts
    rcases hts with rfl | rfl | rfl | rfl
    · rw [gClean_sigma_lt22 r cls (by decide)]
      have hsec2 : secretBytes r 2 = r.fresh 10 32 := by
        unfold secretBytes; rw [setupRandomsAt_of_fit hfit]; rfl
      rw [← hsec2, hfit.1.1.2.2.2.2.2.2.2.2.1]
      exact spkSec_idx
    · rw [gClean_sigma_24]; exact ev0_coins_facts.2.2.1
    · rw [gClean_sigma_38]; exact ev2_coins_idx
    · rw [gClean_sigma_54]; exact ev4_coins_idx
  unfold rnd
  rw [gamma_dhPk, gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, rcprI0_publicKey]
  unfold rcprLookupPub rcprPubOfOpt
  rw [hsecIdx]; rfl

theorem gamma_dhPk_spkB {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    gamma rcprI0 S (gClean r cls) (dhPk spkB) = rcprPubOfIdx ⟨2, by decide⟩ :=
  gamma_dhPk_ratchetTs hfit (by decide)

theorem gamma_dhPk_ek (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat) :
    gamma rcprI0 S (gClean r cls) (dhPk (rnd 22 32)) = rcprPubOfIdx ⟨3, by decide⟩ := by
  unfold rnd
  rw [gamma_dhPk, gamma_rand]
  simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, rcprI0_publicKey, gClean_sigma_22]
  unfold rcprLookupPub rcprPubOfOpt
  rw [ev0_coins_facts.2.1]; rfl

theorem gamma_dhPk_dhsA {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    gamma rcprI0 S (gClean r cls) (dhPk dhsA) = rcprPubOfIdx ⟨4, by decide⟩ :=
  gamma_dhPk_ratchetTs (ts := 24) hfit (by decide)

theorem gamma_dhPk_dhsB1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    gamma rcprI0 S (gClean r cls) (dhPk dhsB1Clean) = rcprPubOfIdx ⟨5, by decide⟩ :=
  gamma_dhPk_ratchetTs hfit (by decide)

theorem gamma_dhPk_dhsA1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    gamma rcprI0 S (gClean r cls) (dhPk dhsA1Clean) = rcprPubOfIdx ⟨6, by decide⟩ :=
  gamma_dhPk_ratchetTs hfit (by decide)

theorem gamma_ratchetKeyTimestamps_inj {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat} {ts₁ ts₂ : Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (h1 : ts₁ ∈ ratchetKeyTimestamps) (h2 : ts₂ ∈ ratchetKeyTimestamps)
    (heq : gamma rcprI0 S (gClean r cls) (dhPk (rnd ts₁ 32)) =
           gamma rcprI0 S (gClean r cls) (dhPk (rnd ts₂ 32))) :
    ts₁ = ts₂ := by
  rw [gamma_dhPk_ratchetTs hfit h1, gamma_dhPk_ratchetTs hfit h2] at heq
  have hidx := rcprPubOfIdx_inj heq
  simp only [ratchetKeyTimestamps, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl <;>
    first | rfl | (simp [ratchetTsSecretIdx] at hidx)

/-! ## 3. Low-Level `gamma` Unfoldings, `SpqrStateAgree`, and `StateBytesAgree` -/

theorem gamma_spqrInitE (S : OpaqueSymbolSemantics) (g : Ghost) (a p : Bytes) :
    gamma rcprI0 S g (DY.Spqr.spqrInit a p) =
      S.init (gamma rcprI0 S g a) (gamma rcprI0 S g p) := by
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll rcprI0 S g)]; rfl

theorem gamma_spqrSendStateE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma rcprI0 S g (({ st, coins := c } : DY.Spqr.SendState.SubF Bytes).pack) =
      S.sendState (gamma rcprI0 S g st) (gamma rcprI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll rcprI0 S g)]; rfl

theorem gamma_spqrSendKeyE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma rcprI0 S g (({ st, coins := c } : DY.Spqr.SendKey.SubF Bytes).pack) =
      spqrKeyBytes (S.sendKey (gamma rcprI0 S g st) (gamma rcprI0 S g c)) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll rcprI0 S g)]; rfl

theorem gamma_spqrSendMsgE (S : OpaqueSymbolSemantics) (g : Ghost) (st c : Bytes) :
    gamma rcprI0 S g (({ st, coins := c } : DY.Spqr.SendMsg.SubF Bytes).pack) =
      S.sendMsg (gamma rcprI0 S g st) (gamma rcprI0 S g c) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll rcprI0 S g)]; rfl

theorem gamma_spqrRecvStateE (S : OpaqueSymbolSemantics) (g : Ghost) (st m : Bytes) :
    gamma rcprI0 S g (({ st, msg := m } : DY.Spqr.RecvState.SubF Bytes).pack) =
      S.recvState (gamma rcprI0 S g st) (gamma rcprI0 S g m) := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll rcprI0 S g)]; rfl

theorem gamma_symEncE (S : OpaqueSymbolSemantics) (g : Ghost) (k iv m : Bytes) :
    gamma rcprI0 S g (DY.SymEnc.symEnc k iv m) =
      (rcprI0 aesCbcEncryptSymbol
        [gamma rcprI0 S g m, gamma rcprI0 S g k, (gamma rcprI0 S g iv).take 16]).getD [] := by
  unfold gamma
  have hpack : DY.SymEnc.symEnc k iv m =
      (({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF Bytes).pack) := rfl
  rw [hpack, ms_pack_sym rcprI0 S g ⟨k, iv, m⟩]; rfl

theorem gamma_trHonestWireMsgE (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk : Bytes) (ns pn : UInt32) (ct pq : Bytes) :
    let w := trHonestWireMsg rk ns pn ct pq
    gamma rcprI0 S g w =
      trWireBytes (g.addr w) canonicalVariation
        { version := 4, ratchetKey := gamma rcprI0 S g rk,
          counter := ns.toNat, previousCounter := pn.toNat,
          ciphertext := gamma rcprI0 S g ct }
        (gamma rcprI0 S g pq) := by
  intro w
  have hpack : w =
      (({ version := messageVersion, senderRatchetKey := rk, counter := ns,
          previousCounter := pn, ciphertext := ct, pqRatchet := pq,
          encodingVariation := canonicalVariation } : DY.TrWire.TrWireMsg.SubF Bytes).pack) := rfl
  unfold gamma
  rw [hpack, ms_pack_trWire rcprI0 S g ⟨messageVersion, rk, ns, pn, ct, pq, canonicalVariation⟩]
  rfl

/-- Agreement between `st.spqr` (under `g`) and `st'.spqr` (under `g'`). -/
def SpqrStateAgree (S : OpaqueSymbolSemantics) (g g' : Ghost) (spqr spqr' : Bytes) : Prop :=
  gamma rcprI0 S g spqr = gamma rcprI0 S g' spqr' ∧
    ((∃ k k' p, spqr = DY.Spqr.spqrInit k p ∧ spqr' = DY.Spqr.spqrInit k' p ∧
        gamma rcprI0 S g k = gamma rcprI0 S g' k' ∧
        gamma rcprI0 S g p = gamma rcprI0 S g' p) ∨
     (spqr.view? DY.Spqr.InitState.SubF = none ∧ spqr'.view? DY.Spqr.InitState.SubF = none))

/-- Concrete byte-level agreement between an outer `ss` `TRState` (under `g`) and the corresponding
clean `ssClean` `TRState` (under `g'`), including receiver-chain `ratchetKey` and `chainKey` lists. -/
structure StateBytesAgree (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (st st' : TRState) : Prop where
  myIk_eq : gamma rcprI0 S g st.myIk = gamma rcprI0 S g' st'.myIk
  peerIk_eq : gamma rcprI0 S g st.peerIk = gamma rcprI0 S g' st'.peerIk
  rk_eq : gamma rcprI0 S g st.rk = gamma rcprI0 S g' st'.rk
  cks_eq : gamma rcprI0 S g st.cks = gamma rcprI0 S g' st'.cks
  dhs_eq : gamma rcprI0 S g st.dhs = gamma rcprI0 S g' st'.dhs
  spqr_agree : SpqrStateAgree S g g' st.spqr st'.spqr
  ns_eq : st.ns = st'.ns
  pn_eq : st.pn = st'.pn
  recvRk_eq : st.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) =
              st'.recv.map (fun c => gamma rcprI0 S g' c.ratchetKey)
  recvCk_eq : st.recv.map (fun c => gamma rcprI0 S g c.chainKey) =
              st'.recv.map (fun c => gamma rcprI0 S g' c.chainKey)

theorem spqrStateAgree_init {S : OpaqueSymbolSemantics} {g g' : Ghost} {k k' : Bytes} (p : Bytes)
    (hk : gamma rcprI0 S g k = gamma rcprI0 S g' k')
    (hp : gamma rcprI0 S g p = gamma rcprI0 S g' p) :
    SpqrStateAgree S g g' (DY.Spqr.spqrInit k p) (DY.Spqr.spqrInit k' p) := by
  refine ⟨?_, Or.inl ⟨k, k', p, rfl, rfl, hk, hp⟩⟩
  rw [gamma_spqrInitE, gamma_spqrInitE, hk, hp]

theorem spqrSend_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {spqr spqr' c c' : Bytes}
    (hsp : SpqrStateAgree S g g' spqr spqr')
    (hc : gamma rcprI0 S g c = gamma rcprI0 S g' c') :
    SpqrStateAgree S g g' (DY.Spqr.spqrSend spqr c).1 (DY.Spqr.spqrSend spqr' c').1 ∧
    gamma rcprI0 S g (DY.Spqr.spqrSend spqr c).2.1 =
      gamma rcprI0 S g' (DY.Spqr.spqrSend spqr' c').2.1 ∧
    gamma rcprI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma rcprI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
  have hst1 : gamma rcprI0 S g (DY.Spqr.spqrSend spqr c).1 =
      gamma rcprI0 S g' (DY.Spqr.spqrSend spqr' c').1 := by
    unfold DY.Spqr.spqrSend
    rw [gamma_spqrSendStateE, gamma_spqrSendStateE, hsp.1, hc]
  have hmsg : gamma rcprI0 S g (DY.Spqr.spqrSend spqr c).2.2 =
      gamma rcprI0 S g' (DY.Spqr.spqrSend spqr' c').2.2 := by
    unfold DY.Spqr.spqrSend
    rw [gamma_spqrSendMsgE, gamma_spqrSendMsgE, hsp.1, hc]
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

theorem spqrRecv_gamma_congr {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {spqr spqr' msg msg' spqrOut key spqrOut' key' : Bytes} {idx idx' : UInt32}
    (hsp : SpqrStateAgree S g g' spqr spqr')
    (hmsg : gamma rcprI0 S g msg = gamma rcprI0 S g' msg')
    (hr1 : DY.Spqr.spqrRecv spqr msg idx = some (spqrOut, key))
    (hr2 : DY.Spqr.spqrRecv spqr' msg' idx' = some (spqrOut', key')) :
    SpqrStateAgree S g g' spqrOut spqrOut' := by
  have hout1 : spqrOut = ({ st := spqr, msg } : DY.Spqr.RecvState.SubF Bytes).pack := by
    unfold DY.Spqr.spqrRecv at hr1; split at hr1
    · cases hr1
    · dsimp only at hr1; split at hr1
      · split at hr1
        · injection hr1 with hp; exact (congrArg Prod.fst hp).symm
        · cases hr1
      · injection hr1 with hp; exact (congrArg Prod.fst hp).symm
  have hout2 : spqrOut' = ({ st := spqr', msg := msg' } : DY.Spqr.RecvState.SubF Bytes).pack := by
    unfold DY.Spqr.spqrRecv at hr2; split at hr2
    · cases hr2
    · dsimp only at hr2; split at hr2
      · split at hr2
        · injection hr2 with hp; exact (congrArg Prod.fst hp).symm
        · cases hr2
      · injection hr2 with hp; exact (congrArg Prod.fst hp).symm
  subst hout1; subst hout2
  refine ⟨?_, Or.inr ⟨
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr, msg } : DY.Spqr.RecvState.SubF Bytes),
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := spqr', msg := msg' } : DY.Spqr.RecvState.SubF Bytes)⟩⟩
  rw [gamma_spqrRecvStateE, gamma_spqrRecvStateE, hsp.1, hmsg]

theorem createChain_gamma_congr {S₁ S₂ : OpaqueSymbolSemantics} {g g' : Ghost}
    {rk rk' theirPk theirPk' ourSk ourSk' : Bytes}
    (hrk : gamma rcprI0 S₁ g rk = gamma rcprI0 S₂ g' rk')
    (hpk : gamma rcprI0 S₁ g theirPk = gamma rcprI0 S₂ g' theirPk')
    (hsk : gamma rcprI0 S₁ g ourSk = gamma rcprI0 S₂ g' ourSk') :
    gamma rcprI0 S₁ g (createChain rk theirPk ourSk).1 =
      gamma rcprI0 S₂ g' (createChain rk' theirPk' ourSk').1 ∧
    gamma rcprI0 S₁ g (createChain rk theirPk ourSk).2 =
      gamma rcprI0 S₂ g' (createChain rk' theirPk' ourSk').2 := by
  have hEq := rcprI0_cryptoEquationsHold
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
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        gamma_whisperRatchet, gamma_whisperRatchet, hrk, hpk, hsk]
  · rw [gamma_createChain_snd rcprI0 hEq, gamma_createChain_snd rcprI0 hEq, hrk, hpk, hsk]

/-! ## 4. Step Transitions (`aliceStart`, `messageEncrypt`, `bobStart`, `messageDecrypt`) -/

theorem o1_ek_eq : o1.ek = dhPk (rnd 22 32) := by
  dsimp only [o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
  rw [t4_length]; rfl

theorem gamma_dhPk_o1_ek (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (cls : Nat → Nat) :
    gamma rcprI0 S (gClean r cls) o1.ek = rcprPubOfIdx ⟨3, by decide⟩ := by
  rw [o1_ek_eq]; exact gamma_dhPk_ek r S cls

theorem o1_ct_eq : o1.ct = (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).1 := by
  dsimp only [o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
    DY.Libsignal.PQXDH.aliceAgreement]
  rw [t4_length]; rfl

theorem keys1_eq :
    keys1 = pqxdhKdf (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
  dsimp only [keys1, o1, aliceOut, aliceOutOpt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
    DY.Libsignal.PQXDH.aliceAgreement]
  rw [t4_length]; rfl

theorem stateBytesAgree_aliceStart {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {tr : ExecTrace} {ik_a ik_b_pk spk_pk pq_pk dhs_a : Bytes}
    (hikA : gamma rcprI0 S g ik_a = gamma rcprI0 S g' ikA)
    (hikB : gamma rcprI0 S g ik_b_pk = gamma rcprI0 S g' (dhPk ikB))
    (hspk : gamma rcprI0 S g spk_pk = gamma rcprI0 S g' (dhPk spkB))
    (hpq : gamma rcprI0 S g pq_pk = gamma rcprI0 S g' (DY.PQKem.kemPk pqskB))
    (hek : gamma rcprI0 S g (rnd tr.length 32) = gamma rcprI0 S g' (rnd 22 32))
    (he : gamma rcprI0 S g (rnd (tr.length + 1) 32) = gamma rcprI0 S g' (rnd 23 32))
    (hdhs : gamma rcprI0 S g dhs_a = gamma rcprI0 S g' dhsA) :
    let o_ss := aliceOut tr ik_a ik_b_pk spk_pk pq_pk
    gamma rcprI0 S g o_ss.ek = gamma rcprI0 S g' o1.ek ∧
    gamma rcprI0 S g o_ss.ct = gamma rcprI0 S g' o1.ct ∧
    StateBytesAgree S g g' (aliceSt "bob" o_ss dhs_a) stA0 := by
  intro o_ss
  have hEq := rcprI0_cryptoEquationsHold
  have hek_pk : gamma rcprI0 S g o_ss.ek = gamma rcprI0 S g' o1.ek := by
    rw [o1_ek_eq]
    show gamma rcprI0 S g (dhPk (rnd tr.length 32)) = gamma rcprI0 S g' (dhPk (rnd 22 32))
    rw [gamma_dhPk, gamma_dhPk, hek]
  have hct_eq : gamma rcprI0 S g o_ss.ct = gamma rcprI0 S g' o1.ct := by
    rw [o1_ct_eq]
    show gamma rcprI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).1 =
      gamma rcprI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).1
    rw [gamma_kemEncap_fst, gamma_kemEncap_fst, hpq, he]
  have hss_eq : gamma rcprI0 S g (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2 =
      gamma rcprI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 := by
    rw [gamma_kemEncap_snd, gamma_kemEncap_snd, hpq, he]
  have hikm : gamma rcprI0 S g
      (pqxdhIkm (agree spk_pk ik_a)
        (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32)) none
        (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2) =
      gamma rcprI0 S g'
      (pqxdhIkm (agree (dhPk spkB) ikA)
        (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
    rw [gamma_pqxdhIkm, gamma_pqxdhIkm,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        hikA, hikB, hspk, hek, hss_eq]; rfl
  have hkdf1 := gamma_pqxdhKdf rcprI0 S g
    (pqxdhIkm (agree spk_pk ik_a)
      (agree ik_b_pk (rnd tr.length 32)) (agree spk_pk (rnd tr.length 32)) none
      (DY.PQKem.kemEncap pq_pk (rnd (tr.length + 1) 32)).2)
  have hkdf2 := gamma_pqxdhKdf rcprI0 S g'
    (pqxdhIkm (agree (dhPk spkB) ikA)
      (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
  rw [hikm] at hkdf1
  have hrk0 : gamma rcprI0 S g o_ss.keys.rk = gamma rcprI0 S g' keys1.rk := by
    rw [keys1_eq]; exact hkdf1.1.trans hkdf2.1.symm
  have hck0 : gamma rcprI0 S g o_ss.keys.ck = gamma rcprI0 S g' keys1.ck := by
    rw [keys1_eq]; exact hkdf1.2.1.trans hkdf2.2.1.symm
  have hpqr0 : gamma rcprI0 S g o_ss.keys.pqr = gamma rcprI0 S g' keys1.pqr := by
    rw [keys1_eq]; exact hkdf1.2.2.trans hkdf2.2.2.symm
  have hcc := createChain_gamma_congr hrk0 hspk hdhs
  refine ⟨hek_pk, hct_eq, ?_, ?_, hcc.1, hcc.2, hdhs, ?_, rfl, rfl, ?_, ?_⟩
  · show gamma rcprI0 S g (serializedIk (dhPk ik_a)) = gamma rcprI0 S g' (serializedIk (dhPk ikA))
    rw [gamma_serializedIk, gamma_serializedIk, gamma_dhPk, gamma_dhPk, hikA]
  · show gamma rcprI0 S g (serializedIk ik_b_pk) = gamma rcprI0 S g' (serializedIk (dhPk ikB))
    rw [gamma_serializedIk, gamma_serializedIk, hikB]
  · refine spqrStateAgree_init spqrA2B hpqr0 ?_
    unfold spqrA2B; rw [gamma_spqrParams_a2b, gamma_spqrParams_a2b]
  · dsimp only [aliceSt, stA0]; exact congrArg (· :: []) hspk
  · dsimp only [aliceSt, stA0]; exact congrArg (· :: []) hck0

theorem stateBytesAgree_encrypt {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {st st' : TRState} {coins coins' pt pt' : Bytes}
    (hst : StateBytesAgree S g g' st st')
    (hc : gamma rcprI0 S g coins = gamma rcprI0 S g' coins')
    (hpt : gamma rcprI0 S g pt = gamma rcprI0 S g' pt')
    (haddr : g.addr (encSig st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt).wire =
             g'.addr (encSig st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt').wire) :
    StateBytesAgree S g g' (encSt st coins) (encSt st' coins') ∧
    gamma rcprI0 S g (encMsg st coins (DY.Spqr.spqrSend st.spqr coins).2.1 pt) =
      gamma rcprI0 S g' (encMsg st' coins' (DY.Spqr.spqrSend st'.spqr coins').2.1 pt') := by
  obtain ⟨hsp1, hpqKey, hpqMsg⟩ := spqrSend_gamma_congr hst.spqr_agree hc
  have hck1 : gamma rcprI0 S g (kdfCk st.cks).1 = gamma rcprI0 S g' (kdfCk st'.cks).1 := by
    rw [gamma_kdfCk_fst, gamma_kdfCk_fst, hst.cks_eq]
  have hseed : gamma rcprI0 S g (kdfCk st.cks).2 = gamma rcprI0 S g' (kdfCk st'.cks).2 := by
    rw [gamma_kdfCk_snd, gamma_kdfCk_snd, hst.cks_eq]
  have hstNext : StateBytesAgree S g g' (encSt st coins) (encSt st' coins') :=
    ⟨hst.myIk_eq, hst.peerIk_eq, hst.rk_eq, hck1, hst.dhs_eq, hsp1,
     congrArg (· + 1) hst.ns_eq, hst.pn_eq, hst.recvRk_eq, hst.recvCk_eq⟩
  refine ⟨hstNext, ?_⟩
  let pq1 := (DY.Spqr.spqrSend st.spqr coins).2.1
  let pq2 := (DY.Spqr.spqrSend st'.spqr coins').2.1
  have hckey : gamma rcprI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey =
      gamma rcprI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey := by
    rw [gamma_trMsgKeys_cipherKey, gamma_trMsgKeys_cipherKey, hpqKey, hseed]
  have hiv : gamma rcprI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).iv =
      gamma rcprI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).iv := by
    rw [gamma_trMsgKeys_iv, gamma_trMsgKeys_iv, hpqKey, hseed]
  have hmkey : gamma rcprI0 S g (trMsgKeys pq1 (kdfCk st.cks).2).macKey =
      gamma rcprI0 S g' (trMsgKeys pq2 (kdfCk st'.cks).2).macKey := by
    rw [gamma_trMsgKeys_macKey, gamma_trMsgKeys_macKey, hpqKey, hseed]
  have hct : gamma rcprI0 S g
      (DY.SymEnc.symEnc (trMsgKeys pq1 (kdfCk st.cks).2).cipherKey
        (trMsgKeys pq1 (kdfCk st.cks).2).iv pt) =
      gamma rcprI0 S g'
      (DY.SymEnc.symEnc (trMsgKeys pq2 (kdfCk st'.cks).2).cipherKey
        (trMsgKeys pq2 (kdfCk st'.cks).2).iv pt') := by
    rw [gamma_symEncE, gamma_symEncE, hckey, hiv, hpt]
  have hrk : gamma rcprI0 S g (dhPk st.dhs) = gamma rcprI0 S g' (dhPk st'.dhs) := by
    rw [gamma_dhPk, gamma_dhPk, hst.dhs_eq]
  have hwire : gamma rcprI0 S g (encSig st coins pq1 pt).wire =
      gamma rcprI0 S g' (encSig st' coins' pq2 pt').wire := by
    dsimp only [encSig]
    rw [gamma_trHonestWireMsgE, gamma_trHonestWireMsgE]
    change trWireBytes (g.addr (encSig st coins pq1 pt).wire) canonicalVariation _ _ =
      trWireBytes (g'.addr (encSig st' coins' pq2 pt').wire) canonicalVariation _ _
    rw [haddr, hrk, hst.ns_eq, hst.pn_eq, hct, hpqMsg]
  unfold encMsg
  rw [gamma_concat, gamma_concat]
  change gamma rcprI0 S g (encSig st coins pq1 pt).wire ++
      gamma rcprI0 S g (computeMac (trMsgKeys pq1 (kdfCk st.cks).2).macKey
        st.myIk st.peerIk (encSig st coins pq1 pt).wire) =
    gamma rcprI0 S g' (encSig st' coins' pq2 pt').wire ++
      gamma rcprI0 S g' (computeMac (trMsgKeys pq2 (kdfCk st'.cks).2).macKey
        st'.myIk st'.peerIk (encSig st' coins' pq2 pt').wire)
  rw [gamma_computeMac, gamma_computeMac, hmkey, hst.myIk_eq, hst.peerIk_eq, hwire]

theorem stateBytesAgree_bobStart {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {cls : Nat → Nat}
    {ik_b spk_b ik_a_pk ek_w ss_kem dhs_b pq_msg spqrOut key : Bytes}
    {msg_b : TRSignalMsg} {c' : RecvChain} {idx : UInt32}
    (hikB : gamma rcprI0 S g ik_b = gamma rcprI0 S g' ikB)
    (hspkB : gamma rcprI0 S g spk_b = gamma rcprI0 S g' spkB)
    (hikA : gamma rcprI0 S g ik_a_pk = gamma rcprI0 S g' (dhPk ikA))
    (hek : gamma rcprI0 S g ek_w = gamma rcprI0 S g' o1.ek)
    (hss : gamma rcprI0 S g ss_kem =
           gamma rcprI0 S g' (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
    (hrkMsg : gamma rcprI0 S g msg_b.ratchetKey = gamma rcprI0 S g' (dhPk dhsA))
    (hdhsB : gamma rcprI0 S g dhs_b = gamma rcprI0 S g' dhsB1Clean)
    (hpqMsg : gamma rcprI0 S g pq_msg = gamma rcprI0 S g' (pqm0Clean cls))
    (hc'Rk : c'.ratchetKey = msg_b.ratchetKey)
    (hc'Ck : c'.chainKey =
      (kdfCk (createChain
        (pqxdhKdf (pqxdhIkm (agree ik_a_pk spk_b) (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)).rk
        msg_b.ratchetKey spk_b).2).1)
    (hspRecv : DY.Spqr.spqrRecv
      (DY.Spqr.spqrInit
        (pqxdhKdf (pqxdhIkm (agree ik_a_pk spk_b)
          (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)).pqr spqrB2A)
      pq_msg idx = some (spqrOut, key)) :
    let keys_b := pqxdhKdf (pqxdhIkm (agree ik_a_pk spk_b)
      (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)
    let (stB_r, _) := ratchetState (bobSt0 "alice" ik_b spk_b ik_a_pk keys_b msg_b)
      msg_b.ratchetKey dhs_b
    StateBytesAgree S g g'
      { stB_r with recv := setRecvChain stB_r.recv c', spqr := spqrOut } (stB2Clean cls) := by
  intro keys_b
  have hEq := rcprI0_cryptoEquationsHold
  have hikm : gamma rcprI0 S g
      (pqxdhIkm (agree ik_a_pk spk_b) (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem) =
      gamma rcprI0 S g'
      (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32))
        none (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) := by
    rw [gamma_pqxdhIkm, gamma_pqxdhIkm,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq]
    have hc1 := hEq.x25519_agreement_commutes
      (clamp (gamma rcprI0 S g spk_b)) (clamp (gamma rcprI0 S g' ikA))
    have hc2 := hEq.x25519_agreement_commutes
      (clamp (gamma rcprI0 S g ik_b)) (clamp (gamma rcprI0 S g' (rnd 22 32)))
    have hc3 := hEq.x25519_agreement_commutes
      (clamp (gamma rcprI0 S g spk_b)) (clamp (gamma rcprI0 S g' (rnd 22 32)))
    have hek' : gamma rcprI0 S g ek_w = gamma rcprI0 S g' (dhPk (rnd 22 32)) := by
      rwa [o1_ek_eq] at hek
    rw [hikA, hek', gamma_dhPk, gamma_dhPk, hc1, hc2, hc3]
    simp only [Option.map, gamma_dhPk, hikB, hspkB, hss]
  have hkdf1 := gamma_pqxdhKdf rcprI0 S g
    (pqxdhIkm (agree ik_a_pk spk_b) (agree ek_w ik_b) (agree ek_w spk_b) none ss_kem)
  have hkdf2 := gamma_pqxdhKdf rcprI0 S g'
    (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32)) (agree (dhPk spkB) (rnd 22 32))
      none (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
  rw [hikm] at hkdf1
  have hrk0 : gamma rcprI0 S g keys_b.rk = gamma rcprI0 S g' keys1.rk := by
    rw [keys1_eq]; exact hkdf1.1.trans hkdf2.1.symm
  have hpqr0 : gamma rcprI0 S g keys_b.pqr = gamma rcprI0 S g' keys1.pqr := by
    rw [keys1_eq]; exact hkdf1.2.2.trans hkdf2.2.2.symm
  have hcc1 := createChain_gamma_congr hrk0 hrkMsg hspkB
  have hcc2 := createChain_gamma_congr hcc1.1 hrkMsg hdhsB
  have hspInit : SpqrStateAgree S g g'
      (DY.Spqr.spqrInit keys_b.pqr spqrB2A) (DY.Spqr.spqrInit keys1.pqr spqrB2A) := by
    refine spqrStateAgree_init spqrB2A hpqr0 ?_
    unfold spqrB2A DY.Spqr.encodeSpqrDirectionParams; rw [gamma_lit, gamma_lit]
  have hspClean : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys1.pqr spqrB2A) (pqm0Clean cls) 1 =
      some (recvSt (DY.Spqr.spqrInit keys1.pqr spqrB2A) (pqm0Clean cls), key0Clean cls) := by
    unfold DY.Spqr.spqrRecv DY.Spqr.spqrEmptyMsg pqm0Clean
    rw [bytesToLiteral_spqrSendMsg]
    have hinit : (DY.Spqr.spqrInit keys1.pqr spqrB2A).view? DY.Spqr.InitState.SubF =
        some { authKey := keys1.pqr, params := spqrB2A } := by
      dsimp only [DY.Spqr.spqrInit]
      exact DY.BytesView.view_pack _
    rw [hinit]; dsimp only; rw [DY.Spqr.spqrParamsDir?_spqrParams .b2a]
    dsimp only [key0Clean, DY.Spqr.spqrSend, stA0, aliceSt, DY.Spqr.spqrInit, spqrA2B]
    rw [DY.BytesView.view_pack]
    simp [recvSt, keys1, DY.Spqr.Direction.flip]
  have hspOut := spqrRecv_gamma_congr hspInit hpqMsg hspRecv hspClean
  have hsetB : setRecvChain (ratchetState (bobSt0 "alice" ik_b spk_b ik_a_pk keys_b msg_b)
      msg_b.ratchetKey dhs_b).1.recv c' = [c'] := by
    simp [setRecvChain, ratchetState, bobSt0, hc'Rk,
      DY.Libsignal.TripleRatchet.maxReceiverChains]
  refine ⟨?_, ?_, hcc2.1, hcc2.2, hdhsB, hspOut, rfl, rfl, ?_, ?_⟩
  · show gamma rcprI0 S g (serializedIk (dhPk ik_b)) = gamma rcprI0 S g' (serializedIk (dhPk ikB))
    rw [gamma_serializedIk, gamma_serializedIk, gamma_dhPk, gamma_dhPk, hikB]
  · show gamma rcprI0 S g (serializedIk ik_a_pk) = gamma rcprI0 S g' (serializedIk (dhPk ikA))
    rw [gamma_serializedIk, gamma_serializedIk, hikA]
  · change List.map (fun c => gamma rcprI0 S g c.ratchetKey)
      (setRecvChain (ratchetState (bobSt0 "alice" ik_b spk_b ik_a_pk keys_b msg_b)
        msg_b.ratchetKey dhs_b).1.recv c') = _
    rw [hsetB]; dsimp only [stB2Clean, cB'Clean, cBClean, List.map]
    rw [hc'Rk]; exact congrArg (· :: []) hrkMsg
  · change List.map (fun c => gamma rcprI0 S g c.chainKey)
      (setRecvChain (ratchetState (bobSt0 "alice" ik_b spk_b ik_a_pk keys_b msg_b)
        msg_b.ratchetKey dhs_b).1.recv c') = _
    rw [hsetB]; dsimp only [stB2Clean, cB'Clean, cBClean, List.map]
    rw [hc'Ck, gamma_kdfCk_fst, gamma_kdfCk_fst, hcc1.2]

theorem stateBytesAgree_decrypt_ratchet {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {st st' : TRState} {rk_msg rk_msg' dhsNew dhsNew' pq_msg pq_msg' spqrOut key spqrOut' key' : Bytes}
    {c0 c0' c' c'' : RecvChain} {idx idx' : UInt32}
    (hst : StateBytesAgree S g g' st st')
    (hrecv1 : st.recv = [c0])
    (hrecv2 : st'.recv = [c0'])
    (hne1 : c0.ratchetKey ≠ rk_msg)
    (hne2 : c0'.ratchetKey ≠ rk_msg')
    (hrkMsg : gamma rcprI0 S g rk_msg = gamma rcprI0 S g' rk_msg')
    (hdhsNew : gamma rcprI0 S g dhsNew = gamma rcprI0 S g' dhsNew')
    (hpqMsg : gamma rcprI0 S g pq_msg = gamma rcprI0 S g' pq_msg')
    (hc'Rk : c'.ratchetKey = rk_msg)
    (hc''Rk : c''.ratchetKey = rk_msg')
    (hc'Ck : c'.chainKey = (kdfCk (createChain st.rk rk_msg st.dhs).2).1)
    (hc''Ck : c''.chainKey = (kdfCk (createChain st'.rk rk_msg' st'.dhs).2).1)
    (hr1 : DY.Spqr.spqrRecv st.spqr pq_msg idx = some (spqrOut, key))
    (hr2 : DY.Spqr.spqrRecv st'.spqr pq_msg' idx' = some (spqrOut', key')) :
    let (st_r, _) := ratchetState st rk_msg dhsNew
    let (st'_r, _) := ratchetState st' rk_msg' dhsNew'
    StateBytesAgree S g g'
      { st_r with recv := setRecvChain st_r.recv c', spqr := spqrOut }
      { st'_r with recv := setRecvChain st'_r.recv c'', spqr := spqrOut' } := by
  have hcc1 := createChain_gamma_congr hst.rk_eq hrkMsg hst.dhs_eq
  have hcc2 := createChain_gamma_congr hcc1.1 hrkMsg hdhsNew
  have hspOut := spqrRecv_gamma_congr hst.spqr_agree hpqMsg hr1 hr2
  have hset1 : setRecvChain (ratchetState st rk_msg dhsNew).1.recv c' = [c0, c'] := by
    simp [setRecvChain, ratchetState, hrecv1, hc'Rk, hne1,
      DY.Libsignal.TripleRatchet.maxReceiverChains]
  have hset2 : setRecvChain (ratchetState st' rk_msg' dhsNew').1.recv c'' = [c0', c''] := by
    simp [setRecvChain, ratchetState, hrecv2, hc''Rk, hne2,
      DY.Libsignal.TripleRatchet.maxReceiverChains]
  have hrk0 : gamma rcprI0 S g c0.ratchetKey = gamma rcprI0 S g' c0'.ratchetKey := by
    have h := hst.recvRk_eq; rw [hrecv1, hrecv2] at h; exact List.cons.inj h |>.1
  have hck0 : gamma rcprI0 S g c0.chainKey = gamma rcprI0 S g' c0'.chainKey := by
    have h := hst.recvCk_eq; rw [hrecv1, hrecv2] at h; exact List.cons.inj h |>.1
  refine ⟨hst.myIk_eq, hst.peerIk_eq, hcc2.1, hcc2.2, hdhsNew, hspOut, rfl,
    congrArg (fun n => if n = 0 then 0 else n - 1) hst.ns_eq, ?_, ?_⟩
  · change List.map (fun c => gamma rcprI0 S g c.ratchetKey)
        (setRecvChain (ratchetState st rk_msg dhsNew).1.recv c') =
      List.map (fun c => gamma rcprI0 S g' c.ratchetKey)
        (setRecvChain (ratchetState st' rk_msg' dhsNew').1.recv c'')
    rw [hset1, hset2]; dsimp only [List.map]; rw [hrk0, hc'Rk, hc''Rk, hrkMsg]
  · change List.map (fun c => gamma rcprI0 S g c.chainKey)
        (setRecvChain (ratchetState st rk_msg dhsNew).1.recv c') =
      List.map (fun c => gamma rcprI0 S g' c.chainKey)
        (setRecvChain (ratchetState st' rk_msg' dhsNew').1.recv c'')
    rw [hset1, hset2]; dsimp only [List.map]
    rw [hck0, hc'Ck, hc''Ck, gamma_kdfCk_fst, gamma_kdfCk_fst, hcc1.2]

/-! ## 5. Reducible Alice Call-4 Key Constants & Exact `gamma` Evaluations -/

def rcprAliceRk4 : HwBytes :=
  [0x58, 0xa4, 0x84, 0xe4, 0x2f, 0xd8, 0xb2, 0x67, 0x88, 0x2c, 0xa1, 0x48, 0x2e, 0xc3, 0xac, 0xca,
   0x27, 0x98, 0x6b, 0x25, 0xd8, 0xfb, 0x4c, 0x32, 0x4c, 0xfa, 0xe7, 0x01, 0x4e, 0x49, 0x89, 0x8d]

def rcprAliceDhs4 : HwBytes :=
  [0x12, 0x96, 0x71, 0x5b, 0x07, 0xf2, 0x29, 0x5c, 0xb6, 0x20, 0x53, 0xe3, 0xbf, 0x6d, 0xee, 0x62,
   0x7f, 0x02, 0x17, 0x9e, 0xe7, 0xf0, 0x0e, 0x5c, 0x99, 0xfd, 0xfd, 0x96, 0x02, 0xe6, 0x62, 0x7f]

def rcprAliceCks4 : HwBytes :=
  [0x79, 0xa3, 0xeb, 0xeb, 0xea, 0x0d, 0x53, 0x88, 0xac, 0x72, 0xb8, 0xa2, 0x61, 0x2b, 0x1e, 0x7d,
   0xdf, 0xe7, 0x5c, 0xf5, 0x6e, 0x21, 0xa1, 0xe0, 0x8b, 0x67, 0x01, 0x03, 0x99, 0x06, 0x45, 0xbc]

def rcprAliceCk0 : HwBytes :=
  [0xf6, 0xf8, 0x98, 0x23, 0xc7, 0xf7, 0x3c, 0x10, 0xf8, 0x2b, 0x80, 0x53, 0xad, 0x26, 0x16, 0x6b,
   0x0a, 0xa3, 0xf0, 0xfc, 0x30, 0x8e, 0x34, 0xe8, 0x7b, 0x34, 0x54, 0x3c, 0xe6, 0x2f, 0xb2, 0x05]

def rcprAliceCk1 : HwBytes :=
  [0xd3, 0x5e, 0x29, 0x16, 0x13, 0xc0, 0x8d, 0x49, 0x77, 0x34, 0xa2, 0xc1, 0x9f, 0xe0, 0x0b, 0x34,
   0xda, 0xe1, 0x4d, 0x28, 0x0c, 0x19, 0xc7, 0x0c, 0x6c, 0x40, 0xf8, 0x0b, 0x14, 0xfe, 0x45, 0x02]

noncomputable section

private abbrev F0 := DY.Libsignal.Refinement.sha256CompressFunction rcprI0
private def wrLabelFast : HwBytes :=
  DY.Libsignal.Composed.Refinement.ofByteArray "WhisperRatchet".toList.utf8Encode
private def pqLabelFast : HwBytes :=
  DY.Libsignal.Composed.Refinement.ofByteArray
    "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toList.utf8Encode

private theorem str_toUTF8_eq (s : String) : s.toUTF8 = s.toList.utf8Encode := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]

private def hkdfRoot0 (rk dh : HwBytes) : HwBytes :=
  Symbolic.Swarm.CREF.TR.hkdfBlock1Bytes F0 (ByteSpecs.hmacWith F0 rk dh) wrLabelFast
private def hkdfChain0 (rk dh : HwBytes) : HwBytes :=
  Symbolic.Swarm.CREF.TR.hkdfBlock2Bytes F0 (ByteSpecs.hmacWith F0 rk dh) wrLabelFast

private theorem dhAgreeBytes_of_idx {sk pk : HwBytes} {i j : Fin 7}
    (hs : rcprSecretIdx (clamp sk) = some i) (hp : pk = rcprPubOfIdx j) :
    (rcprI0 DY.Libsignal.Refinement.x25519AgreementSymbol [clamp sk, pk]).getD [] = rcprDhByIdx i j := by
  rw [rcprI0_agreement, Option.getD_some]; unfold rcprLookupDh; subst hp
  change (if DY.X25519.isLowOrderKey ((rcprPubOfOpt (some j)).map BitVec.toNat) then _ else
    match rcprSecretIdx (clamp sk), DefsI0.rcprPointIdx (rcprPubOfOpt (some j)) with
    | some i, some j => rcprDhByIdx i j | _, _ => _) = _
  rw [rcprPubOfOpt_not_lowOrder (some j), rcprPointIdx_rcprPubOfOpt (some j), hs]; rfl

private theorem gamma_createChain_idx {S : OpaqueSymbolSemantics} {g : Ghost}
    {rk theirPk ourSk : Bytes} {i j : Fin 7}
    (hs : rcprSecretIdx (clamp (gamma rcprI0 S g ourSk)) = some i)
    (hp : gamma rcprI0 S g theirPk = rcprPubOfIdx j) :
    gamma rcprI0 S g (createChain rk theirPk ourSk).1 =
      hkdfRoot0 (gamma rcprI0 S g rk) (rcprDhByIdx i j) ∧
    gamma rcprI0 S g (createChain rk theirPk ourSk).2 =
      hkdfChain0 (gamma rcprI0 S g rk) (rcprDhByIdx i j) := by
  have h1 : (createChain rk theirPk ourSk).1 = DY.Libsignal.TripleRatchet.hkdfBlock1
    (DY.Libsignal.TripleRatchet.hmac rk (agree theirPk ourSk))
    (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  have h2 : (createChain rk theirPk ourSk).2 = DY.Libsignal.TripleRatchet.hkdfBlock2
    (DY.Libsignal.TripleRatchet.hmac rk (agree theirPk ourSk))
    (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
  have hwr : Symbolic.Swarm.CREF.TR.whisperRatchetBytes = wrLabelFast := by
    unfold Symbolic.Swarm.CREF.TR.whisperRatchetBytes wrLabelFast; rw [str_toUTF8_eq]
  rw [h1, h2, gamma_hkdfBlock1, gamma_hkdfBlock2, gamma_hmac,
      gamma_agree rcprI0 rcprI0_cryptoEquationsHold, gamma_whisperRatchet, hwr,
      dhAgreeBytes_of_idx hs hp]
  exact ⟨rfl, rfl⟩

private theorem ikASec_idx : rcprSecretIdx (clamp rcprSetup.aliceId) = some ⟨0, by decide⟩ := by decide +kernel
private theorem ikBSec_idx : rcprSecretIdx (clamp rcprSetup.bobId) = some ⟨1, by decide⟩ := by decide +kernel

private def cleanIkmBytes : HwBytes :=
  Symbolic.Swarm.CREF.TR.pqxdhIkmBytes
    (rcprDhByIdx ⟨0, by decide⟩ ⟨2, by decide⟩) (rcprDhByIdx ⟨3, by decide⟩ ⟨1, by decide⟩)
    (rcprDhByIdx ⟨3, by decide⟩ ⟨2, by decide⟩) none
    ((Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberEncaps ev0KyberEntFast).drop 1568)
private def cleanPrk0Bytes : HwBytes := ByteSpecs.hmacWith F0 (List.replicate 32 0#8) cleanIkmBytes
private def cleanRk0Bytes : HwBytes := Symbolic.Swarm.CREF.TR.hkdfBlock1Bytes F0 cleanPrk0Bytes pqLabelFast
private def cleanCk0Bytes : HwBytes := Symbolic.Swarm.CREF.TR.hkdfBlock2Bytes F0 cleanPrk0Bytes pqLabelFast
private def cleanRkA0Bytes : HwBytes := hkdfRoot0 cleanRk0Bytes (rcprDhByIdx ⟨4, by decide⟩ ⟨2, by decide⟩)
private def cleanRkA1Bytes : HwBytes := hkdfRoot0 cleanRkA0Bytes (rcprDhByIdx ⟨4, by decide⟩ ⟨5, by decide⟩)
private def cleanCkA1RawBytes : HwBytes := hkdfChain0 cleanRkA0Bytes (rcprDhByIdx ⟨4, by decide⟩ ⟨5, by decide⟩)
private def cleanRkA2Bytes : HwBytes := hkdfRoot0 cleanRkA1Bytes (rcprDhByIdx ⟨6, by decide⟩ ⟨5, by decide⟩)
private def cleanCksA2Bytes : HwBytes := hkdfChain0 cleanRkA1Bytes (rcprDhByIdx ⟨6, by decide⟩ ⟨5, by decide⟩)
private def cleanCkA1Bytes : HwBytes := ByteSpecs.hmacWith F0 cleanCkA1RawBytes [0x02#8]

private theorem cleanBytes_eval_all :
    cleanRkA2Bytes = rcprAliceRk4 ∧ ev4CoinsFast.take 32 = rcprAliceDhs4 ∧
    cleanCksA2Bytes = rcprAliceCks4 ∧ cleanCk0Bytes = rcprAliceCk0 ∧
    cleanCkA1Bytes = rcprAliceCk1 := by decide +kernel

end

theorem gamma_stA4Clean_keys {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    gamma rcprI0 S (gClean r cls) (stA4Clean cls).rk = rcprAliceRk4 ∧
    gamma rcprI0 S (gClean r cls) (stA4Clean cls).dhs = rcprAliceDhs4 ∧
    gamma rcprI0 S (gClean r cls) (stA4Clean cls).cks = rcprAliceCks4 ∧
    gamma rcprI0 S (gClean r cls) cA0Clean.chainKey = rcprAliceCk0 ∧
    gamma rcprI0 S (gClean r cls) cA1Clean.chainKey = rcprAliceCk1 := by
  have hEq := rcprI0_cryptoEquationsHold
  have hrandAt := setupRandomsAt_of_fit hfit
  have hsec (ts idx : Nat) (hlt : ts < 22) (hs : secretBytes r idx = r.fresh ts 32) :
      gamma rcprI0 S (gClean r cls) (rnd ts 32) = secretBytes r idx := by
    unfold rnd; rw [gamma_rand]
    simp only [show (32 : Nat) ≠ 0 by decide, ↓reduceIte, gClean_sigma_lt22 _ _ hlt, hs]
  have hikA : gamma rcprI0 S (gClean r cls) ikA = rcprSetup.aliceId :=
    (hsec 0 0 (by decide) (by unfold secretBytes; rw [hrandAt]; rfl)).trans
      hfit.1.1.2.2.2.2.2.2.1
  have hikB : gamma rcprI0 S (gClean r cls) ikB = rcprSetup.bobId :=
    (hsec 5 1 (by decide) (by unfold secretBytes; rw [hrandAt]; rfl)).trans
      hfit.1.1.2.2.2.2.2.2.2.1
  have h22 : gamma rcprI0 S (gClean r cls) (rnd 22 32) = slice (ev 0).coins 0 32 := by
    unfold rnd; rw [gamma_rand]; simp [gClean_sigma_22]
  have h23 : gamma rcprI0 S (gClean r cls) (rnd 23 32) = ev0KyberEnt := by
    unfold rnd; rw [gamma_rand]; simp [gClean_sigma_23]
  have hdhsA : gamma rcprI0 S (gClean r cls) dhsA = slice (ev 0).coins 160 32 := by
    show gamma rcprI0 S (gClean r cls) (rnd 24 32) = _; unfold rnd; rw [gamma_rand]; simp [gClean_sigma_24]
  have hdhsA1 : gamma rcprI0 S (gClean r cls) dhsA1Clean = (ev 4).coins.take 32 := by
    show gamma rcprI0 S (gClean r cls) (rnd 54 32) = _; unfold rnd; rw [gamma_rand]; simp [gClean_sigma_54]
  have hpkIkB : gamma rcprI0 S (gClean r cls) (dhPk ikB) = rcprPubOfIdx ⟨1, by decide⟩ := by
    rw [gamma_dhPk, hikB, rcprI0_publicKey]; unfold rcprLookupPub rcprPubOfOpt; rw [ikBSec_idx]; rfl
  have hpkSpkB := gamma_dhPk_spkB (S := S) (cls := cls) hfit
  have hpkDhsB1 := gamma_dhPk_dhsB1 (S := S) (cls := cls) hfit
  have hss : gamma rcprI0 S (gClean r cls)
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 =
      (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compKyberEncaps ev0KyberEntFast).drop 1568 := by
    have hent32 : ev0KyberEntFast.length = 32 := by rw [← ev0KyberEnt_eq]; exact ev0_coins_facts.2.2.2.1
    simp only [gamma_kemEncap_snd, h23, ev0KyberEnt_eq, hent32, ↓reduceIte,
      rcprI0_kyberEncaps, Option.getD_some]
  have hikm : gamma rcprI0 S (gClean r cls)
      (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32))
        (agree (dhPk spkB) (rnd 22 32)) none
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2) = cleanIkmBytes := by
    rw [gamma_pqxdhIkm, gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq, gamma_agree rcprI0 hEq,
        hikA, h22, dhAgreeBytes_of_idx ikASec_idx hpkSpkB,
        dhAgreeBytes_of_idx ev0_coins_facts.2.1 hpkIkB,
        dhAgreeBytes_of_idx ev0_coins_facts.2.1 hpkSpkB, hss]; rfl
  have hkdf := gamma_pqxdhKdf rcprI0 S (gClean r cls)
    (pqxdhIkm (agree (dhPk spkB) ikA) (agree (dhPk ikB) (rnd 22 32))
      (agree (dhPk spkB) (rnd 22 32)) none
      (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2)
  have hpql : Symbolic.Swarm.CREF.TR.pqxdhLabelBytes = pqLabelFast := by
    unfold Symbolic.Swarm.CREF.TR.pqxdhLabelBytes pqLabelFast; rw [str_toUTF8_eq]
  rw [hikm] at hkdf
  have hrk0 : gamma rcprI0 S (gClean r cls) keys1.rk = cleanRk0Bytes := by
    unfold cleanRk0Bytes cleanPrk0Bytes F0
    rw [keys1_eq]; simpa only [Symbolic.Swarm.CREF.TR.pqxdhKdfBytes, hpql] using hkdf.1
  have hck0 : gamma rcprI0 S (gClean r cls) keys1.ck = cleanCk0Bytes := by
    unfold cleanCk0Bytes cleanPrk0Bytes F0
    rw [keys1_eq]; simpa only [Symbolic.Swarm.CREF.TR.pqxdhKdfBytes, hpql] using hkdf.2.1
  have hs4 : rcprSecretIdx (clamp (gamma rcprI0 S (gClean r cls) dhsA)) = some ⟨4, by decide⟩ := by
    rw [hdhsA]; exact ev0_coins_facts.2.2.1
  have hs6 : rcprSecretIdx (clamp (gamma rcprI0 S (gClean r cls) dhsA1Clean)) = some ⟨6, by decide⟩ := by
    rw [hdhsA1]; exact ev4_coins_idx
  have hrkA0 : gamma rcprI0 S (gClean r cls) stA0.rk = cleanRkA0Bytes := by
    show gamma rcprI0 S (gClean r cls) (createChain keys1.rk (dhPk spkB) dhsA).1 = _
    rw [(gamma_createChain_idx hs4 hpkSpkB).1, hrk0]; rfl
  have hcc1 := gamma_createChain_idx (rk := stA0.rk) hs4 hpkDhsB1
  rw [hrkA0] at hcc1
  have hcc2 := gamma_createChain_idx (rk := (createChain stA0.rk (dhPk dhsB1Clean) dhsA).1) hs6 hpkDhsB1
  rw [hcc1.1] at hcc2
  obtain ⟨eRk, eDhs, eCks, eCk0, eCk1⟩ := cleanBytes_eval_all
  refine ⟨hcc2.1.trans eRk, ?_, hcc2.2.trans eCks, hck0.trans eCk0, ?_⟩
  · show gamma rcprI0 S (gClean r cls) dhsA1Clean = rcprAliceDhs4
    rw [hdhsA1, ev4Coins_eq]; exact eDhs
  · show gamma rcprI0 S (gClean r cls) (kdfCk (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2).1 = _
    rw [gamma_kdfCk_fst, hcc1.2]; exact eCk1

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
