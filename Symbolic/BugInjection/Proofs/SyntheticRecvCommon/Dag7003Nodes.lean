/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.Basic

/-!
# Concrete `TermAt` and `SafeMemo` Proofs for Seed 7003 (`Dag7003Nodes.lean`)

Connects the 323-node concrete DAG in `Dag7003Data` to the symbolic DY protocol terms, stored
states, and trial terms for both receive-path regression disproofs under `gClean7003`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH
  (PQXDHState HandshakeKeys AliceHandshakeOut aliceAgreement serializedIk pqxdhKdf pqxdhIkm)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg RecvChain trMsgKeys computeMac kdfCk kdfRk createChain
   hkdfBlock1 hkdfBlock2 hkdfBlock3 zeroSalt spqrA2B spqrB2A trHonestWireMsg)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost randTerm ofByteArray spqrKeyBytes gamma' gamma)
open Symbolic.BugInjection (fillFresh)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd aliceOut aliceSt encMsg encSig encSt bobSt0 ratchetState recvSt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (t4_length)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
  (tRnd tLit tCat tDhPk tKdf tSym tTr8 tKemEnc tKemSS tSSendSt tSSendM tTrW)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003 compLookupDh)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
  (pt1M1Bytes pt1M2Bytes pt3M2Bytes coins1Bytes coins3M2Bytes addr1Bytes
   pqrBytes salt1Bytes pqMsg1Bytes salt3Bytes pqMsg3Bytes ev4Variation)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
  (SemPinned2 SemPinned4_M2 if_pos' if_neg')
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs (DagOp trWireEvOf)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
  (notAnyAiNodeBytes noAiSuffix noStrictAiSuffix IsPt7003Bytes SafeMemo TermAt
   safeMemo_of_termAt gamma_of_termAt termAt_congr)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt

/-! ## 1. Zero-Fuel `isAliceWire` & Unified `gClean7003` -/

def isAliceWire (tw : DY.Bytes) : Bool :=
  match tw.view? DY.TrWire.TrWireMsg.SubF with
  | some f =>
    match f.senderRatchetKey.view? DY.DiffieHellman.DhPk.SubF with
    | some k =>
      match k.sk.view? DY.Random.Random with
      | some r => r.timestamp == 24
      | none => false
    | none => false
  | none => false

theorem isAliceWire_tTrW_dhPk_rnd (ver : UInt8) (ts sz : Nat) (cnt prev : UInt32)
    (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) :
    isAliceWire (tTrW ver (dhPk (tRnd ts sz)) cnt prev ct pq ev) = (ts == 24) := by
  simp only [isAliceWire, tTrW, dhPk, DY.DiffieHellman.CanDH.dhPk, tRnd, DY.BytesView.view_pack]

def gClean7003 (mode : Bool) (cl₁ cl₃ : Nat) : Ghost where
  σ ts sz :=
    if ts == 0 && sz == 32 then bytesOf ikAId
    else if ts == 5 && sz == 32 then bytesOf ikBId
    else if ts == 10 && sz == 32 then bytesOf spkBId
    else if ts == 11 && sz == 64 then fillFresh 11 64
    else if ts == 16 && sz == 64 then bytesOf pqskBId
    else if ts == 17 && sz == 64 then fillFresh 17 64
    else if ts == 22 && sz == 32 then bytesOf r22Id
    else if ts == 23 && sz == 32 then bytesOf r23Id
    else if ts == 24 && sz == 32 then bytesOf dhsAId
    else if ts == 31 && sz == 32 then (if mode then pt1M2Bytes else pt1M1Bytes)
    else if ts == 32 && sz == cl₁ && decide (0 < cl₁ ∧ cl₁ ≤ 64) then coins1Bytes.take cl₁
    else if ts == 38 && sz == 32 then bytesOf dhsBId
    else if ts == 47 && sz == 32 then pt3M2Bytes
    else if ts == 48 && sz == cl₃ && decide (0 < cl₃ ∧ cl₃ ≤ 64) then coins3M2Bytes.take cl₃
    else List.replicate sz 0#8
  addr tw := if isAliceWire tw then addr1Bytes else []

private theorem ite_len {c : Bool} {a b : HwBytes} {sz : Nat}
    (ha : c = true → a.length = sz) (hb : b.length = sz) :
    (if c then a else b).length = sz := by
  cases c <;> simp_all

theorem gClean7003_σ_length {mode : Bool} {cl₁ cl₃ ts sz : Nat}
    (h31 : ts ≠ 31) (h47 : ts ≠ 47) :
    ((gClean7003 mode cl₁ cl₃).σ ts sz).length = sz := by
  have hc1 : coins1Bytes.length = 64 := by decide
  have hc3 : coins3M2Bytes.length = 64 := by decide
  unfold gClean7003; dsimp only
  have h31b : (ts == 31 && sz == 32) = false := by simp [beq_eq_false_iff_ne.mpr h31]
  have h47b : (ts == 47 && sz == 32) = false := by simp [beq_eq_false_iff_ne.mpr h47]
  rw [h31b, h47b]
  refine ite_len ?_ (ite_len ?_ (ite_len ?_ (ite_len ?_ (ite_len ?_ (ite_len ?_
    (ite_len ?_ (ite_len ?_ (ite_len ?_ (ite_len (fun h => nomatch h)
    (ite_len ?_ (ite_len ?_ (ite_len (fun h => nomatch h)
    (ite_len ?_ List.length_replicate)))))))))))))
  all_goals (
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    try obtain ⟨⟨_, rfl⟩, _, _⟩ := h
    try obtain ⟨_, rfl⟩ := h
    first | rfl | decide | (rw [List.length_take, hc1]; omega) | (rw [List.length_take, hc3]; omega))

/-! ## 2. Pure Protocol Terms & Equalities to `HonestSession` -/

def o1Pure : AliceHandshakeOut :=
  let ikA := tRnd 0 32
  let ek := tRnd 22 32
  let e := tRnd 23 32
  let ikBPk := dhPk (tRnd 5 32)
  let spkPk := dhPk (tRnd 10 32)
  let pqPk := DY.PQKem.kemPk (tRnd 16 64)
  { ikA := dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk := none, ek := dhPk ek,
    ct := (aliceAgreement ikA ek ikBPk spkPk pqPk none e).1,
    keys := (aliceAgreement ikA ek ikBPk spkPk pqPk none e).2 }

theorem o1_eq_pure : HonestSession.o1 = o1Pure := by
  unfold HonestSession.o1 aliceOut
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt
  rw [t4_length]; rfl

def stA0Pure : TRState := aliceSt "bob" o1Pure (tRnd 24 32)

theorem stA0_eq_pure : HonestSession.stA0 = stA0Pure := by
  unfold HonestSession.stA0 stA0Pure; rw [o1_eq_pure]; rfl

def key0Pure : DY.Bytes :=
  DY.Spqr.spqrChainKey o1Pure.keys.pqr spqrA2B (DY.Spqr.encodeSpqrIndexTerm 1)

theorem spqrSend_stA0_key (cl₁ : Nat) :
    (DY.Spqr.spqrSend stA0Pure.spqr (tRnd 32 cl₁)).2.1 = key0Pure := by
  dsimp only [stA0Pure, aliceSt, DY.Spqr.spqrSend, DY.Spqr.spqrInit]
  rw [DY.BytesView.view_pack]; rfl

def pqMsg1Pure (cl₁ : Nat) : DY.Bytes := (DY.Spqr.spqrSend stA0Pure.spqr (tRnd 32 cl₁)).2.2
def stA1Pure (cl₁ : Nat) : TRState := encSt stA0Pure (tRnd 32 cl₁)
def encMsg1Pure (cl₁ : Nat) : DY.Bytes := encMsg stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32)
def encSig1Pure (cl₁ : Nat) : TRState × TRSignalMsg :=
  (stA1Pure cl₁, encSig stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32))

abbrev dhsBPure : DY.Bytes := tRnd 38 32

def stB00Pure (cl₁ : Nat) : TRState :=
  bobSt0 "alice" (tRnd 5 32) (tRnd 10 32) (dhPk (tRnd 0 32)) o1Pure.keys
    (encSig stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32))

def stB0'Pure (cl₁ : Nat) : TRState :=
  (ratchetState (stB00Pure cl₁) (dhPk (tRnd 24 32)) dhsBPure).1

def cBPure (cl₁ : Nat) : RecvChain :=
  (ratchetState (stB00Pure cl₁) (dhPk (tRnd 24 32)) dhsBPure).2

def cB'Pure (cl₁ : Nat) : RecvChain :=
  { cBPure cl₁ with chainKey := (kdfCk (cBPure cl₁).chainKey).1, index := 1 }

def stB1Pure (cl₁ : Nat) : TRState :=
  { stB0'Pure cl₁ with
      recv := [cB'Pure cl₁]
      spqr := recvSt (DY.Spqr.spqrInit o1Pure.keys.pqr spqrB2A) (pqMsg1Pure cl₁) }

def key3Pure (cl₁ cl₃ : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend (stB1Pure cl₁).spqr (tRnd 48 cl₃)).2.1

def pqMsg3Pure (cl₁ cl₃ : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend (stB1Pure cl₁).spqr (tRnd 48 cl₃)).2.2

def stB2Pure (cl₁ cl₃ : Nat) : TRState := encSt (stB1Pure cl₁) (tRnd 48 cl₃)

def encMsg3Pure (cl₁ cl₃ : Nat) : DY.Bytes :=
  encMsg (stB1Pure cl₁) (tRnd 48 cl₃) (key3Pure cl₁ cl₃) (tRnd 47 32)

def encSig3Pure (cl₁ cl₃ : Nat) : TRSignalMsg :=
  encSig (stB1Pure cl₁) (tRnd 48 cl₃) (key3Pure cl₁ cl₃) (tRnd 47 32)

def wire4MutPure (cl₁ cl₃ : Nat) : DY.Bytes :=
  tTrW 4 (dhPk dhsBPure) 0 0 (encSig3Pure cl₁ cl₃).ciphertext (pqMsg3Pure cl₁ cl₃) ev4Variation

def tMut4M2Pure (cl₁ cl₃ : Nat) : DY.Bytes :=
  tCat (wire4MutPure cl₁ cl₃) (encSig3Pure cl₁ cl₃).mac

/-! ## 3. Generic Key-Schedule, MAC, and Coin Combinators -/

theorem norm_dhPk_eq (sk : DY.Bytes) :
    DY.X25519.normalizeX25519Key (dhPk sk) = dhPk sk := by
  dsimp only [DY.X25519.normalizeX25519Key, dhPk, DY.DiffieHellman.CanDH.dhPk]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

theorem ta_trMsgKeys {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {tsalt tseed : DY.Bytes} {salt seed prk ck wi2 mk wi3 iv : Nat}
    (hsalt : TermAt mode S g pts tsalt salt) (hseed : TermAt mode S g pts tseed seed)
    (hw1 : TermAt mode S g pts (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 1)) wmkInfo1Id)
    (hw2 : TermAt mode S g pts (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 2)) wmkInfo2Id)
    (hw3 : TermAt mode S g pts (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 3)) wmkInfo3Id)
    (h1 : opOf prk = .kdf salt seed := by decide) (hp1 : prk < dagSize := by decide)
    (hs1 : prk ≠ skipIdOf mode := by skip_ok)
    (h2 : opOf ck = .kdf prk wmkInfo1Id := by decide) (hp2 : ck < dagSize := by decide)
    (hs2 : ck ≠ skipIdOf mode := by skip_ok)
    (h3 : opOf wi2 = .concat ck wmkInfo2Id := by decide) (hp3 : wi2 < dagSize := by decide)
    (hs3 : wi2 ≠ skipIdOf mode := by skip_ok)
    (h4 : opOf mk = .kdf prk wi2 := by decide) (hp4 : mk < dagSize := by decide)
    (hs4 : mk ≠ skipIdOf mode := by skip_ok)
    (h5 : opOf wi3 = .concat mk wmkInfo3Id := by decide) (hp5 : wi3 < dagSize := by decide)
    (hs5 : wi3 ≠ skipIdOf mode := by skip_ok)
    (h6 : opOf iv = .kdf prk wi3 := by decide) (hp6 : iv < dagSize := by decide)
    (hs6 : iv ≠ skipIdOf mode := by skip_ok) :
    TermAt mode S g pts (trMsgKeys tsalt tseed).cipherKey ck ∧
    TermAt mode S g pts (trMsgKeys tsalt tseed).macKey mk ∧
    TermAt mode S g pts (trMsgKeys tsalt tseed).iv iv := by
  have hprk : TermAt mode S g pts (DY.Libsignal.TripleRatchet.hmac tsalt tseed) prk :=
    termAt_kdf h1 hp1 hs1 hsalt hseed
  have hck : TermAt mode S g pts (trMsgKeys tsalt tseed).cipherKey ck :=
    termAt_kdf h2 hp2 hs2 hprk hw1
  have hwi2 := termAt_concat h3 hp3 hs3 hck hw2
  have hmk : TermAt mode S g pts (trMsgKeys tsalt tseed).macKey mk :=
    termAt_kdf h4 hp4 hs4 hprk hwi2
  have hwi3 := termAt_concat h5 hp5 hs5 hmk hw3
  have hiv : TermAt mode S g pts (trMsgKeys tsalt tseed).iv iv :=
    termAt_kdf h6 hp6 hs6 hprk hwi3
  exact ⟨hck, hmk, hiv⟩

theorem ta_macFromMi {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {tmk tsik trik tw : DY.Bytes} {mk mi fm mac : Nat}
    (hmk : TermAt mode S g pts tmk mk)
    (hmi : TermAt mode S g pts (tCat tsik (tCat trik tw)) mi)
    (h1 : opOf fm = .kdf mk mi := by decide) (hp1 : fm < dagSize := by decide)
    (hs1 : fm ≠ skipIdOf mode := by skip_ok)
    (h2 : opOf mac = .trunc8 fm := by decide) (hp2 : mac < dagSize := by decide)
    (hs2 : mac ≠ skipIdOf mode := by skip_ok) :
    TermAt mode S g pts (computeMac tmk tsik trik tw) mac :=
  termAt_trunc8 h2 hp2 hs2 (termAt_kdf h1 hp1 hs1 hmk hmi)

theorem ta_createChain {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {trk tsk1 tsk2 : DY.Bytes} {rk pk1 sk1 pk2 sk2 dhId prk rkOut wi2 ckOut : Nat}
    (hrk : TermAt mode S g pts trk rk)
    (hsk1 : TermAt mode S g pts tsk1 sk1) (hpk1 : TermAt mode S g pts (dhPk tsk1) pk1)
    (hsk2 : TermAt mode S g pts tsk2 sk2) (hpk2 : TermAt mode S g pts (dhPk tsk2) pk2)
    (hwr1 : TermAt mode S g pts (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
      (DY.Libsignal.TripleRatchet.litByte 1)) wrInfo1Id)
    (hwr2 : TermAt mode S g pts (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
      (DY.Libsignal.TripleRatchet.litByte 2)) wrInfo2Id)
    (hsh1 : tsk1 = shapeOf sk1 := by rfl) (hsh2 : tsk2 = shapeOf sk2 := by rfl)
    (hdh : opOf dhId = .dh pk1 sk2 := by decide) (hpd : dhId < dagSize := by decide)
    (hsd : dhId ≠ skipIdOf mode := by skip_ok)
    (hcomm : compLookupDh (DY.Libsignal.Composed.Refinement.clamp (bytesOf sk1)) (bytesOf pk2) =
      bytesOf dhId := by decide)
    (h1 : opOf prk = .kdf rk dhId := by decide) (hp1 : prk < dagSize := by decide)
    (hs1 : prk ≠ skipIdOf mode := by skip_ok)
    (h2 : opOf rkOut = .kdf prk wrInfo1Id := by decide) (hp2 : rkOut < dagSize := by decide)
    (hs2 : rkOut ≠ skipIdOf mode := by skip_ok)
    (h3 : opOf wi2 = .concat rkOut wrInfo2Id := by decide) (hp3 : wi2 < dagSize := by decide)
    (hs3 : wi2 ≠ skipIdOf mode := by skip_ok)
    (h4 : opOf ckOut = .kdf prk wi2 := by decide) (hp4 : ckOut < dagSize := by decide)
    (hs4 : ckOut ≠ skipIdOf mode := by skip_ok) :
    TermAt mode S g pts (createChain trk (dhPk tsk1) tsk2).1 rkOut ∧
    TermAt mode S g pts (createChain trk (dhPk tsk1) tsk2).2 ckOut := by
  have hd := termAt_dh_dhPk hdh hpd hsd hcomm hsh1 hsh2 hsk1 hpk1 hsk2 hpk2
  have hprk := termAt_kdf h1 hp1 hs1 hrk hd
  have hrkO := termAt_kdf h2 hp2 hs2 hprk hwr1
  have hwi2 := termAt_concat h3 hp3 hs3 hrkO hwr2
  have hckO := termAt_kdf h4 hp4 hs4 hprk hwi2
  unfold createChain DY.X25519.agree
  rw [norm_dhPk_eq]
  exact ⟨hrkO, hckO⟩

private def coin1NodeValid (cl : Nat) : Bool :=
  let id := coin1NodeId cl
  decide (id < dagSize) && decide (id ≠ dh44Id) && decide (id ≠ dh55Id) &&
    (opOf id == .rand 32 cl) && (bytesOf id == coins1Bytes.take cl)

private theorem all_coin1NodesValid :
    ((List.range' 1 64).all coin1NodeValid) = true := by decide +kernel

theorem coins32_safe_and_gamma {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (hcl : cl₁ ≤ 64) :
    SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 32 cl₁) ∧
    gamma compI7003 S (gClean7003 mode cl₁ cl₃) (tRnd 32 cl₁) = coins1Bytes.take cl₁ := by
  by_cases hz : cl₁ = 0
  · subst hz
    exact ⟨safeMemo_randTerm_zero 32,
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_randTerm_zero S _ 32⟩
  · have hpos : 0 < cl₁ := Nat.pos_of_ne_zero hz
    have hmem : cl₁ ∈ List.range' 1 64 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have hv := List.all_eq_true.mp all_coin1NodesValid cl₁ hmem
    unfold coin1NodeValid at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨hid, h44⟩, h55⟩, hop⟩, hb⟩ := hv
    have hskp : coin1NodeId cl₁ ≠ skipIdOf mode := by cases mode <;> [exact h55; exact h44]
    have hg : (gClean7003 mode cl₁ cl₃).σ 32 cl₁ = bytesOf (coin1NodeId cl₁) := by
      unfold gClean7003; simp [hpos, hcl, hb]
    have hta := termAt_rand (pts := pts) (S := S) hop hid hskp hg
    exact ⟨safeMemo_of_termAt hta, (gamma_of_termAt hta).trans hb⟩

private def coin3NodeValid (cl : Nat) : Bool :=
  let id := coin3NodeId cl
  decide (id < dagSize) && decide (id ≠ dh44Id) && decide (id ≠ dh55Id) &&
    (opOf id == .rand 48 cl) && (bytesOf id == coins3M2Bytes.take cl)

private theorem all_coin3NodesValid :
    ((List.range' 1 64).all coin3NodeValid) = true := by decide +kernel

theorem coins48_safe_and_gamma {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (hcl : cl₃ ≤ 64) :
    SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 48 cl₃) ∧
    gamma compI7003 S (gClean7003 mode cl₁ cl₃) (tRnd 48 cl₃) = coins3M2Bytes.take cl₃ := by
  by_cases hz : cl₃ = 0
  · subst hz
    exact ⟨safeMemo_randTerm_zero 48,
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_randTerm_zero S _ 48⟩
  · have hpos : 0 < cl₃ := Nat.pos_of_ne_zero hz
    have hmem : cl₃ ∈ List.range' 1 64 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have hv := List.all_eq_true.mp all_coin3NodesValid cl₃ hmem
    unfold coin3NodeValid at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨hid, h44⟩, h55⟩, hop⟩, hb⟩ := hv
    have hskp : coin3NodeId cl₃ ≠ skipIdOf mode := by cases mode <;> [exact h55; exact h44]
    have hg : (gClean7003 mode cl₁ cl₃).σ 48 cl₃ = bytesOf (coin3NodeId cl₃) := by
      unfold gClean7003; simp [hpos, hcl, hb]
    have hta := termAt_rand (pts := pts) (S := S) hop hid hskp hg
    exact ⟨safeMemo_of_termAt hta, (gamma_of_termAt hta).trans hb⟩

theorem key3Pure_eq (cl₁ cl₃ : Nat) :
    key3Pure cl₁ cl₃ =
      ({ st := (stB1Pure cl₁).spqr, coins := tRnd 48 cl₃ } : DY.Spqr.SendKey.SubF DY.Bytes).pack := by
  dsimp only [key3Pure, stB1Pure, DY.Spqr.spqrSend]
  rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.notInit_recv]

theorem cBPure_chainKey_eq (cl₁ : Nat) : (cBPure cl₁).chainKey = stA0Pure.cks := by
  dsimp only [cBPure, stB00Pure, bobSt0, stA0Pure, aliceSt, o1Pure, ratchetState, encSig]
  rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.createChain_comm]

theorem cB'Pure_chainKey_eq (cl₁ : Nat) : (cB'Pure cl₁).chainKey = (stA1Pure cl₁).cks := by
  dsimp only [cB'Pure, stA1Pure, encSt]; rw [cBPure_chainKey_eq]

theorem stA0Pure_rk_comm :
    (createChain o1Pure.keys.rk (dhPk (tRnd 24 32)) (tRnd 10 32)).1 = stA0Pure.rk := by
  dsimp only [stA0Pure, aliceSt]
  exact congrArg Prod.fst
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.createChain_comm o1Pure.keys.rk (tRnd 24 32) (tRnd 10 32))

theorem stB1Pure_rk_eq (cl₁ : Nat) :
    (stB1Pure cl₁).rk = (createChain stA0Pure.rk (dhPk (tRnd 24 32)) dhsBPure).1 := by
  dsimp only [stB1Pure, stB0'Pure, stB00Pure, bobSt0, ratchetState]
  rw [stA0Pure_rk_comm]

theorem stB1Pure_cks_eq (cl₁ : Nat) :
    (stB1Pure cl₁).cks = (createChain stA0Pure.rk (dhPk (tRnd 24 32)) dhsBPure).2 := by
  dsimp only [stB1Pure, stB0'Pure, stB00Pure, bobSt0, ratchetState]
  rw [stA0Pure_rk_comm]

theorem stB1Pure_sid_eq (cl₁ : Nat) : (stB1Pure cl₁).sid = stA0Pure.sid := by
  dsimp only [stB1Pure, stB0'Pure, stB00Pure, bobSt0, stA0Pure, aliceSt, ratchetState, encSig]
  rw [norm_dhPk_eq]

/-! ## 4. Bundled Common, M1, and M2 `TermAt` Records -/

structure CommonNodes (mode : Bool) (S : OpaqueSymbolSemantics) (pts : List DY.Bytes)
    (cl₁ cl₃ : Nat) : Prop where
  b01 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (DY.Libsignal.TripleRatchet.litByte 1) b01Id
  b02 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (DY.Libsignal.TripleRatchet.litByte 2) b02Id
  zero32 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts zeroSalt zero32Id
  wmkInfo1 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 1)) wmkInfo1Id
  wmkInfo2 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 2)) wmkInfo2Id
  wmkInfo3 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
      (DY.Libsignal.TripleRatchet.litByte 3)) wmkInfo3Id
  wrInfo1 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
      (DY.Libsignal.TripleRatchet.litByte 1)) wrInfo1Id
  wrInfo2 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
      (DY.Libsignal.TripleRatchet.litByte 2)) wrInfo2Id
  ikA : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 0 32) ikAId
  ikB : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 5 32) ikBId
  spkB : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 10 32) spkBId
  pqskB : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 16 64) pqskBId
  pk0 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (dhPk (tRnd 0 32)) pk0Id
  pk1 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (dhPk (tRnd 5 32)) pk1Id
  pk2 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (dhPk (tRnd 10 32)) pk2Id
  ik0s : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (serializedIk (dhPk (tRnd 0 32))) ik0sId
  ik1s : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (serializedIk (dhPk (tRnd 5 32))) ik1sId
  pqpk : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (DY.PQKem.kemPk (tRnd 16 64)) pqpkId
  r22 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 22 32) r22Id
  r23 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 23 32) r23Id
  dhsA : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (tRnd 24 32) dhsAId
  ek : TermAt mode S (gClean7003 mode cl₁ cl₃) pts o1Pure.ek ekId
  pk4 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (dhPk (tRnd 24 32)) pk4Id
  ctKem : TermAt mode S (gClean7003 mode cl₁ cl₃) pts o1Pure.ct ctKemId
  rkInit : TermAt mode S (gClean7003 mode cl₁ cl₃) pts o1Pure.keys.rk rkInitId
  ckInit : TermAt mode S (gClean7003 mode cl₁ cl₃) pts o1Pure.keys.ck ckInitId
  pqrInit : TermAt mode S (gClean7003 mode cl₁ cl₃) pts o1Pure.keys.pqr pqrInitId
  sid : TermAt mode S (gClean7003 mode cl₁ cl₃) pts stA0Pure.sid sidId
  stA0Rk : TermAt mode S (gClean7003 mode cl₁ cl₃) pts stA0Pure.rk stA0RkId
  stA0Cks : TermAt mode S (gClean7003 mode cl₁ cl₃) pts stA0Pure.cks stA0CksId
  spqrA0_safe : SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts stA0Pure.spqr
  pqKey1 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts key0Pure pqKey1Id
  pqMsg1 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (pqMsg1Pure cl₁) pqMsg1Id
  seedA0 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (kdfCk stA0Pure.cks).2 seedA0Id
  stA1Cks : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (stA1Pure cl₁).cks stA1CksId
  spqrA1_safe : SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts (stA1Pure cl₁).spqr
  a0Ckey : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk stA0Pure.cks).2).cipherKey a0CkeyId
  a0Mkey : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk stA0Pure.cks).2).macKey a0MkeyId
  a0Iv : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk stA0Pure.cks).2).iv a0IvId
  zA0Ckey : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).cipherKey zA0CkeyId
  zA0Mkey : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey zA0MkeyId
  zA0Iv : TermAt mode S (gClean7003 mode cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).iv zA0IvId
  dhsB : TermAt mode S (gClean7003 mode cl₁ cl₃) pts dhsBPure dhsBId
  pk5 : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (dhPk dhsBPure) pk5Id
  stB1Rk : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (stB1Pure cl₁).rk stB1RkId
  stB1Cks : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (stB1Pure cl₁).cks stB1CksId
  spqrB1_safe : SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts (stB1Pure cl₁).spqr

theorem mkCommonNodes {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat}
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hsem2 : SemPinned2 S cl₁) :
    CommonNodes mode S pts cl₁ cl₃ := by
  let g := gClean7003 mode cl₁ cl₃
  have hb00 : TermAt mode S g pts spqrA2B b00Id :=
    termAt_litByteArray (bs := bytesOf b00Id) (by decide)
  have hb01s : TermAt mode S g pts spqrB2A b01Id :=
    termAt_litByteArray (bs := bytesOf b01Id) (by decide)
  have hb01 : TermAt mode S g pts (DY.Libsignal.TripleRatchet.litByte 1) b01Id :=
    termAt_litByteArray (bs := bytesOf b01Id) (by decide)
  have hb02 : TermAt mode S g pts (DY.Libsignal.TripleRatchet.litByte 2) b02Id :=
    termAt_litByteArray (bs := bytesOf b02Id) (by decide)
  have hb03 : TermAt mode S g pts (DY.Libsignal.TripleRatchet.litByte 3) b03Id :=
    termAt_litByteArray (bs := bytesOf b03Id) (by decide)
  have hb05 : TermAt mode S g pts (DY.Libsignal.TripleRatchet.litByte 5) b05Id :=
    termAt_litByteArray (bs := bytesOf b05Id) (by decide)
  have hu32_1 : TermAt mode S g pts (DY.Spqr.encodeSpqrIndexTerm 1) u32_1Id :=
    termAt_litByteArray (bs := bytesOf u32_1Id) (by decide)
  have hff32 : TermAt mode S g pts DY.Libsignal.PQXDH.discontinuity ff32Id :=
    termAt_litByteArray (bs := bytesOf ff32Id) (by decide)
  have hzero32 : TermAt mode S g pts zeroSalt zero32Id :=
    termAt_litByteArray (bs := bytesOf zero32Id) (by decide)
  have hwrLbl : TermAt mode S g pts (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") wrLblId :=
    termAt_litByteArray (bs := bytesOf wrLblId) (by simp only [String.toUTF8_eq_toByteArray]; decide)
  have hwmkLbl : TermAt mode S g pts (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") wmkLblId :=
    termAt_litByteArray (bs := bytesOf wmkLblId) (by simp only [String.toUTF8_eq_toByteArray]; decide)
  have hpqxdhLbl : TermAt mode S g pts DY.Libsignal.PQXDH.pqxdhLabel pqxdhLblId :=
    termAt_litByteArray (bs := bytesOf pqxdhLblId) (by simp only [String.toUTF8_eq_toByteArray]; decide)
  have hwmk1 := termAt_concat (id := wmkInfo1Id) (hl := hwmkLbl) (hr := hb01)
  have hwmk2 := termAt_concat (id := wmkInfo2Id) (hl := hwmkLbl) (hr := hb02)
  have hwmk3 := termAt_concat (id := wmkInfo3Id) (hl := hwmkLbl) (hr := hb03)
  have hwr1 := termAt_concat (id := wrInfo1Id) (hl := hwrLbl) (hr := hb01)
  have hwr2 := termAt_concat (id := wrInfo2Id) (hl := hwrLbl) (hr := hb02)
  have hpqi1 := termAt_concat (id := pqxdhInfo1Id) (hl := hpqxdhLbl) (hr := hb01)
  have hpqi2 := termAt_concat (id := pqxdhInfo2Id) (hl := hpqxdhLbl) (hr := hb02)
  have hpqi3 := termAt_concat (id := pqxdhInfo3Id) (hl := hpqxdhLbl) (hr := hb03)
  have hikA : TermAt mode S g pts (tRnd 0 32) ikAId := termAt_rand (id := ikAId) (hg := rfl)
  have hikB : TermAt mode S g pts (tRnd 5 32) ikBId := termAt_rand (id := ikBId) (hg := rfl)
  have hspkB : TermAt mode S g pts (tRnd 10 32) spkBId := termAt_rand (id := spkBId) (hg := rfl)
  have hpqskB : TermAt mode S g pts (tRnd 16 64) pqskBId := termAt_rand (id := pqskBId) (hg := rfl)
  have hpk0 := termAt_dhPk (id := pk0Id) (hsk := hikA)
  have hpk1 := termAt_dhPk (id := pk1Id) (hsk := hikB)
  have hpk2 := termAt_dhPk (id := pk2Id) (hsk := hspkB)
  have hik0s := termAt_concat (id := ik0sId) (hl := hb05) (hr := hpk0)
  have hik1s := termAt_concat (id := ik1sId) (hl := hb05) (hr := hpk1)
  obtain ⟨hpqpk_sh, hpqpk_sm⟩ := opaque_kemPk (safeMemo_of_termAt hpqskB)
  have hpqpk : TermAt mode S g pts (DY.PQKem.kemPk (tRnd 16 64)) pqpkId :=
    termAt_of_opaque_pinned (id := pqpkId) (bs := bytesOf pqpkId) (hsh_lit := hpqpk_sh)
      (hgam := by
        rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_kemPk,
            gamma_of_termAt hpqskB, hkpk])
      (hmemo := hpqpk_sm)
  have hr22 : TermAt mode S g pts (tRnd 22 32) r22Id := termAt_rand (id := r22Id) (hg := rfl)
  have hr23 : TermAt mode S g pts (tRnd 23 32) r23Id := termAt_rand (id := r23Id) (hg := rfl)
  have hdhsA : TermAt mode S g pts (tRnd 24 32) dhsAId := termAt_rand (id := dhsAId) (hg := rfl)
  have hek := termAt_dhPk (id := ekId) (hsk := hr22)
  have hpk4 := termAt_dhPk (id := pk4Id) (hsk := hdhsA)
  have hctKem := termAt_kemEncap (id := ctKemId) (hpk := hpqpk) (hent := hr23)
  have hssKem := termAt_kemSS (id := ssKemId) (hpk := hpqpk) (hent := hr23)
  have hdh02 : TermAt mode S g pts (DY.Libsignal.PQXDH.agree (dhPk (tRnd 10 32)) (tRnd 0 32)) dh02Id := by
    unfold DY.Libsignal.PQXDH.agree; rw [norm_dhPk_eq, DY.DiffieHellman.dh_commutes]
    exact termAt_dh_dhPk (id := dh02Id) (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
      (hsk1 := hikA) (hpk1 := hpk0) (hsk2 := hspkB) (hpk2 := hpk2)
  have hdh13 : TermAt mode S g pts (DY.Libsignal.PQXDH.agree (dhPk (tRnd 5 32)) (tRnd 22 32)) dh13Id := by
    unfold DY.Libsignal.PQXDH.agree; rw [norm_dhPk_eq]
    exact termAt_dh_dhPk (id := dh13Id) (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
      (hsk1 := hikB) (hpk1 := hpk1) (hsk2 := hr22) (hpk2 := hek)
  have hdh23 : TermAt mode S g pts (DY.Libsignal.PQXDH.agree (dhPk (tRnd 10 32)) (tRnd 22 32)) dh23Id := by
    unfold DY.Libsignal.PQXDH.agree; rw [norm_dhPk_eq]
    exact termAt_dh_dhPk (id := dh23Id) (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
      (hsk1 := hspkB) (hpk1 := hpk2) (hsk2 := hr22) (hpk2 := hek)
  have hc3 := termAt_concat (id := c3Id) (hl := hdh23) (hr := hssKem)
  have hc2 := termAt_concat (id := c2Id) (hl := hdh13) (hr := hc3)
  have hc1 := termAt_concat (id := c1Id) (hl := hdh02) (hr := hc2)
  have hikm := termAt_concat (id := ikmId) (hl := hff32) (hr := hc1)
  have hprkPq := termAt_kdf (id := prkPqId) (hsalt := hzero32) (hikm := hikm)
  have hrkInit := termAt_kdf (id := rkInitId) (hsalt := hprkPq) (hikm := hpqi1)
  have hpqi2C := termAt_concat (id := pqi2CId) (hl := hrkInit) (hr := hpqi2)
  have hckInit := termAt_kdf (id := ckInitId) (hsalt := hprkPq) (hikm := hpqi2C)
  have hpqi3C := termAt_concat (id := pqi3CId) (hl := hckInit) (hr := hpqi3)
  have hpqrInit : TermAt mode S g pts o1Pure.keys.pqr pqrInitId :=
    termAt_kdf (id := pqrInitId) (hsalt := hprkPq) (hikm := hpqi3C)
  have hsid := termAt_concat (id := sidId) (hl := hpk4) (hr := hrkInit)
  obtain ⟨hstA0Rk, hstA0Cks⟩ := ta_createChain
    (dhId := dh24Id) (prk := prkAId) (rkOut := stA0RkId) (wi2 := wri2CAId) (ckOut := stA0CksId)
    hrkInit hspkB hpk2 hdhsA hpk4 hwr1 hwr2 (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
  have hspqrA0 : SafeMemo mode S g pts stA0Pure.spqr :=
    safeMemo_spqrInit (safeMemo_of_termAt hpqrInit) (safeMemo_of_termAt hb00)
  obtain ⟨hpqKey1_sh, hpqKey1_sm, _⟩ := opaque_spqrChainKey
    (safeMemo_of_termAt hpqrInit) (safeMemo_of_termAt hb00) (safeMemo_of_termAt hu32_1)
  have hpqKey1 : TermAt mode S g pts key0Pure pqKey1Id :=
    termAt_of_opaque_pinned (id := pqKey1Id) (bs := bytesOf pqKey1Id) (hsh_lit := hpqKey1_sh)
      (hgam := by
        dsimp only [key0Pure]
        rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrChainKey,
            gamma_of_termAt hpqrInit, gamma_of_termAt hb00, gamma_of_termAt hu32_1]
        have hp1 : bytesOf pqrInitId = pqrBytes := by decide
        have hp2 : bytesOf b00Id = [0#8] := by decide
        have hp3 : bytesOf u32_1Id = [1#8, 0#8, 0#8, 0#8] := by decide
        have hp4 : salt1Bytes = bytesOf pqKey1Id := by decide
        rw [hp1, hp2, hp3, hsem2.2.1, hp4])
      (hmemo := hpqKey1_sm)
  obtain ⟨hc1_safe, hc1_gam⟩ := coins32_safe_and_gamma (mode := mode) (S := S) (pts := pts)
    (cl₃ := cl₃) hsem2.le64
  obtain ⟨hpqMsg1_sh, hpqMsg1_sm⟩ := opaque_spqrSendMsg hspqrA0 hc1_safe
  have hpqMsg1 : TermAt mode S g pts (pqMsg1Pure cl₁) pqMsg1Id :=
    termAt_of_opaque_pinned (id := pqMsg1Id) (bs := bytesOf pqMsg1Id) (hsh_lit := hpqMsg1_sh)
      (hgam := by
        change gamma compI7003 S g (tSSendM stA0Pure.spqr (tRnd 32 cl₁)) = bytesOf pqMsg1Id
        dsimp only [tSSendM, stA0Pure, aliceSt]
        rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrSendMsg,
            Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrInit,
            gamma_of_termAt hpqrInit, gamma_of_termAt hb00, hc1_gam]
        have hp1 : bytesOf pqrInitId = pqrBytes := by decide
        have hp2 : bytesOf b00Id = [0#8] := by decide
        have hp4 : pqMsg1Bytes = bytesOf pqMsg1Id := by decide
        rw [hp1, hp2, hsem2.2.2, hp4])
      (hmemo := hpqMsg1_sm)
  have hseedA0 := termAt_kdf (id := seedA0Id) (hsalt := hstA0Cks) (hikm := hb01)
  have hstA1Cks := termAt_kdf (id := stA1CksId) (hsalt := hstA0Cks) (hikm := hb02)
  have hspqrA1 : SafeMemo mode S g pts (stA1Pure cl₁).spqr :=
    safeMemo_spqrSendState hspqrA0 hc1_safe
  obtain ⟨ha0Ck, ha0Mk, ha0Iv⟩ := ta_trMsgKeys
    (prk := a0PrkId) (ck := a0CkeyId) (wi2 := a0Wmki2Id) (mk := a0MkeyId) (wi3 := a0Wmki3Id)
    (iv := a0IvId) hpqKey1 hseedA0 hwmk1 hwmk2 hwmk3
  obtain ⟨hzA0Ck, hzA0Mk, hzA0Iv⟩ := ta_trMsgKeys
    (prk := zA0PrkId) (ck := zA0CkeyId) (wi2 := zA0Wmki2Id) (mk := zA0MkeyId) (wi3 := zA0Wmki3Id)
    (iv := zA0IvId) hzero32 hseedA0 hwmk1 hwmk2 hwmk3
  have hdhsB : TermAt mode S g pts dhsBPure dhsBId := termAt_rand (id := dhsBId) (hg := rfl)
  have hpk5 := termAt_dhPk (id := pk5Id) (hsk := hdhsB)
  obtain ⟨hstB1Rk_raw, hstB1Cks_raw⟩ := ta_createChain
    (dhId := dh45Id) (prk := prkBId) (rkOut := stB1RkId) (wi2 := wri2CBId) (ckOut := stB1CksId)
    hstA0Rk hdhsA hpk4 hdhsB hpk5 hwr1 hwr2 (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
  have hspqrB1 : SafeMemo mode S g pts (stB1Pure cl₁).spqr :=
    safeMemo_spqrRecvState
      (safeMemo_spqrInit (safeMemo_of_termAt hpqrInit) (safeMemo_of_termAt hb01s))
      (safeMemo_of_termAt hpqMsg1)
  exact {
    b01 := hb01, b02 := hb02, zero32 := hzero32,
    wmkInfo1 := hwmk1, wmkInfo2 := hwmk2, wmkInfo3 := hwmk3, wrInfo1 := hwr1, wrInfo2 := hwr2,
    ikA := hikA, ikB := hikB, spkB := hspkB, pqskB := hpqskB,
    pk0 := hpk0, pk1 := hpk1, pk2 := hpk2, ik0s := hik0s, ik1s := hik1s, pqpk := hpqpk,
    r22 := hr22, r23 := hr23, dhsA := hdhsA, ek := hek, pk4 := hpk4, ctKem := hctKem,
    rkInit := hrkInit, ckInit := hckInit, pqrInit := hpqrInit, sid := hsid,
    stA0Rk := hstA0Rk, stA0Cks := hstA0Cks, spqrA0_safe := hspqrA0,
    pqKey1 := hpqKey1, pqMsg1 := hpqMsg1, seedA0 := hseedA0, stA1Cks := hstA1Cks,
    spqrA1_safe := hspqrA1,
    a0Ckey := ha0Ck, a0Mkey := ha0Mk, a0Iv := ha0Iv,
    zA0Ckey := hzA0Ck, zA0Mkey := hzA0Mk, zA0Iv := hzA0Iv,
    dhsB := hdhsB, pk5 := hpk5,
    stB1Rk := termAt_congr (stB1Pure_rk_eq cl₁) hstB1Rk_raw,
    stB1Cks := termAt_congr (stB1Pure_cks_eq cl₁) hstB1Cks_raw,
    spqrB1_safe := hspqrB1
  }

structure M1Nodes (S : OpaqueSymbolSemantics) (pts : List DY.Bytes) (cl₁ : Nat) : Prop where
  ct1 : TermAt false S (gClean7003 false cl₁ 0) pts (encSig1Pure cl₁).2.ciphertext ct1M1Id
  wire1 : TermAt false S (gClean7003 false cl₁ 0) pts (encSig1Pure cl₁).2.wire wire1M1Id
  mac1 : TermAt false S (gClean7003 false cl₁ 0) pts (encSig1Pure cl₁).2.mac mac1M1Id
  out1 : TermAt false S (gClean7003 false cl₁ 0) pts (encMsg1Pure cl₁) out1M1Id
  zMac1 : TermAt false S (gClean7003 false cl₁ 0) pts
    (computeMac (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey
      stA0Pure.myIk stA0Pure.peerIk (encSig1Pure cl₁).2.wire) zMac1M1Id
  ckAA0 : TermAt false S (gClean7003 false cl₁ 0) pts
    (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2 ckAA0Id
  seedAA0 : TermAt false S (gClean7003 false cl₁ 0) pts
    (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2 seedAA0Id
  ckAA1 : TermAt false S (gClean7003 false cl₁ 0) pts
    (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).1 ckAA1Id
  zAACkey : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).cipherKey zAACkeyId
  zAAMkey : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).macKey zAAMkeyId
  zAAIv : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).iv zAAIvId
  zAAMac : TermAt false S (gClean7003 false cl₁ 0) pts
    (computeMac
      (trMsgKeys DY.Spqr.zeroKey
        (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).macKey
      stA0Pure.peerIk stA0Pure.myIk (encSig1Pure cl₁).2.wire) zAAMacId
  p1AACkey : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).cipherKey p1AACkeyId
  p1AAMkey : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).macKey p1AAMkeyId
  p1AAIv : TermAt false S (gClean7003 false cl₁ 0) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).iv p1AAIvId
  p1AAMac : TermAt false S (gClean7003 false cl₁ 0) pts
    (computeMac
      (trMsgKeys key0Pure
        (kdfCk (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2).2).macKey
      stA0Pure.peerIk stA0Pure.myIk (encSig1Pure cl₁).2.wire) p1AAMacId

theorem mkM1Nodes {S : OpaqueSymbolSemantics} {pts : List DY.Bytes} {cl₁ : Nat}
    (cn : CommonNodes false S pts cl₁ 0) (hpt1 : tRnd 31 32 ∈ pts) :
    M1Nodes S pts cl₁ := by
  let g := gClean7003 false cl₁ 0
  have hct1 : TermAt false S g pts (encSig1Pure cl₁).2.ciphertext ct1M1Id :=
    termAt_symEncPt (id := ct1M1Id) (hkey := cn.a0Ckey) (hiv := cn.a0Iv)
      (hpt_mem := hpt1) (hpt_bs := Or.inl rfl) (hg_pt := rfl)
  have hwire1 : TermAt false S g pts (encSig1Pure cl₁).2.wire wire1M1Id :=
    termAt_trWire (id := wire1M1Id) (addr := addr1Bytes) (useEv4Var := false)
      (hrk := cn.pk4) (hct := hct1) (hpq := cn.pqMsg1)
      (haddr := by dsimp only [g, gClean7003, encSig1Pure, encSig, trHonestWireMsg, stA0Pure, aliceSt, trWireEvOf]; rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
  have hmiR1 := termAt_concat (id := miR1M1Id) (hl := cn.ik1s) (hr := hwire1)
  have hmi1 := termAt_concat (id := mi1M1Id) (hl := cn.ik0s) (hr := hmiR1)
  have hmac1 := ta_macFromMi (fm := fmac1M1Id) (mac := mac1M1Id) cn.a0Mkey hmi1
  have hout1 : TermAt false S g pts (encMsg1Pure cl₁) out1M1Id :=
    termAt_concat (id := out1M1Id) (hl := hwire1) (hr := hmac1)
  have hzMac1 := ta_macFromMi (fm := zFmac1M1Id) (mac := zMac1M1Id) cn.zA0Mkey hmi1
  obtain ⟨_, hckAA0⟩ := ta_createChain
    (dhId := dh44Id) (prk := prkAAId) (rkOut := rkAAId) (wi2 := wri2CAAId) (ckOut := ckAA0Id)
    cn.stA0Rk cn.dhsA cn.pk4 cn.dhsA cn.pk4 cn.wrInfo1 cn.wrInfo2
    (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
  have hseedAA0 := termAt_kdf (id := seedAA0Id) (hsalt := hckAA0) (hikm := cn.b01)
  have hckAA1 := termAt_kdf (id := ckAA1Id) (hsalt := hckAA0) (hikm := cn.b02)
  have hmiRAA := termAt_concat (id := miRAAId) (hl := cn.ik0s) (hr := hwire1)
  have hmiAA := termAt_concat (id := miAAId) (hl := cn.ik1s) (hr := hmiRAA)
  obtain ⟨hzAACk, hzAAMk, hzAAIv⟩ := ta_trMsgKeys
    (prk := zAAPrkId) (ck := zAACkeyId) (wi2 := zAAWmki2Id) (mk := zAAMkeyId) (wi3 := zAAWmki3Id)
    (iv := zAAIvId) cn.zero32 hseedAA0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hzAAMac := ta_macFromMi (fm := zAAFmacId) (mac := zAAMacId) hzAAMk hmiAA
  obtain ⟨hp1AACk, hp1AAMk, hp1AAIv⟩ := ta_trMsgKeys
    (prk := p1AAPrkId) (ck := p1AACkeyId) (wi2 := p1AAWmki2Id) (mk := p1AAMkeyId)
    (wi3 := p1AAWmki3Id) (iv := p1AAIvId) cn.pqKey1 hseedAA0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hp1AAMac := ta_macFromMi (fm := p1AAFmacId) (mac := p1AAMacId) hp1AAMk hmiAA
  exact {
    ct1 := hct1, wire1 := hwire1, mac1 := hmac1, out1 := hout1, zMac1 := hzMac1,
    ckAA0 := hckAA0, seedAA0 := hseedAA0, ckAA1 := hckAA1,
    zAACkey := hzAACk, zAAMkey := hzAAMk, zAAIv := hzAAIv, zAAMac := hzAAMac,
    p1AACkey := hp1AACk, p1AAMkey := hp1AAMk, p1AAIv := hp1AAIv, p1AAMac := hp1AAMac
  }

structure M2Nodes (S : OpaqueSymbolSemantics) (pts : List DY.Bytes) (cl₁ cl₃ : Nat) : Prop where
  ct1 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig1Pure cl₁).2.ciphertext ct1M2Id
  wire1 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig1Pure cl₁).2.wire wire1M2Id
  mac1 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig1Pure cl₁).2.mac mac1M2Id
  out1 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encMsg1Pure cl₁) out1M2Id
  zMac1 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey
      stA0Pure.myIk stA0Pure.peerIk (encSig1Pure cl₁).2.wire) zMac1M2Id
  pqKey3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (key3Pure cl₁ cl₃) pqKey3Id
  pqMsg3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (pqMsg3Pure cl₁ cl₃) pqMsg3Id
  seedB0 : TermAt true S (gClean7003 true cl₁ cl₃) pts (kdfCk (stB1Pure cl₁).cks).2 seedB0Id
  stB2Cks : TermAt true S (gClean7003 true cl₁ cl₃) pts (stB2Pure cl₁ cl₃).cks stB2CksId
  spqrB2_safe : SafeMemo true S (gClean7003 true cl₁ cl₃) pts (stB2Pure cl₁ cl₃).spqr
  b0Ckey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃) (kdfCk (stB1Pure cl₁).cks).2).cipherKey b0CkeyId
  b0Mkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃) (kdfCk (stB1Pure cl₁).cks).2).macKey b0MkeyId
  b0Iv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃) (kdfCk (stB1Pure cl₁).cks).2).iv b0IvId
  ct3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig3Pure cl₁ cl₃).ciphertext ct3M2Id
  wire3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig3Pure cl₁ cl₃).wire wire3M2Id
  mac3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encSig3Pure cl₁ cl₃).mac mac3M2Id
  out3 : TermAt true S (gClean7003 true cl₁ cl₃) pts (encMsg3Pure cl₁ cl₃) out3M2Id
  wire4Mut : TermAt true S (gClean7003 true cl₁ cl₃) pts (wire4MutPure cl₁ cl₃) wire4MutId
  out4Mut : TermAt true S (gClean7003 true cl₁ cl₃) pts (tMut4M2Pure cl₁ cl₃) out4MutId
  p3B0Mac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac (trMsgKeys (key3Pure cl₁ cl₃) (kdfCk (stB1Pure cl₁).cks).2).macKey
      stA0Pure.peerIk stA0Pure.myIk (wire4MutPure cl₁ cl₃)) p3B0Mac4Id
  zB0Ckey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk (stB1Pure cl₁).cks).2).cipherKey zB0CkeyId
  zB0Mkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk (stB1Pure cl₁).cks).2).macKey zB0MkeyId
  zB0Iv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey (kdfCk (stB1Pure cl₁).cks).2).iv zB0IvId
  zB0Mac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac (trMsgKeys DY.Spqr.zeroKey (kdfCk (stB1Pure cl₁).cks).2).macKey
      stA0Pure.peerIk stA0Pure.myIk (wire4MutPure cl₁ cl₃)) zB0Mac4Id
  p1B0Ckey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk (stB1Pure cl₁).cks).2).cipherKey p1B0CkeyId
  p1B0Mkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk (stB1Pure cl₁).cks).2).macKey p1B0MkeyId
  p1B0Iv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure (kdfCk (stB1Pure cl₁).cks).2).iv p1B0IvId
  p1B0Mac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac (trMsgKeys key0Pure (kdfCk (stB1Pure cl₁).cks).2).macKey
      stA0Pure.peerIk stA0Pure.myIk (wire4MutPure cl₁ cl₃)) p1B0Mac4Id
  ckBB0 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2 ckBB0Id
  seedBB0 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2 seedBB0Id
  ckBB1 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).1 ckBB1Id
  zBBCkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).cipherKey zBBCkeyId
  zBBMkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey zBBMkeyId
  zBBIv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys DY.Spqr.zeroKey
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).iv zBBIvId
  zBBMac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac
      (trMsgKeys DY.Spqr.zeroKey
        (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey
      stA0Pure.myIk stA0Pure.peerIk (wire4MutPure cl₁ cl₃)) zBBMac4Id
  p1BBCkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).cipherKey p1BBCkeyId
  p1BBMkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey p1BBMkeyId
  p1BBIv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys key0Pure
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).iv p1BBIvId
  p1BBMac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac
      (trMsgKeys key0Pure
        (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey
      stA0Pure.myIk stA0Pure.peerIk (wire4MutPure cl₁ cl₃)) p1BBMac4Id
  p3BBCkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃)
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).cipherKey p3BBCkeyId
  p3BBMkey : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃)
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey p3BBMkeyId
  p3BBIv : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (trMsgKeys (key3Pure cl₁ cl₃)
      (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).iv p3BBIvId
  p3BBMac4 : TermAt true S (gClean7003 true cl₁ cl₃) pts
    (computeMac
      (trMsgKeys (key3Pure cl₁ cl₃)
        (kdfCk (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2).2).macKey
      stA0Pure.myIk stA0Pure.peerIk (wire4MutPure cl₁ cl₃)) p3BBMac4Id

theorem mkM2Nodes {S : OpaqueSymbolSemantics} {pts : List DY.Bytes} {cl₁ cl₃ : Nat}
    (cn : CommonNodes true S pts cl₁ cl₃)
    (hsem4 : SemPinned4_M2 S cl₁ cl₃)
    (hpt1 : tRnd 31 32 ∈ pts) (hpt3 : tRnd 47 32 ∈ pts) :
    M2Nodes S pts cl₁ cl₃ := by
  let g := gClean7003 true cl₁ cl₃
  have hct1 : TermAt true S g pts (encSig1Pure cl₁).2.ciphertext ct1M2Id :=
    termAt_symEncPt (id := ct1M2Id) (hkey := cn.a0Ckey) (hiv := cn.a0Iv)
      (hpt_mem := hpt1) (hpt_bs := Or.inr (Or.inl rfl)) (hg_pt := rfl)
  have hwire1 : TermAt true S g pts (encSig1Pure cl₁).2.wire wire1M2Id :=
    termAt_trWire (id := wire1M2Id) (addr := addr1Bytes) (useEv4Var := false)
      (hrk := cn.pk4) (hct := hct1) (hpq := cn.pqMsg1)
      (haddr := by dsimp only [g, gClean7003, encSig1Pure, encSig, trHonestWireMsg, stA0Pure, aliceSt, trWireEvOf]; rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
  have hmiR1 := termAt_concat (id := miR1M2Id) (hl := cn.ik1s) (hr := hwire1)
  have hmi1 := termAt_concat (id := mi1M2Id) (hl := cn.ik0s) (hr := hmiR1)
  have hmac1 := ta_macFromMi (fm := fmac1M2Id) (mac := mac1M2Id) cn.a0Mkey hmi1
  have hout1 : TermAt true S g pts (encMsg1Pure cl₁) out1M2Id :=
    termAt_concat (id := out1M2Id) (hl := hwire1) (hr := hmac1)
  have hzMac1 := ta_macFromMi (fm := zFmac1M2Id) (mac := zMac1M2Id) cn.zA0Mkey hmi1
  obtain ⟨hc3_safe, hc3_gam⟩ := coins48_safe_and_gamma (mode := true) (S := S) (pts := pts)
    (cl₁ := cl₁) hsem4.le64
  have hb01s : TermAt true S g pts spqrB2A b01Id :=
    termAt_litByteArray (bs := bytesOf b01Id) (by decide)
  have hg_spqrB1 : gamma compI7003 S g (stB1Pure cl₁).spqr =
      S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes := by
    dsimp only [stB1Pure, recvSt]
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrRecvState,
        Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrInit,
        gamma_of_termAt cn.pqrInit, gamma_of_termAt hb01s, gamma_of_termAt cn.pqMsg1]
    have hp1 : bytesOf pqrInitId = pqrBytes := by decide
    have hp2 : bytesOf b01Id = [1#8] := by decide
    have hp3 : bytesOf pqMsg1Id = pqMsg1Bytes := by decide
    rw [hp1, hp2, hp3]
  obtain ⟨hpqKey3_sh, hpqKey3_sm⟩ := opaque_spqrSendKey cn.spqrB1_safe hc3_safe
  have hpqKey3 : TermAt true S g pts (key3Pure cl₁ cl₃) pqKey3Id :=
    termAt_congr (key3Pure_eq cl₁ cl₃) <|
      termAt_of_opaque_pinned (id := pqKey3Id) (bs := bytesOf pqKey3Id) (hsh_lit := hpqKey3_sh)
        (hgam := by
          rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrSendKey,
              hg_spqrB1, hc3_gam, hsem4.2.2.1]
          decide)
        (hmemo := hpqKey3_sm)
  obtain ⟨hpqMsg3_sh, hpqMsg3_sm⟩ := opaque_spqrSendMsg cn.spqrB1_safe hc3_safe
  have hpqMsg3 : TermAt true S g pts (pqMsg3Pure cl₁ cl₃) pqMsg3Id :=
    termAt_of_opaque_pinned (id := pqMsg3Id) (bs := bytesOf pqMsg3Id) (hsh_lit := hpqMsg3_sh)
      (hgam := by
        change gamma compI7003 S g (tSSendM (stB1Pure cl₁).spqr (tRnd 48 cl₃)) = bytesOf pqMsg3Id
        dsimp only [tSSendM]
        rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_spqrSendMsg,
            hg_spqrB1, hc3_gam, hsem4.2.2.2]
        decide)
      (hmemo := hpqMsg3_sm)
  have hseedB0 := termAt_kdf (id := seedB0Id) (hsalt := cn.stB1Cks) (hikm := cn.b01)
  have hstB2Cks := termAt_kdf (id := stB2CksId) (hsalt := cn.stB1Cks) (hikm := cn.b02)
  have hspqrB2 : SafeMemo true S g pts (stB2Pure cl₁ cl₃).spqr :=
    safeMemo_spqrSendState cn.spqrB1_safe hc3_safe
  obtain ⟨hb0Ck, hb0Mk, hb0Iv⟩ := ta_trMsgKeys
    (prk := b0PrkId) (ck := b0CkeyId) (wi2 := b0Wmki2Id) (mk := b0MkeyId) (wi3 := b0Wmki3Id)
    (iv := b0IvId) hpqKey3 hseedB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hct3 : TermAt true S g pts (encSig3Pure cl₁ cl₃).ciphertext ct3M2Id :=
    termAt_symEncPt (id := ct3M2Id) (hkey := hb0Ck) (hiv := hb0Iv)
      (hpt_mem := hpt3) (hpt_bs := Or.inr (Or.inr rfl)) (hg_pt := rfl)
  have hwire3_eq : (encSig3Pure cl₁ cl₃).wire =
      tTrW 4 (dhPk dhsBPure) 0 0 (encSig3Pure cl₁ cl₃).ciphertext
        (pqMsg3Pure cl₁ cl₃) (trWireEvOf false) := rfl
  have hwire3 : TermAt true S g pts (encSig3Pure cl₁ cl₃).wire wire3M2Id :=
    termAt_congr hwire3_eq <|
      termAt_trWire (id := wire3M2Id) (addr := []) (useEv4Var := false)
        (hrk := cn.pk5) (hct := hct3) (hpq := hpqMsg3)
        (haddr := by dsimp only [g, gClean7003, dhsBPure, trWireEvOf]; rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
  have hmiR3 := termAt_concat (id := miR3M2Id) (hl := cn.ik0s) (hr := hwire3)
  have hmi3 := termAt_concat (id := mi3M2Id) (hl := cn.ik1s) (hr := hmiR3)
  have hmac3 := ta_macFromMi (fm := fmac3M2Id) (mac := mac3M2Id) hb0Mk hmi3
  have hout3 : TermAt true S g pts (encMsg3Pure cl₁ cl₃) out3M2Id :=
    termAt_concat (id := out3M2Id) (hl := hwire3) (hr := hmac3)
  have hwire4 : TermAt true S g pts (wire4MutPure cl₁ cl₃) wire4MutId :=
    termAt_trWire (id := wire4MutId) (addr := []) (useEv4Var := true)
      (hrk := cn.pk5) (hct := hct3) (hpq := hpqMsg3)
      (haddr := by dsimp only [g, gClean7003, dhsBPure, trWireEvOf]; rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
  have hout4 : TermAt true S g pts (tMut4M2Pure cl₁ cl₃) out4MutId :=
    termAt_concat (id := out4MutId) (hl := hwire4) (hr := hmac3)
  have hmiR4AB := termAt_concat (id := miR4ABId) (hl := cn.ik0s) (hr := hwire4)
  have hmi4AB := termAt_concat (id := mi4ABId) (hl := cn.ik1s) (hr := hmiR4AB)
  have hp3B0Mac4 := ta_macFromMi (fm := p3B0Fmac4Id) (mac := p3B0Mac4Id) hb0Mk hmi4AB
  obtain ⟨hzB0Ck, hzB0Mk, hzB0Iv⟩ := ta_trMsgKeys
    (prk := zB0PrkId) (ck := zB0CkeyId) (wi2 := zB0Wmki2Id) (mk := zB0MkeyId)
    (wi3 := zB0Wmki3Id) (iv := zB0IvId) cn.zero32 hseedB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hzB0Mac4 := ta_macFromMi (fm := zB0Fmac4Id) (mac := zB0Mac4Id) hzB0Mk hmi4AB
  obtain ⟨hp1B0Ck, hp1B0Mk, hp1B0Iv⟩ := ta_trMsgKeys
    (prk := p1B0PrkId) (ck := p1B0CkeyId) (wi2 := p1B0Wmki2Id) (mk := p1B0MkeyId)
    (wi3 := p1B0Wmki3Id) (iv := p1B0IvId) cn.pqKey1 hseedB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hp1B0Mac4 := ta_macFromMi (fm := p1B0Fmac4Id) (mac := p1B0Mac4Id) hp1B0Mk hmi4AB
  obtain ⟨_, hckBB0⟩ := ta_createChain
    (dhId := dh55Id) (prk := prkBBId) (rkOut := rkBBId) (wi2 := wri2CBBId) (ckOut := ckBB0Id)
    cn.stB1Rk cn.dhsB cn.pk5 cn.dhsB cn.pk5 cn.wrInfo1 cn.wrInfo2
    (hsh1 := shapeOf_rand) (hsh2 := shapeOf_rand)
  have hseedBB0 := termAt_kdf (id := seedBB0Id) (hsalt := hckBB0) (hikm := cn.b01)
  have hckBB1 := termAt_kdf (id := ckBB1Id) (hsalt := hckBB0) (hikm := cn.b02)
  have hmiR4BB := termAt_concat (id := miR4BBId) (hl := cn.ik1s) (hr := hwire4)
  have hmi4BB := termAt_concat (id := mi4BBId) (hl := cn.ik0s) (hr := hmiR4BB)
  obtain ⟨hzBBCk, hzBBMk, hzBBIv⟩ := ta_trMsgKeys
    (prk := zBBPrkId) (ck := zBBCkeyId) (wi2 := zBBWmki2Id) (mk := zBBMkeyId)
    (wi3 := zBBWmki3Id) (iv := zBBIvId) cn.zero32 hseedBB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hzBBMac4 := ta_macFromMi (fm := zBBFmac4Id) (mac := zBBMac4Id) hzBBMk hmi4BB
  obtain ⟨hp1BBCk, hp1BBMk, hp1BBIv⟩ := ta_trMsgKeys
    (prk := p1BBPrkId) (ck := p1BBCkeyId) (wi2 := p1BBWmki2Id) (mk := p1BBMkeyId)
    (wi3 := p1BBWmki3Id) (iv := p1BBIvId) cn.pqKey1 hseedBB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hp1BBMac4 := ta_macFromMi (fm := p1BBFmac4Id) (mac := p1BBMac4Id) hp1BBMk hmi4BB
  obtain ⟨hp3BBCk, hp3BBMk, hp3BBIv⟩ := ta_trMsgKeys
    (prk := p3BBPrkId) (ck := p3BBCkeyId) (wi2 := p3BBWmki2Id) (mk := p3BBMkeyId)
    (wi3 := p3BBWmki3Id) (iv := p3BBIvId) hpqKey3 hseedBB0 cn.wmkInfo1 cn.wmkInfo2 cn.wmkInfo3
  have hp3BBMac4 := ta_macFromMi (fm := p3BBFmac4Id) (mac := p3BBMac4Id) hp3BBMk hmi4BB
  exact {
    ct1 := hct1, wire1 := hwire1, mac1 := hmac1, out1 := hout1, zMac1 := hzMac1,
    pqKey3 := hpqKey3, pqMsg3 := hpqMsg3, seedB0 := hseedB0, stB2Cks := hstB2Cks,
    spqrB2_safe := hspqrB2, b0Ckey := hb0Ck, b0Mkey := hb0Mk, b0Iv := hb0Iv,
    ct3 := hct3, wire3 := hwire3, mac3 := hmac3, out3 := hout3,
    wire4Mut := hwire4, out4Mut := hout4, p3B0Mac4 := hp3B0Mac4,
    zB0Ckey := hzB0Ck, zB0Mkey := hzB0Mk, zB0Iv := hzB0Iv, zB0Mac4 := hzB0Mac4,
    p1B0Ckey := hp1B0Ck, p1B0Mkey := hp1B0Mk, p1B0Iv := hp1B0Iv, p1B0Mac4 := hp1B0Mac4,
    ckBB0 := hckBB0, seedBB0 := hseedBB0, ckBB1 := hckBB1,
    zBBCkey := hzBBCk, zBBMkey := hzBBMk, zBBIv := hzBBIv, zBBMac4 := hzBBMac4,
    p1BBCkey := hp1BBCk, p1BBMkey := hp1BBMk, p1BBIv := hp1BBIv, p1BBMac4 := hp1BBMac4,
    p3BBCkey := hp3BBCk, p3BBMkey := hp3BBMk, p3BBIv := hp3BBIv, p3BBMac4 := hp3BBMac4
  }

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
