/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ReceiveRatchetCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen

/-!
# Verification of `TripleRatchet::apply_to_session_state`

Proves that `<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state` (`0x1cbf4`)
satisfies `trApplySpec` and `trApplySpecX`, both in-image and under `[LibsignalPlacement]`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

open CryptoVerification.InImageLift
/-! ## Drop-glue callee hypotheses for `TR::apply_to_session_state` -/

namespace ReceiveRatchetApply

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``vecGhostAt, #[2]), (``vecU8At, #[1]), (``vecAt, #[5]), (``vecBuf, #[5, 6]), (``vecU8Buf, #[1, 2]), (``optSenderChainAt, #[1]), (``optTailVecAt, #[2]), (``sessionStateAt, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

-- Instruction decode lemmas for `TR::apply_to_session_state` (`0x1cbf4`).
theorem sp_sub_224_orr_4 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    (sp - 224#64) ||| 4#64 = sp - 220#64 := by
  bv_kernel

theorem deserialize_ok_bytes_ne_nil {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : bs ≠ [] := by
  rintro rfl
  simp [PublicKey.deserialize] at h

open CryptoGames.HMAC in
theorem deserialize_serialize_pk (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

theorem serialize_pk_length (pk : PublicKey) : pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

theorem optSenderChainBytes_length (o : Option SenderChain) {pad : List (BitVec 8)}
    (hpad : pad.length = 100) :
    (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none =>
    simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    simp [optSenderChainBytes, senderChainBytes, chainKeyBytes, CryptoGames.HMAC.keyToBytes32,
      leBytes, sc.ratchetKey.publicKey.bytes.toList_length,
      sc.ratchetKey.privateKey.bytes.toList_length]

theorem exists_unpack64_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) :
    ∃ w0 w1 w2 w3 w4 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 8 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h1
  refine ⟨w0, w1, w2, w3, w4, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0, hw4, ← pointsTo64_eq_pointsToBytes]
  simp only [sepConj_assoc]

theorem exists_unpack64_of_length_104 {bs : List (BitVec 8)} (h : bs.length = 104) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
            ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
            ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
            ((a + 96#64) ↦₆₄ w12)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 64).length = 40 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, w12, hp2⟩ := exists_unpack64_of_length_40 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, fun a => ?_⟩
  have hsplit1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  have hsplit2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
    have hd : (bs.drop 32).drop 32 = bs.drop 64 := by simp [List.drop_drop]
    rw [← hd, List.take_append_drop]
  rw [hsplit1, pointsToBytes_append, h0, hsplit2, pointsToBytes_append, h1, hp0, hp1, hp2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem leBytes_4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem optSenderChainBytes_none_eq (a : BitVec 64) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes none pad) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦ₛ pad) := by
  unfold optSenderChainBytes
  have h0 : leBytes 4 0 = unpack32 0#32 := rfl
  rw [h0, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes]

theorem optSenderChainBytes_some_eq (a : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes (some sc) pad) =
      (a ↦₃₂ 1#32) ∗
        ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
        ((a + 36#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
        ((a + 68#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
        ((a + 100#64) ↦₃₂ sc.chainKey.index) := by
  dsimp only [optSenderChainBytes, senderChainBytes, chainKeyBytes]
  have h1 : leBytes 4 1 = unpack32 1#32 := rfl
  have hpk : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.toList_length
  have hsk : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.toList_length
  have hck : (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  rw [h1, leBytes_4_eq_unpack32]
  simp only [List.append_assoc, pointsToBytes_append, unpack32_length, hpk, hsk, hck,
    ← pointsTo32_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

/-! ## Stack layout helpers -/

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

theorem stackAt_sub_split (sp : BitVec 64) (n k : Nat) (h : k ≤ n) (hn : n < 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  simp only [stackAt]
  refine memRegion_split' (by omega) ?_ (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt hn
  have h2 : (n - k) % 2 ^ 64 = n - k := Nat.mod_eq_of_lt (by omega)
  have h3 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

@[expose] def trApplySavedRegs (sp : BitVec 64) (s : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s.readReg64 .lr) ∗
  ((sp - 80#64) ↦₆₄ s.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s.readReg64 .x27) ∗
  ((sp - 64#64) ↦₆₄ s.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)

theorem stackAt_trApply (sp : BitVec 64) :
    stackAt sp trApplyStack =
      stackAt (sp - 224#64) extHookStack ∗
      (∃∗ u0 : BitVec 64, (sp - 224#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp - 216#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (sp - 208#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (sp - 200#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (sp - 192#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp - 184#64) ↦₆₄ u5) ∗
      (∃∗ u6 : BitVec 64, (sp - 176#64) ↦₆₄ u6) ∗
      (∃∗ u7 : BitVec 64, (sp - 168#64) ↦₆₄ u7) ∗
      (∃∗ u8 : BitVec 64, (sp - 160#64) ↦₆₄ u8) ∗
      (∃∗ u9 : BitVec 64, (sp - 152#64) ↦₆₄ u9) ∗
      (∃∗ u10 : BitVec 64, (sp - 144#64) ↦₆₄ u10) ∗
      (∃∗ u11 : BitVec 64, (sp - 136#64) ↦₆₄ u11) ∗
      (∃∗ u12 : BitVec 64, (sp - 128#64) ↦₆₄ u12) ∗
      memRegion (sp - 120#64) 24 ∗
      (∃∗ r0 : BitVec 64, (sp - 96#64) ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (sp - 88#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (sp - 80#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (sp - 72#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (sp - 64#64) ↦₆₄ r4) ∗
      (∃∗ r5 : BitVec 64, (sp - 56#64) ↦₆₄ r5) ∗
      (∃∗ r6 : BitVec 64, (sp - 48#64) ↦₆₄ r6) ∗
      (∃∗ r7 : BitVec 64, (sp - 40#64) ↦₆₄ r7) ∗
      (∃∗ r8 : BitVec 64, (sp - 32#64) ↦₆₄ r8) ∗
      (∃∗ r9 : BitVec 64, (sp - 24#64) ↦₆₄ r9) ∗
      (∃∗ r10 : BitVec 64, (sp - 16#64) ↦₆₄ r10) ∗
      (∃∗ r11 : BitVec 64, (sp - 8#64) ↦₆₄ r11) := by
  simp only [stackAt, trApplyStack, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

theorem stackAt_trApply_fold (sp : BitVec 64) (s0 : State) :
    (stackAt (sp - 224#64) extHookStack ∗
      memRegion (sp - 224#64) 104 ∗
      memRegion (sp - 120#64) 24 ∗
      ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      stackAt sp trApplyStack := by
  simp only [stackAt, trApplyStack, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval

/-! ## `trAt` and `sessionStateAt` exposure and reassembly -/

theorem trAt_expose (A : RustAlloc) (t : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A t trG tr ⊢
      ⌜(∀ sc, tr.ratchet.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) ∧
        trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧
        tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      (t ↦₆₄ trG.ratchet.chainsCap) ∗
      ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
      vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      ((t + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
      ((t + 128#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey) ∗
      ((t + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
      ((t + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
      memRegion (t + 172#64) 4 ∗
      ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
      ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
      ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
      vecU8Buf A trG.pq.cap trG.pq.ptr tr.pqrState ∗
      ((t + 200#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((t + 232#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) := by
  dsimp only [trAt, ratchetAt]
  refine Entails.pure_left fun hclamp => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hchains_len, hpad_len, hmax_jumps⟩ => ?_
  have hzip_len : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length =
      tr.ratchet.receiverChains.length := by simp [hchains_len]
  dsimp only [vecAt]
  rw [hzip_len, vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  bi_entail

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem trAt_in_struct_entails_memRegion (t : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (hpad : trG.ratchet.senderPad.length = 100) :
    ((t ↦₆₄ trG.ratchet.chainsCap) ∗
      ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
      ((t + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
      ((t + 128#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey) ∗
      ((t + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
      ((t + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
      memRegion (t + 172#64) 4 ∗
      ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
      ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
      ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
      ((t + 200#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((t + 232#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ⊢
      memRegion t 264 := by
  have := optSenderChainBytes_length tr.ratchet.senderChain hpad
  have := length_keyToBytes32 tr.ratchet.rootKey
  have := tr.localIdentityKey.publicKey.bytes.toList_length
  have := tr.remoteIdentityKey.publicKey.bytes.toList_length
  sep_interval

@[expose] def sessionApplyFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.localIk ss ∗
  vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
  vecGhostAt A G.alice (ss + 0x60#64) ∗
  optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
  optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
  ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 0x150#64) ↦ₛ G.regIds)

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``sessionApplyFrame, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

theorem deserialize_ok_nonempty {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 0 < bs.length := by
  cases bs with
  | nil => simp [PublicKey.deserialize] at h
  | cons _ _ => simp

theorem vecU8Buf_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hc : cap ≠ 0) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ 0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
  apply Entails.pure_right ⟨hle, hpos, hlt, hptr⟩
  rw [ite_eq_right_iff.mpr (fun h => (hc h).elim)]
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
    refine memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion ptr bs) (Entails.refl _))

theorem slt_one_false_of_pos_lt {cap : BitVec 64} (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    cap.slt 1#64 = false := by
  have h1 : 1#64 ≤ cap := by bv_omega
  have h2 : cap < 0x8000000000000000#64 := by bv_omega
  revert h1 h2; bv_kernel

theorem vecU8At_expose_nonempty_dealloc (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hlen : 0 < bs.length) :
    vecU8At A v cap ptr bs ⊢
      ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧
        (cap + 1#64 == 0#64) = false ∧ cap.slt 1#64 = false ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hpos : 0 < cap.toNat := by omega
  have hc0 : cap ≠ 0 := fun h => by subst h; simp at hpos
  have hc0_beq : (cap == 0#64) = false := beq_false_of_ne hc0
  have hc1_beq : (cap + 1#64 == 0#64) = false := by
    apply beq_false_of_ne; intro h; have : cap.toNat = 2 ^ 64 - 1 := by bv_omega
    omega
  have hslt : cap.slt 1#64 = false := slt_one_false_of_pos_lt hpos hlt
  apply Entails.pure_right ⟨hpos, hlt, hc0_beq, hc1_beq, hslt, hptr⟩
  rw [ite_eq_right_iff.mpr (fun h => (hc0 h).elim)]
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
    refine memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsToBytes_entails_memRegion ptr bs) (Entails.refl _)))))

theorem sessionStateAt_expose_apply (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ⌜G.chains.length = st.receiverChains.length ∧
        0 < G.root.cap.toNat ∧ G.root.cap.toNat < 2 ^ 63 ∧
        (G.root.cap == 0#64) = false ∧ G.root.ptr ≠ 0 ∧
        G.sender.isSome = st.senderChain.isSome⌝ ∗
      sessionApplyFrame A ss G st ∗
      ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ ((ss + 64#64) ↦₆₄ 32#64) ∗
      A.live G.root.ptr G.root.cap.toNat 1 ∗ memRegion G.root.ptr G.root.cap.toNat ∗
      vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
      ((ss + 332#64) ↦₃₂ st.previousCounter) := by
  have h1 : sessionStateAt A ss G st ⊢
      ⌜G.chains.length = st.receiverChains.length⌝ ∗
      sessionApplyFrame A ss G st ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
      vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
      ((ss + 0x14c#64) ↦₃₂ st.previousCounter) := by
    dsimp only [sessionStateAt, sessionApplyFrame]
    refine Entails.pure_left fun ⟨hlik, hrik, hchains, hpend, hreg, hlik_len, hrik_len⟩ => ?_
    bi_entail
  refine Entails.trans h1 ?_
  apply Entails.pure_left; intro hchains
  have hroot := vecU8At_expose_nonempty_dealloc A (ss + 48#64) G.root.cap G.root.ptr
    (CryptoGames.HMAC.keyToBytes32 st.rootKey) (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at hroot
  have hpq : vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ⊢
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  have hsc_eq : optSenderChainAt A (ss + 144#64) G.sender st.senderChain ⊢
      ⌜G.sender.isSome = st.senderChain.isSome⌝ ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain := by
    cases G.sender <;> cases st.senderChain <;> dsimp only [optSenderChainAt]
    · exact Entails.pure_right rfl (Entails.refl _)
    · exact Entails.pure_left_only False.elim
    · exact Entails.pure_left_only False.elim
    · exact Entails.pure_right rfl (Entails.refl _)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hroot
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono hroot (sepConj_mono (Entails.refl _)
      (sepConj_mono hpq (sepConj_mono hsc_eq (Entails.refl _)))))) ?_
  bi_entail

theorem layoutOk_of_pos_lt {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

abbrev mkApplyGhost (G : SessionGhost) (trG : TrGhost) (rootPtr : BitVec 64)
    (sender' : Option SenderChainGhost) : SessionGhost :=
  { G with
    root := ⟨32#64, rootPtr⟩
    chainsCap := trG.ratchet.chainsCap
    chainsPtr := trG.ratchet.chainsPtr
    chains := trG.ratchet.chains
    pq := trG.pq
    sender := sender' }

attribute [local arm64_norm] mkApplyGhost

theorem trApplyRel_mkApplyGhost (G : SessionGhost) (trG : TrGhost) (rootPtr : BitVec 64)
    (sender' : Option SenderChainGhost) :
    G.TrApplyRel trG (mkApplyGhost G trG rootPtr sender') := by
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sessionStateAt_reassemble_apply (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (rootPtr : BitVec 64)
    (sender' : Option SenderChainGhost)
    (hchains : trG.ratchet.chains.length = tr.ratchet.receiverChains.length) :
    (sessionApplyFrame A ss G st ∗
      vecU8At A (ss + 0x30#64) 32#64 rootPtr (CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      ((ss + 120#64) ↦₆₄ trG.pq.cap) ∗ ((ss + 128#64) ↦₆₄ trG.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
      vecU8Buf A trG.pq.cap trG.pq.ptr tr.pqrState ∗
      optSenderChainAt A (ss + 0x90#64) sender' tr.ratchet.senderChain ∗
      ((ss + 0x14c#64) ↦₃₂ tr.ratchet.previousCounter)) ⊢
      sessionStateAt A ss (mkApplyGhost G trG rootPtr sender') (tr.applyToSessionState st) := by
  dsimp only [sessionStateAt, sessionApplyFrame, mkApplyGhost, TripleRatchet.applyToSessionState]
  rw [vecU8At_eq_header_sep_buf (v := ss + 0x78#64)]; dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.pure_left fun ⟨hlik, hrik, hpend, hreg, hlik_len, hrik_len⟩ => ?_
  bi_entail

@[expose] def senderChainRawSlots (ss : BitVec 64) : SepProp :=
  memRegion (ss + 144#64) 8 ∗
  memRegion (ss + 152#64) 8 ∗
  memRegion (ss + 160#64) 8 ∗
  memRegion (ss + 168#64) 8 ∗
  memRegion (ss + 176#64) 8 ∗
  memRegion (ss + 184#64) 8 ∗
  memRegion (ss + 192#64) 8 ∗
  memRegion (ss + 200#64) 8 ∗
  memRegion (ss + 208#64) 8 ∗
  memRegion (ss + 216#64) 8 ∗
  memRegion (ss + 224#64) 8 ∗
  memRegion (ss + 232#64) 8 ∗
  memRegion (ss + 240#64) 4 ∗
  memRegion (ss + 244#64) 4

theorem optSenderChainAt_none_expose (A : RustAlloc) (ss : BitVec 64) :
    optSenderChainAt A (ss + 144#64) none none ⊢
      ((ss + 144#64) ↦₆₄ noneCap) ∗
      (∃∗ d152 : BitVec 64, (ss + 152#64) ↦₆₄ d152) ∗
      (∃∗ d160 : BitVec 64, (ss + 160#64) ↦₆₄ d160) ∗
      (∃∗ d168 : BitVec 64, (ss + 168#64) ↦₆₄ d168) ∗
      (∃∗ d176 : BitVec 64, (ss + 176#64) ↦₆₄ d176) ∗
      (∃∗ d184 : BitVec 64, (ss + 184#64) ↦₆₄ d184) ∗
      (∃∗ d192 : BitVec 64, (ss + 192#64) ↦₆₄ d192) ∗
      (∃∗ d200 : BitVec 64, (ss + 200#64) ↦₆₄ d200) ∗
      (∃∗ d208 : BitVec 64, (ss + 208#64) ↦₆₄ d208) ∗
      (∃∗ d216 : BitVec 64, (ss + 216#64) ↦₆₄ d216) ∗
      (∃∗ d224 : BitVec 64, (ss + 224#64) ↦₆₄ d224) ∗
      (∃∗ d232 : BitVec 64, (ss + 232#64) ↦₆₄ d232) ∗
      (∃∗ d240 : BitVec 32, (ss + 240#64) ↦₃₂ d240) ∗
      memRegion (ss + 244#64) 4 := by
  dsimp only [optSenderChainAt]
  exact Entails.of_eq (by sep_interval_eq)

theorem optSenderChainAt_some_expose (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ⌜0 < sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧
        (sg.srk.cap == 0#64) = false ∧ (sg.srk.cap + 1#64 == 0#64) = false ∧ sg.srk.ptr ≠ 0 ∧
        0 < sg.priv.cap.toNat ∧ sg.priv.cap.toNat < 2 ^ 63 ∧
        (sg.priv.cap == 0#64) = false ∧ sg.priv.ptr ≠ 0 ∧
        0 < sg.ck.cap.toNat ∧ sg.ck.cap.toNat < 2 ^ 63 ∧
        sg.ck.cap.slt 1#64 = false ∧ sg.ck.ptr ≠ 0⌝ ∗
      ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
      ((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
      A.live sg.srk.ptr sg.srk.cap.toNat 1 ∗ memRegion sg.srk.ptr sg.srk.cap.toNat ∗
      ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗
      ((ss + 184#64) ↦₆₄ BitVec.ofNat 64 sg.priv.bytes.length) ∗
      A.live sg.priv.ptr sg.priv.cap.toNat 1 ∗ memRegion sg.priv.ptr sg.priv.cap.toNat ∗
      vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
      ((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
      ((ss + 232#64) ↦₆₄ 32#64) ∗
      A.live sg.ck.ptr sg.ck.cap.toNat 1 ∗ memRegion sg.ck.ptr sg.ck.cap.toNat ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4 := by
  unfold optSenderChainAt vecGhostAt optChainKeyAt
  apply Entails.pure_left
  rintro ⟨hsrk_deser, hpriv_eq, _, _⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hsrk_ne : 0 < sg.srk.bytes.length := deserialize_ok_nonempty hsrk_deser
  have hpriv_ne : 0 < sg.priv.bytes.length := by
    rw [hpriv_eq, sc.ratchetKey.privateKey.bytes.toList_length]; decide
  have hck_len : (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key).length = 32 := length_keyToBytes32 _
  have hck_ne : 0 < (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key).length := by omega
  have h1 := vecU8At_expose_nonempty_dealloc A (ss + 144#64) sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_ne
  have h2 := vecU8At_expose_nonempty_dealloc A (ss + 168#64) sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_ne
  have h4 := vecU8At_expose_nonempty_dealloc A (ss + 216#64) sg.ck.cap sg.ck.ptr
    (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) hck_ne
  rw [hck_len] at h4
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h1 h2 h4
  rw [← and_assoc, ← and_assoc] at h4
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono (Entails.refl _)
    (sepConj_mono h4 (Entails.refl _))))) ?_
  bi_entail

theorem optSenderChainAt_none_fold (A : RustAlloc) (ss : BitVec 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) (v12 : BitVec 32) :
    (((ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((ss + 152#64) ↦₆₄ v1) ∗
      ((ss + 160#64) ↦₆₄ v2) ∗
      ((ss + 168#64) ↦₆₄ v3) ∗
      ((ss + 176#64) ↦₆₄ v4) ∗
      ((ss + 184#64) ↦₆₄ v5) ∗
      ((ss + 192#64) ↦₆₄ v6) ∗
      ((ss + 200#64) ↦₆₄ v7) ∗
      ((ss + 208#64) ↦₆₄ v8) ∗
      ((ss + 216#64) ↦₆₄ v9) ∗
      ((ss + 224#64) ↦₆₄ v10) ∗
      ((ss + 232#64) ↦₆₄ v11) ∗
      ((ss + 240#64) ↦₃₂ v12) ∗
      memRegion (ss + 244#64) 4) ⊢
      optSenderChainAt A (ss + 144#64) none none := by
  dsimp only [optSenderChainAt, noneCap]; sep_interval

theorem vecU8At_fold_exact (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hcap : cap.toNat = n) (hlen : bs.length = n) (hc0 : cap ≠ 0) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ cap) ∗
      A.live ptr n 1 ∗ (ptr ↦ₛ bs)) ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader
  have hbit : BitVec.ofNat 64 bs.length = cap := by rw [hlen, ← hcap, BitVec.ofNat_toNat]; rfl
  rw [hbit, ite_eq_right_iff.mpr (fun h => (hc0 h).elim)]
  have hsub : cap.toNat - bs.length = 0 := by omega
  rw [hsub, hcap, memRegion_zero, sepConj_emp]
  simp only [sepConj_assoc]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_))
  exact Entails.pure_right ⟨by omega, by omega, hptr⟩ (Entails.refl _)

theorem vecAt_nil_0_8 (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecAt A 104 8 (messageKeyAt A) v 0#64 8#64 [] := by
  unfold vecAt vecHeader vecBuf
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (messageKeyAt A) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List (MessageKeyGhost × MessageKeyGenerator)).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List (MessageKeyGhost × MessageKeyGenerator)).length) * 104)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

@[expose] def mkSenderChainGhost (sc : SenderChain) (srkPtr privPtr ckPtr : BitVec 64) : SenderChainGhost :=
  { srk := ⟨33#64, srkPtr, sc.ratchetKey.publicKey.serialize⟩
    priv := ⟨32#64, privPtr, sc.ratchetKey.privateKey.bytes.toList⟩
    mkCap := 0#64
    mkPtr := 8#64
    ck := ⟨32#64, ckPtr⟩ }

theorem optSenderChainAt_some_fold (A : RustAlloc) (ss : BitVec 64) (sc : SenderChain)
    (srkPtr privPtr ckPtr : BitVec 64)
    (hclamp : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hsrk : srkPtr ≠ 0#64) (hpriv : privPtr ≠ 0#64) (hck : ckPtr ≠ 0#64) :
    (((ss + 144#64) ↦₆₄ 33#64) ∗
      ((ss + 152#64) ↦₆₄ srkPtr) ∗
      ((ss + 160#64) ↦₆₄ 33#64) ∗
      A.live srkPtr 33 1 ∗
      (srkPtr ↦ₛ sc.ratchetKey.publicKey.serialize) ∗
      ((ss + 168#64) ↦₆₄ 32#64) ∗
      ((ss + 176#64) ↦₆₄ privPtr) ∗
      ((ss + 184#64) ↦₆₄ 32#64) ∗
      A.live privPtr 32 1 ∗
      (privPtr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((ss + 192#64) ↦₆₄ 0#64) ∗
      ((ss + 200#64) ↦₆₄ 8#64) ∗
      ((ss + 208#64) ↦₆₄ 0#64) ∗
      ((ss + 216#64) ↦₆₄ 32#64) ∗
      ((ss + 224#64) ↦₆₄ ckPtr) ∗
      ((ss + 232#64) ↦₆₄ 32#64) ∗
      A.live ckPtr 32 1 ∗
      (ckPtr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗
      memRegion (ss + 244#64) 4) ⊢
      optSenderChainAt A (ss + 144#64) (some (mkSenderChainGhost sc srkPtr privPtr ckPtr)) (some sc) := by
  unfold optSenderChainAt mkSenderChainGhost vecGhostAt optChainKeyAt
  have hsrk_len : sc.ratchetKey.publicKey.serialize.length = 33 := by
    simp [PublicKey.serialize, sc.ratchetKey.publicKey.bytes.toList_length]
  apply Entails.pure_right ⟨deserialize_serialize_pk sc.ratchetKey.publicKey, rfl, hclamp, hsrk_len⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := vecU8At_fold_exact A (ss + 144#64) 33#64 srkPtr
    sc.ratchetKey.publicKey.serialize 33 rfl
    (by simp [PublicKey.serialize, sc.ratchetKey.publicKey.bytes.toList_length]) (by decide) (by decide) hsrk
  have h2 := vecU8At_fold_exact A (ss + 168#64) 32#64 privPtr
    sc.ratchetKey.privateKey.bytes.toList 32 rfl
    (by simp [sc.ratchetKey.privateKey.bytes.toList_length]) (by decide) (by decide) hpriv
  have h3 := vecAt_nil_0_8 A (ss + 192#64)
  have h4 := vecU8At_fold_exact A (ss + 216#64) 32#64 ckPtr
    (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) 32 rfl
    (length_keyToBytes32 _) (by decide) (by decide) hck
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4
  have hcomb := sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
    (sepConj_mono h4 (Entails.refl (((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4)))))
  simpa only [sepConj_assoc] using hcomb

theorem vecU8Buf_zero_entails_emp (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  apply Entails.pure_left; intro _
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live ptr (0#64 : BitVec 64).toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) ((0#64 : BitVec 64).toNat - bs.length)) = emp := rfl
  rw [hite]
  exact Entails.refl _

theorem vecU8Buf_eq_zero_entails_emp (A : RustAlloc) {cap : BitVec 64} (ptr : BitVec 64)
    (bs : List (BitVec 8)) (h : cap = 0) :
    vecU8Buf A cap ptr bs ⊢ emp := by
  subst h; exact vecU8Buf_zero_entails_emp A ptr bs

theorem mr_split_24 (a : BitVec 64) (c : Nat) :
    memRegion (a + BitVec.ofNat 64 c) 24 =
      memRegion (a + BitVec.ofNat 64 c) 8 ∗
      memRegion (a + BitVec.ofNat 64 (c + 8)) 8 ∗
      memRegion (a + BitVec.ofNat 64 (c + 16)) 8 := by
  rw [mr_cut_add a c 8 16 (by decide)]
  rw [mr_cut_add a (c + 8) 8 8 (by decide)]

theorem memRegion_24_unpack (a : BitVec 64) (c : Nat) :
    memRegion (a + BitVec.ofNat 64 c) 24 =
      ((∃∗ d0 : BitVec 64, (a + BitVec.ofNat 64 c) ↦₆₄ d0) ∗
       (∃∗ d1 : BitVec 64, (a + BitVec.ofNat 64 (c + 8)) ↦₆₄ d1) ∗
       (∃∗ d2 : BitVec 64, (a + BitVec.ofNat 64 (c + 16)) ↦₆₄ d2)) := by
  rw [mr_split_24 a c, ← memRegion_eight, ← memRegion_eight, ← memRegion_eight]

theorem memRegion_32_unpack (a : BitVec 64) :
    memRegion a 32 =
      ((∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
       (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
       (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
       (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3)) := by
  sep_interval_eq

theorem SepWPp_pure_elim3 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp :=
  SepWPp.weaken_pre (by bi_entail) (SepWPp.pure_elim h)

theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨ha, hp⟩
  unfold allocFailedIn at ha ⊢
  rw [← htr]
  exact ⟨ha, hp⟩

theorem hsc_stack_pack {sp : BitVec 64} {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12)) :
    (((sp - 224#64) ↦₆₄ w0) ∗ ((sp - 216#64) ↦₆₄ w1) ∗ ((sp - 208#64) ↦₆₄ w2) ∗ ((sp - 200#64) ↦₆₄ w3) ∗
      ((sp - 192#64) ↦₆₄ w4) ∗ ((sp - 184#64) ↦₆₄ w5) ∗ ((sp - 176#64) ↦₆₄ w6) ∗ ((sp - 168#64) ↦₆₄ w7) ∗
      ((sp - 160#64) ↦₆₄ w8) ∗ ((sp - 152#64) ↦₆₄ w9) ∗ ((sp - 144#64) ↦₆₄ w10) ∗ ((sp - 136#64) ↦₆₄ w11) ∗
      ((sp - 128#64) ↦₆₄ w12)) ⊢
      ((sp - 224#64) ↦ₛ bs) := by
  rw [h (sp - 224#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem hsc_tr_pack {t : BitVec 64} {bs : List (BitVec 8)}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12)) :
    (((t + 24#64) ↦₆₄ w0) ∗ ((t + 32#64) ↦₆₄ w1) ∗ ((t + 40#64) ↦₆₄ w2) ∗ ((t + 48#64) ↦₆₄ w3) ∗
      ((t + 56#64) ↦₆₄ w4) ∗ ((t + 64#64) ↦₆₄ w5) ∗ ((t + 72#64) ↦₆₄ w6) ∗ ((t + 80#64) ↦₆₄ w7) ∗
      ((t + 88#64) ↦₆₄ w8) ∗ ((t + 96#64) ↦₆₄ w9) ∗ ((t + 104#64) ↦₆₄ w10) ∗ ((t + 112#64) ↦₆₄ w11) ∗
      ((t + 120#64) ↦₆₄ w12)) ⊢
      ((t + 24#64) ↦ₛ bs) := by
  rw [h (t + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem hrk_pack {p : BitVec 64} {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) :
    ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3)) ⊢
      (p ↦ₛ bs) := by
  rw [h p]
  exact Entails.refl _

theorem hrk_tr_pack {t : BitVec 64} {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) :
    (((t + 128#64) ↦₆₄ w0) ∗ ((t + 136#64) ↦₆₄ w1) ∗ ((t + 144#64) ↦₆₄ w2) ∗ ((t + 152#64) ↦₆₄ w3)) ⊢
      ((t + 128#64) ↦ₛ bs) := by
  rw [h (t + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem stackAt_ext_to (sp : BitVec 64) (k : Nat) (hk : k ≤ extHookStack := by decide) :
    stackAt (sp - 224#64) extHookStack ⊢
      memRegion (sp - 16608#64) (extHookStack - k) ∗ stackAt (sp - 224#64) k := by
  rw [stackAt_sub_split (sp - 224#64) extHookStack k hk (by decide)]
  have heq : sp - 224#64 - BitVec.ofNat 64 extHookStack = sp - 16608#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq]
  exact Entails.refl _

theorem stackAt_to_ext (sp sp' : BitVec 64) (k : Nat) (hsp : sp' = sp - 224#64)
    (hk : k ≤ extHookStack := by decide) :
    (memRegion (sp - 16608#64) (extHookStack - k) ∗ stackAt sp' k) ⊢
      stackAt (sp - 224#64) extHookStack := by
  subst hsp
  have h := (stackAt_sub_split (sp - 224#64) extHookStack k hk (by decide)).symm
  have heq : sp - 224#64 - BitVec.ofNat 64 extHookStack = sp - 16608#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq] at h
  exact Entails.of_eq h

theorem stackAt_switch (sp sp' : BitVec 64) (k1 k2 : Nat) (hsp : sp' = sp - 224#64)
    (hk1 : k1 ≤ extHookStack := by decide) (hk2 : k2 ≤ extHookStack := by decide) :
    (memRegion (sp - 16608#64) (extHookStack - k1) ∗ stackAt sp' k1) ⊢
      memRegion (sp - 16608#64) (extHookStack - k2) ∗ stackAt (sp - 224#64) k2 :=
  Entails.trans (stackAt_to_ext sp sp' k1 hsp hk1) (stackAt_ext_to sp k2 hk2)

theorem SepWPp_fold_stack {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (k1 k2 : Nat)
    (hk1 : k1 ≤ extHookStack) (hk2 : k2 ≤ extHookStack)
    (hf : P = (memRegion (sp - 16608#64) (extHookStack - k1) ∗ stackAt sp' k1) ∗ F)
    (hsp : sp' = sp - 224#64)
    (h : SepWPp prog ret s ((memRegion (sp - 16608#64) (extHookStack - k2) ∗ stackAt (sp - 224#64) k2) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_switch sp sp' k1 k2 hsp hk1 hk2) hf h

theorem SepWPp_fold_stack_to_ext {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hk : k ≤ extHookStack)
    (hf : P = (memRegion (sp - 16608#64) (extHookStack - k) ∗ stackAt sp' k) ∗ F)
    (hsp : sp' = sp - 224#64)
    (h : SepWPp prog ret s (stackAt (sp - 224#64) extHookStack ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_to_ext sp sp' k hsp hk) hf h

theorem vecAt_chains_fold (A : RustAlloc) (ss : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hchains : trG.ratchet.chains.length = tr.ratchet.receiverChains.length) :
    (((ss + 72#64) ↦₆₄ trG.ratchet.chainsCap) ∗
      ((ss + 80#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
      vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains)) ⊢
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) := by
  unfold vecAt vecHeader
  have hzip : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length =
      tr.ratchet.receiverChains.length := by simp [hchains]
  rw [hzip]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem optSenderChainBytes_none_stack_eq (sp : BitVec 64) (pad : List (BitVec 8)) :
    ((sp - 224#64) ↦ₛ optSenderChainBytes none pad) =
      (((sp - 224#64) ↦₃₂ 0#32) ∗ ((sp - 220#64) ↦ₛ pad)) := by
  rw [optSenderChainBytes_none_eq (sp - 224#64) pad]
  have h1 : sp - 224#64 + 4#64 = sp - 220#64 := by bv_omega
  rw [h1]

theorem stack_104_none_to_memRegion (sp : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 100) :
    (((sp - 224#64) ↦₃₂ 0#32) ∗ ((sp - 220#64) ↦ₛ pad)) ⊢
      memRegion (sp - 224#64) 104 := by
  have h := pointsToBytes_entails_memRegion (sp - 224#64) (optSenderChainBytes none pad)
  rw [optSenderChainBytes_length none hpad, optSenderChainBytes_none_stack_eq sp pad] at h
  exact h

theorem optSenderChainBytes_some_stack_eq (sp : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    ((sp - 224#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((sp - 224#64) ↦₃₂ 1#32) ∗
       ((sp - 220#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp - 188#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp - 156#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       ((sp - 124#64) ↦₃₂ sc.chainKey.index)) := by
  rw [optSenderChainBytes_some_eq (sp - 224#64) sc pad]
  have h1 : sp - 224#64 + 4#64 = sp - 220#64 := by bv_omega
  have h2 : sp - 224#64 + 36#64 = sp - 188#64 := by bv_omega
  have h3 : sp - 224#64 + 68#64 = sp - 156#64 := by bv_omega
  have h4 : sp - 224#64 + 100#64 = sp - 124#64 := by bv_omega
  rw [h1, h2, h3, h4]

theorem stack_104_some_to_memRegion (sp : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8))
    (hpad : pad.length = 100) :
    (((sp - 224#64) ↦₃₂ 1#32) ∗
      ((sp - 220#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp - 188#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp - 156#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
      ((sp - 124#64) ↦₃₂ sc.chainKey.index)) ⊢
      memRegion (sp - 224#64) 104 := by
  have h := pointsToBytes_entails_memRegion (sp - 224#64) (optSenderChainBytes (some sc) pad)
  rw [optSenderChainBytes_length (some sc) hpad, optSenderChainBytes_some_stack_eq sp sc pad] at h
  exact h

theorem optSenderChainBytes_some_tr_eq (t : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8))
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) :
    ((t + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((t + 24#64) ↦₃₂ 1#32) ∗
       ((t + 28#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((t + 60#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((t + 92#64) ↦₆₄ w0) ∗ ((t + 100#64) ↦₆₄ w1) ∗ ((t + 108#64) ↦₆₄ w2) ∗ ((t + 116#64) ↦₆₄ w3) ∗
       ((t + 124#64) ↦₃₂ sc.chainKey.index)) := by
  rw [optSenderChainBytes_some_eq (t + 24#64) sc pad]
  have hck := h (t + 92#64)
  have h1 : t + 24#64 + 4#64 = t + 28#64 := by bv_omega
  have h2 : t + 24#64 + 36#64 = t + 60#64 := by bv_omega
  have h3 : t + 24#64 + 68#64 = t + 92#64 := by bv_omega
  have h4 : t + 24#64 + 100#64 = t + 124#64 := by bv_omega
  have h5 : t + 92#64 + 8#64 = t + 100#64 := by bv_omega
  have h6 : t + 92#64 + 16#64 = t + 108#64 := by bv_omega
  have h7 : t + 92#64 + 24#64 = t + 116#64 := by bv_omega
  rw [h1, h2, h3, h4, hck, h5, h6, h7]
  simp only [sepConj_assoc]

theorem hck_tr_pack {t : BitVec 64} {sc : SenderChain} (pad : List (BitVec 8))
    {w0 w1 w2 w3 : BitVec 64}
    (h : ∀ a : BitVec 64, (a ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) :
    (((t + 24#64) ↦₃₂ 1#32) ∗
      ((t + 28#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((t + 60#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((t + 92#64) ↦₆₄ w0) ∗ ((t + 100#64) ↦₆₄ w1) ∗ ((t + 108#64) ↦₆₄ w2) ∗ ((t + 116#64) ↦₆₄ w3) ∗
      ((t + 124#64) ↦₃₂ sc.chainKey.index)) ⊢
      ((t + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) := by
  rw [optSenderChainBytes_some_tr_eq t sc pad h]
  exact Entails.refl _

theorem stack_24_to_memRegion (sp v0 v1 v2 : BitVec 64) :
    (((sp - 120#64) ↦₆₄ v0) ∗ ((sp - 112#64) ↦₆₄ v1) ∗ ((sp - 104#64) ↦₆₄ v2)) ⊢
      memRegion (sp - 120#64) 24 := by
  sep_interval

theorem spAligned_sub_224 {sp sp' : BitVec 64} (halign : (sp &&& 15#64 == 0#64) = true)
    (hsp : sp' = sp - 224#64) : (sp' &&& 15#64 == 0#64) = true := by
  subst hsp; revert halign; bv_kernel

theorem SepWP_instantiate_post_exists_outer {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ a, Q sf a) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (Entails.sepExists_intro w) (h1 hm), h2⟩

theorem SepWPp_panic_oom {prog : Program} {ret panic_pc : BitVec 64} {s0 s : State} {P R : SepProp}
    {Q : State → SepProp → Prop}
    (hrun : s.status = .Running)
    (hpc : s.pc = panic_pc)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rw [← hpc] at hext
  refine SepWPp.panic hrun hext (fun h => ?_)
  rw [← sepConj_assoc]
  exact allowPanic_panicked (allocFailedIn_of_eq (s0 := s0) htr) h

theorem boxU8Buf_pk_expose (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢
      ⌜ptr ≠ 0#64⌝ ∗ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  unfold boxU8Buf
  apply Entails.pure_left; rintro ⟨hptr, _⟩
  apply Entails.pure_right hptr
  rw [ite_eq_right_iff.mpr (fun h => by nomatch h)]
  have hlen : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, pk.bytes.toList_length]
  rw [hlen]
  exact Entails.refl _

theorem pk_buf_to_memRegion (ptr : BitVec 64) (pk : PublicKey) :
    (ptr ↦ₛ pk.serialize) ⊢ memRegion ptr 33 := by
  have hlen : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, pk.bytes.toList_length]
  rw [← hlen]
  exact pointsToBytes_entails_memRegion ptr _

theorem vecU8At_priv_expose_stack (A : RustAlloc) (sp cap ptr : BitVec 64) (k : List.Vector (BitVec 8) 32) :
    vecU8At A (sp - 120#64) cap ptr k.toList ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
      ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗ ((sp - 104#64) ↦₆₄ 32#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have hlen : k.toList.length = 32 := k.toList_length
  have h1 : sp - 120#64 + 8#64 = sp - 112#64 := by bv_omega
  have h2 : sp - 120#64 + 16#64 = sp - 104#64 := by bv_omega
  rw [hlen, h1, h2]
  simp only [BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hc0 : cap ≠ 0#64 := by intro h; subst h; simp at hle
  have hc0_beq : (cap == 0#64) = false := beq_false_of_ne hc0
  apply Entails.pure_right ⟨hle, hlt, hc0_beq, hptr⟩
  rw [ite_eq_right_iff.mpr (fun h => (hc0 h).elim)]
  exact Entails.refl _

theorem vecU8_priv_expose_stack (A : RustAlloc) (sp : BitVec 64) (k : List.Vector (BitVec 8) 32) :
    vecU8 A (sp - 120#64) k.toList ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
        ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗ ((sp - 104#64) ↦₆₄ 32#64) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (vecU8At_priv_expose_stack A sp cap ptr k))

theorem priv_buf_to_memRegion (ptr cap : BitVec 64) (k : List.Vector (BitVec 8) 32)
    (hle : 32 ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    ((ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) ⊢
      memRegion ptr cap.toNat := by
  have hlen : k.toList.length = 32 := k.toList_length
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr k.toList.length ∗ memRegion (ptr + BitVec.ofNat 64 k.toList.length) (cap.toNat - k.toList.length) :=
    memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  refine sepConj_mono (pointsToBytes_entails_memRegion ptr k.toList) ?_
  rw [hlen]
  exact Entails.refl _

/-! ## Top-level `TrApplyOk` theorem -/

theorem stackAt_trApply_x (sp : BitVec 64) :
    stackAt sp trApplyStackX =
      stackAt (sp - 224#64) dropVecChainStackX ∗
      (∃∗ u0 : BitVec 64, (sp - 224#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp - 216#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (sp - 208#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (sp - 200#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (sp - 192#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp - 184#64) ↦₆₄ u5) ∗
      (∃∗ u6 : BitVec 64, (sp - 176#64) ↦₆₄ u6) ∗
      (∃∗ u7 : BitVec 64, (sp - 168#64) ↦₆₄ u7) ∗
      (∃∗ u8 : BitVec 64, (sp - 160#64) ↦₆₄ u8) ∗
      (∃∗ u9 : BitVec 64, (sp - 152#64) ↦₆₄ u9) ∗
      (∃∗ u10 : BitVec 64, (sp - 144#64) ↦₆₄ u10) ∗
      (∃∗ u11 : BitVec 64, (sp - 136#64) ↦₆₄ u11) ∗
      (∃∗ u12 : BitVec 64, (sp - 128#64) ↦₆₄ u12) ∗
      memRegion (sp - 120#64) 24 ∗
      (∃∗ r0 : BitVec 64, (sp - 96#64) ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (sp - 88#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (sp - 80#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (sp - 72#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (sp - 64#64) ↦₆₄ r4) ∗
      (∃∗ r5 : BitVec 64, (sp - 56#64) ↦₆₄ r5) ∗
      (∃∗ r6 : BitVec 64, (sp - 48#64) ↦₆₄ r6) ∗
      (∃∗ r7 : BitVec 64, (sp - 40#64) ↦₆₄ r7) ∗
      (∃∗ r8 : BitVec 64, (sp - 32#64) ↦₆₄ r8) ∗
      (∃∗ r9 : BitVec 64, (sp - 24#64) ↦₆₄ r9) ∗
      (∃∗ r10 : BitVec 64, (sp - 16#64) ↦₆₄ r10) ∗
      (∃∗ r11 : BitVec 64, (sp - 8#64) ↦₆₄ r11) := by
  simp only [stackAt, trApplyStackX, dropVecChainStackX, dropVecMessageKeyStackX, extHookStack,
    Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

theorem stackAt_trApply_fold_x (sp : BitVec 64) (s0 : State) :
    (stackAt (sp - 224#64) dropVecChainStackX ∗
      memRegion (sp - 224#64) 104 ∗
      memRegion (sp - 120#64) 24 ∗
      ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      stackAt sp trApplyStackX := by
  simp only [stackAt, trApplyStackX, dropVecChainStackX, dropVecMessageKeyStackX, extHookStack,
    Nat.reducePow, Nat.reduceAdd]
  sep_interval

/-! ## Stack- and optional-image-parameterized proof (`trApply_ok_opt`) -/

@[irreducible] private def frozenStop (pc : BitVec 64) : BitVec 64 := pc

private theorem SepWP.done_frozen {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running) (hpost : post s P) :
    SepWP prog (frozenStop mid) s P post := by
  unfold frozenStop
  exact SepWP.done hpc hrun hpost

abbrev pkSerializeSpecAt (A : RustAlloc) (pkStack : Nat) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
    stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool ∗ stackAt s0.sp pkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev privSerializeSpecAt (A : RustAlloc) (privStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (k, bs, ret) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32⌝ ∗ (k ↦ₛ bs) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt s.sp privStack
  post := fun (k, bs, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A ret bs ∗ A.pool ∗ stackAt s0.sp privStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev dropVecMessageKeySpecAt (A : RustAlloc) (mkStack : Nat) : Spec DropVecMessageKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (messageKeyAt A) x.v x.cap x.ptr x.mks ∗ A.pool ∗
      stackAt s.sp mkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp mkStack

abbrev dropVecChainSpecAt (A : RustAlloc) (chStack : Nat) : Spec DropVecChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗
      stackAt s.sp chStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp chStack

abbrev trApplySpecAt (A : RustAlloc) (calleeStack : Nat) : Spec TrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.t ∧ s.readReg64 .x1 = x.ss⌝ ∗
      trAt A x.t x.trG x.tr ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp (224 + calleeStack) ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.TrApplyRel x.trG G'⌝ ∗
        sessionStateAt A x.ss G' (x.tr.applyToSessionState x.st)) ∗
      memRegion x.t 264 ∗ stackAt s0.sp (224 + calleeStack) ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem stackAt_ext_to_gen (sp : BitVec 64) (calleeStack k : Nat)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hk : k ≤ calleeStack) :
    stackAt (sp - 224#64) calleeStack ⊢
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k) ∗
        stackAt (sp - 224#64) k := by
  rw [stackAt_sub_split (sp - 224#64) calleeStack k hk (by omega)]
  have heq : sp - 224#64 - BitVec.ofNat 64 calleeStack =
      sp - BitVec.ofNat 64 (224 + calleeStack) := by
    rw [BitVec.sub_sub]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [heq]
  exact Entails.refl _

theorem stackAt_to_ext_gen (sp sp' : BitVec 64) (calleeStack k : Nat) (hsp : sp' = sp - 224#64)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hk : k ≤ calleeStack) :
    (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k) ∗ stackAt sp' k) ⊢
      stackAt (sp - 224#64) calleeStack := by
  subst hsp
  have h := (stackAt_sub_split (sp - 224#64) calleeStack k hk (by omega)).symm
  have heq : sp - 224#64 - BitVec.ofNat 64 calleeStack =
      sp - BitVec.ofNat 64 (224 + calleeStack) := by
    rw [BitVec.sub_sub]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [heq] at h
  exact Entails.of_eq h

theorem stackAt_switch_gen (sp sp' : BitVec 64) (calleeStack k1 k2 : Nat) (hsp : sp' = sp - 224#64)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hk1 : k1 ≤ calleeStack) (hk2 : k2 ≤ calleeStack) :
    (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k1) ∗ stackAt sp' k1) ⊢
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k2) ∗
        stackAt (sp - 224#64) k2 :=
  Entails.trans (stackAt_to_ext_gen sp sp' calleeStack k1 hsp hcallee hk1)
    (stackAt_ext_to_gen sp calleeStack k2 hcallee hk2)

theorem SepWPp_fold_stack_gen {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (calleeStack k1 k2 : Nat)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hk1 : k1 ≤ calleeStack) (hk2 : k2 ≤ calleeStack)
    (hf : P = (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k1) ∗ stackAt sp' k1) ∗ F)
    (hsp : sp' = sp - 224#64)
    (h : SepWPp prog ret s
      ((memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k2) ∗
        stackAt (sp - 224#64) k2) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_switch_gen sp sp' calleeStack k1 k2 hsp hcallee hk1 hk2) hf h

theorem SepWPp_fold_stack_to_ext_gen {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (calleeStack k : Nat)
    (hcallee : 224 + calleeStack < 2 ^ 64) (hk : k ≤ calleeStack)
    (hf : P = (memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - k) ∗ stackAt sp' k) ∗ F)
    (hsp : sp' = sp - 224#64)
    (h : SepWPp prog ret s (stackAt (sp - 224#64) calleeStack ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_to_ext_gen sp sp' calleeStack k hsp hcallee hk) hf h

section FnOffShield
attribute [local irreducible] _root_.Arm64.Program.fnOff

namespace ApplyTailSteps

end ApplyTailSteps

end FnOffShield

namespace ApplyTailSteps

end ApplyTailSteps

open ProofLib.GenPlacedFetches

abbrev LsClInv [LibsignalPlacement] (s : State) : Prop :=
  LibsignalCodeLoaded lsmpl s.mem

theorem LsClInv.of_steps [LibsignalPlacement] {prog : Program} {s s' : State}
    (hsteps : Steps prog s s') (h : LsClInv s) : LsClInv s' :=
  h.of_keepsFrozen hsteps.keepsFrozen

theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : LsClInv s)
    (h : SepWP prog mid s P (fun sm Pm => LsClInv sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_seq_lscl hinv (SepWP.mono h fun _ _ hp hr h' hcl =>
    SepWP.done hp hr (h' hcl)))

private theorem SepWP.of_sepWP_lscl_frozen [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : LsClInv s)
    (h : SepWP prog (frozenStop mid) s P
      (fun sm Pm => LsClInv sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold frozenStop at h
  exact sepWP_seq_lscl hinv h

theorem SepWPp.call_lscl_frame [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hinv : LsClInv s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsClInv sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hcall_cl : subroutine_ok prog entry
      { withLsCodeLoaded lsmpl spec with
        post := fun x s0 sf => ⌜LsClInv sf⌝ ∗ spec.post x s0 sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0 hpc0 hrun0 hpre0 hsp0 hL => ?_
    have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre0
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0 hpc0 hrun0 hpre0 hsp0 hL
    have hclf : LsClInv sf := hcl0.of_keepsFrozen hsteps.keepsFrozen
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hclf, hpost⟩
    · exact Or.inr hrest
  refine ProofLib.SepWPp.call (x := x) (F := F) hcall_cl hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [withLsCodeLoaded]
    rw [hspec, sepConj_assoc, sepConj_left_comm (⌜φ⌝ ∗ T), satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf code R' hex hpost
    exact hexit sf code R' hex hpost
  · intro sf hpan
    exact hpanic sf hpan
  · intro sf hpcm hrunm hspm hcsm
    dsimp only
    exact SepWPp.congr_pre (sepConj_assoc _ _ _) (SepWPp.pure_left (hnext sf hpcm hrunm hspm hcsm))
  · intro sf R' _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hoom_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem SepWPp_call_pk_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {A : RustAlloc} {pkStack : Nat}
    (hpk : subroutine_ok prog entry (withLsCodeLoaded lsmpl (pkSerializeSpecAt A pkStack)))
    (hinv : LsClInv s)
    (pk : PublicKey)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = s0.sp - 220#64)
    (hP : P = (((s0.sp - 220#64) ↦ₛ pk.bytes.toList) ∗ A.pool ∗
      stackAt (s0.sp - 224#64) pkStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWPp prog ret sf
        ((⌜sf.readReg64 Reg.x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
          ((s0.sp - 220#64) ↦ₛ pk.bytes.toList) ∗
          boxU8Buf A (sf.readReg64 Reg.x0) pk.serialize ∗
          A.pool ∗ stackAt (s0.sp - 224#64) pkStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  refine SepWPp.call_lscl_frame (x := ⟨s0.sp - 220#64, pk⟩) hpk hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_ hx0 hP
    (fun sf code R' _ h => not_satisfies_false_sepConj h)
    (fun sf _ h => by rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [pkSerializeSpecAt]
    rw [hsp_eq]
  · dsimp only [pkSerializeSpecAt]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

theorem SepWPp_call_priv_lscl [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {A : RustAlloc} {privStack : Nat}
    (hpriv : subroutine_ok prog entry (withLsCodeLoaded lsmpl (privSerializeSpecAt A privStack)))
    (hinv : LsClInv s)
    (bs : List (BitVec 8))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 224#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = s0.sp - 188#64 ∧ s.readReg64 Reg.x8 = s0.sp - 120#64 ∧ bs.length = 32)
    (hP : P = (((s0.sp - 188#64) ↦ₛ bs) ∗ memRegion (s0.sp - 120#64) 24 ∗ A.pool ∗
      stackAt (s0.sp - 224#64) privStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 224#64 → CalleeSavedPreserved s sf → LsClInv sf →
      SepWPp prog ret sf
        ((⌜sf.trace = s0.trace⌝ ∗ ((s0.sp - 188#64) ↦ₛ bs) ∗
          vecU8 A (s0.sp - 120#64) bs ∗ A.pool ∗ stackAt (s0.sp - 224#64) privStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  refine SepWPp.call_lscl_frame (x := (s0.sp - 188#64, bs, s0.sp - 120#64)) hpriv hinv hpc hrun
    (spAligned_sub_224 hsp_align hsp_eq) hlr ?_ hx hP
    (fun sf code R' _ h => not_satisfies_false_sepConj h)
    (fun sf _ h => by rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f => ?_)
  · dsimp only [privSerializeSpecAt]
    rw [hsp_eq]
  · dsimp only [privSerializeSpecAt]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hinv_f

namespace ApplyTailSteps

theorem SepWPp_drop_old_sender_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {calleeStack stubStack mkStack chStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hmk_le : mkStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A stubStack))
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpecAt A mkStack)))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp ss : BitVec 64) {sp' : BitVec 64}
    {G_sender : Option SenderChainGhost} {st_sender : Option SenderChain}
    (hinv : LsClInv s)
    (hpc : s.pc = (blkPl_58).base + 208#64)
    (hrun : s.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp : s.sp = sp - 224#64)
    (hx20 : s.readReg64 .x20 = ss)
    (hGs_eq : G_sender.isSome = st_sender.isSome)
    (hP : P = (optSenderChainAt A (ss + 144#64) G_sender st_sender ∗ A.pool ∗
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - stubStack) ∗
      stackAt sp' stubStack) ∗ F)
    (hsp' : sp' = sp - 224#64)
    (hnext : ∀ (sf : State) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) (v12 : BitVec 32),
      sf.pc = (blkPl_58).base + 288#64 →
      sf.status = .Running →
      sf.sp = sp - 224#64 →
      sf.trace = s.trace →
      CalleeSavedPreserved s sf →
      LsClInv sf →
      SepWPp ((blkPC_58).rebase (blkPl_58).base H) ret sf
        ((((ss + 144#64) ↦₆₄ v0) ∗ ((ss + 152#64) ↦₆₄ v1) ∗ ((ss + 160#64) ↦₆₄ v2) ∗
          ((ss + 168#64) ↦₆₄ v3) ∗ ((ss + 176#64) ↦₆₄ v4) ∗ ((ss + 184#64) ↦₆₄ v5) ∗
          ((ss + 192#64) ↦₆₄ v6) ∗ ((ss + 200#64) ↦₆₄ v7) ∗ ((ss + 208#64) ↦₆₄ v8) ∗
          ((ss + 216#64) ↦₆₄ v9) ∗ ((ss + 224#64) ↦₆₄ v10) ∗ ((ss + 232#64) ↦₆₄ v11) ∗
          ((ss + 240#64) ↦₃₂ v12) ∗ memRegion (ss + 244#64) 4 ∗ A.pool ∗
          memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - chStack) ∗
          stackAt (sp - 224#64) chStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_58).rebase (blkPl_58).base H) ret s P Q Qp := by
  rw [hP, hsp']; clear hP hsp'
  cases hGs : G_sender <;> cases hsts : st_sender
  · refine SepWPp.fold (optSenderChainAt_none_expose A ss) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat refine SepWPp.exists_elim fun _ => ?_
    refine SepWPp_fold_stack_gen sp calleeStack stubStack chStack hcallee hstub_le hch_le (by sep_focus) rfl ?_
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (288)) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_f
    refine SepWPp.weaken_pre (by bi_entail)
      (hnext _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [CalleeSavedPreserved, arm64_norm, *]) hinv_f)
  · simp [hGs, hsts] at hGs_eq
  · simp [hGs, hsts] at hGs_eq
  · rename_i sg sc0
    refine SepWPp.fold (optSenderChainAt_some_expose A ss sg sc0) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hsrk_pos, hsrk_lt, hsrk_c0, hsrk_cmn, hsrk_ptr,
      hpriv_pos, hpriv_lt, hpriv_c0, hpriv_ptr, hck_pos, hck_lt, hck_slt, hck_ptr⟩ => ?_
    have hsrk_layout : LayoutOk sg.srk.cap.toNat 1 := layoutOk_of_pos_lt hsrk_pos hsrk_lt
    have hpriv_layout : LayoutOk sg.priv.cap.toNat 1 := layoutOk_of_pos_lt hpriv_pos hpriv_lt
    have hck_layout : LayoutOk sg.ck.cap.toNat 1 := layoutOk_of_pos_lt hck_pos hck_lt
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (280)) hinv
    wp_steps
    wp_call hdealloc (sg.srk.ptr, sg.srk.cap.toNat, 1)
    wp_steps
    wp_call hdealloc (sg.priv.ptr, sg.priv.cap.toNat, 1)
    wp_steps
    wp_call hdealloc (sg.ck.ptr, sg.ck.cap.toNat, 1)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_280
    refine SepWPp_fold_stack_gen sp calleeStack stubStack mkStack hcallee hstub_le hmk_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (288)) hinv_280
    apply SepWP.of_sepWP_lscl_frozen (mid := lsmpl.base 3) hinv_280
    wp_steps
    apply SepWP.done_frozen (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_call_mk
    wp_call (lscall_blk_cl (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (spec := dropVecMessageKeySpecAt A mkStack) hdropMk hinv_call_mk) ⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_288
    rw [memRegion_24_unpack ss 192]
    simp only [Nat.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d208 => SepWPp.exists_elim fun d200 => SepWPp.exists_elim fun d192 => ?_
    refine SepWPp_fold_stack_gen sp calleeStack mkStack chStack hcallee hmk_le hch_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWPp.weaken_pre (by bi_entail)
      (hnext _ sg.srk.cap sg.srk.ptr (BitVec.ofNat 64 sg.srk.bytes.length)
        sg.priv.cap sg.priv.ptr (BitVec.ofNat 64 sg.priv.bytes.length)
        d192 d200 d208 sg.ck.cap sg.ck.ptr 32#64 sc0.chainKey.index
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [CalleeSavedPreserved, arm64_norm, *]) hinv_288)

theorem SepWPp_tail_14c_to_184_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {calleeStack stubStack chStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A stubStack))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp ss t : BitVec 64) {sp' : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hpc : s.pc = (blkPl_58).base + 332#64)
    (hrun : s.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp : s.sp = sp - 224#64)
    (hx19 : s.readReg64 .x19 = t)
    (hx20 : s.readReg64 .x20 = ss)
    (hchains_len : trG.ratchet.chains.length = tr.ratchet.receiverChains.length)
    (hP : P = (memRegion (ss + 72#64) 24 ∗
      (t ↦₆₄ trG.ratchet.chainsCap) ∗
      ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
      vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
      ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
      ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗
      ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
      A.pool ∗
      memRegion (sp - BitVec.ofNat 64 (224 + calleeStack)) (calleeStack - chStack) ∗
      stackAt sp' chStack) ∗ F)
    (hsp' : sp' = sp - 224#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_58).base + 388#64 →
      sf.status = .Running →
      sf.sp = sp - 224#64 →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp ((blkPC_58).rebase (blkPl_58).base H) ret sf
        ((vecAt A 104 8 (chainAt A) (ss + 0x48#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
            (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
          (t ↦₆₄ trG.ratchet.chainsCap) ∗
          ((t + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((t + 16#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.receiverChains.length) ∗
          ((t + 176#64) ↦₆₄ trG.pq.cap) ∗
          ((t + 184#64) ↦₆₄ trG.pq.ptr) ∗
          ((t + 192#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          ((ss + 120#64) ↦₆₄ trG.pq.cap) ∗
          ((ss + 128#64) ↦₆₄ trG.pq.ptr) ∗
          ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          A.pool ∗
          stackAt (sp - 224#64) calleeStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_58).rebase (blkPl_58).base H) ret s P Q Qp := by
  rw [hP, hsp']; clear hP hsp'
  rw [memRegion_24_unpack ss 72]
  simp only [Nat.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ => ?_
  apply SepWPp.of_sepWP (mid := (blkPl_58).base + bv% (356))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPp.fold (vecAt_chains_fold A ss trG tr hchains_len) (by sep_focus) ?_
  by_cases hpq_cap : G.pq.cap = 0
  · have hpq_beq : (G.pq.cap == 0#64) = true := by simp [hpq_cap]
    refine SepWPp.fold (vecU8Buf_eq_zero_entails_emp A G.pq.ptr st.pqRatchetState hpq_cap) (by sep_focus) ?_
    simp only [emp_sepConj]
    refine SepWPp_fold_stack_to_ext_gen sp calleeStack chStack hcallee hch_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply SepWPp.of_sepWP (mid := (blkPl_58).base + bv% (388))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre (by bi_entail)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  · have hpq_beq : (G.pq.cap == 0#64) = false := beq_false_of_ne hpq_cap
    refine SepWPp.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState hpq_cap) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hpq_pos, hpq_lt, hpq_ptr⟩ => ?_
    have hpq_layout : LayoutOk G.pq.cap.toNat 1 := layoutOk_of_pos_lt hpq_pos hpq_lt
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    refine SepWPp_fold_stack_gen sp calleeStack chStack stubStack hcallee hch_le hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply SepWPp.of_sepWP (mid := (blkPl_58).base + bv% (388))
    wp_steps
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp_fold_stack_to_ext_gen sp calleeStack stubStack hcallee hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWPp.weaken_pre (by bi_entail)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))

end ApplyTailSteps

theorem trApply_placed_ok_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {calleeStack stubStack mkStack chStack pkStack privStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hmk_le : mkStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hpk_le : pkStack ≤ calleeStack)
    (hpriv_le : privStack ≤ calleeStack)
    (hstack_open : ∀ sp : BitVec 64,
      stackAt sp (224 + calleeStack) =
        stackAt (sp - 224#64) calleeStack ∗
        (∃∗ u0 : BitVec 64, (sp - 224#64) ↦₆₄ u0) ∗
        (∃∗ u1 : BitVec 64, (sp - 216#64) ↦₆₄ u1) ∗
        (∃∗ u2 : BitVec 64, (sp - 208#64) ↦₆₄ u2) ∗
        (∃∗ u3 : BitVec 64, (sp - 200#64) ↦₆₄ u3) ∗
        (∃∗ u4 : BitVec 64, (sp - 192#64) ↦₆₄ u4) ∗
        (∃∗ u5 : BitVec 64, (sp - 184#64) ↦₆₄ u5) ∗
        (∃∗ u6 : BitVec 64, (sp - 176#64) ↦₆₄ u6) ∗
        (∃∗ u7 : BitVec 64, (sp - 168#64) ↦₆₄ u7) ∗
        (∃∗ u8 : BitVec 64, (sp - 160#64) ↦₆₄ u8) ∗
        (∃∗ u9 : BitVec 64, (sp - 152#64) ↦₆₄ u9) ∗
        (∃∗ u10 : BitVec 64, (sp - 144#64) ↦₆₄ u10) ∗
        (∃∗ u11 : BitVec 64, (sp - 136#64) ↦₆₄ u11) ∗
        (∃∗ u12 : BitVec 64, (sp - 128#64) ↦₆₄ u12) ∗
        memRegion (sp - 120#64) 24 ∗
        (∃∗ r0 : BitVec 64, (sp - 96#64) ↦₆₄ r0) ∗
        (∃∗ r1 : BitVec 64, (sp - 88#64) ↦₆₄ r1) ∗
        (∃∗ r2 : BitVec 64, (sp - 80#64) ↦₆₄ r2) ∗
        (∃∗ r3 : BitVec 64, (sp - 72#64) ↦₆₄ r3) ∗
        (∃∗ r4 : BitVec 64, (sp - 64#64) ↦₆₄ r4) ∗
        (∃∗ r5 : BitVec 64, (sp - 56#64) ↦₆₄ r5) ∗
        (∃∗ r6 : BitVec 64, (sp - 48#64) ↦₆₄ r6) ∗
        (∃∗ r7 : BitVec 64, (sp - 40#64) ↦₆₄ r7) ∗
        (∃∗ r8 : BitVec 64, (sp - 32#64) ↦₆₄ r8) ∗
        (∃∗ r9 : BitVec 64, (sp - 24#64) ↦₆₄ r9) ∗
        (∃∗ r10 : BitVec 64, (sp - 16#64) ↦₆₄ r10) ∗
        (∃∗ r11 : BitVec 64, (sp - 8#64) ↦₆₄ r11))
    (hstack_fold : ∀ (sp : BitVec 64) (s0 : State),
      (stackAt (sp - 224#64) calleeStack ∗
        memRegion (sp - 224#64) 104 ∗
        memRegion (sp - 120#64) 24 ∗
        ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
        stackAt sp (224 + calleeStack))
    (hshim : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack stubStack))
    (halloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A stubStack))
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A stubStack))
    (hmemcpy : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsMemcpySym) (memcpySpecWithStack stubStack))
    (hpanic : ((blkPC_58).rebase (blkPl_58).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked)
    (hpriv : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 208) (withLsCodeLoaded lsmpl (privSerializeSpecAt A privStack)))
    (hpk : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (pkSerializeSpecAt A pkStack)))
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpecAt A mkStack)))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 2) (withLsCodeLoaded lsmpl (dropVecChainSpecAt A chStack))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpecAt A calleeStack)) := by
  unfold withLsCodeLoaded trApplySpecAt
  wpp_init x s0
  have hinv0 : LsClInv s0 := by assumption
  have hdropSender := @ApplyTailSteps.SepWPp_drop_old_sender_placed _ A H
    calleeStack stubStack mkStack chStack hcallee hstub_le hmk_le hch_le hdealloc hdropMk
  have htail14c := @ApplyTailSteps.SepWPp_tail_14c_to_184_placed _ A H
    calleeStack stubStack chStack hcallee hstub_le hch_le hdealloc
  obtain ⟨t, trG, tr, ss, G, st⟩ := x
  dsimp only at *
  have hx0_eq : s0.readReg64 .x0 = t := by assumption
  have hx1_eq : s0.readReg64 .x1 = ss := by assumption
  subst hx0_eq hx1_eq
  refine SepWPp.weaken_pre (sepConj_mono (trAt_expose A (s0.readReg64 .x0) trG tr)
    (sepConj_mono (sessionStateAt_expose_apply A (s0.readReg64 .x1) G st)
      (sepConj_mono (Entails.of_eq (hstack_open s0.sp)) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat refine SepWPp.exists_elim fun _ => ?_
  refine SepWPp.pure_elim fun ⟨hclamp, hchains_len, hpad_len, hmax_jumps⟩ => ?_
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine SepWPp.pure_elim fun ⟨hG_chains_len, hroot_pos, hroot_lt, hroot_c0, hroot_ptr, hGs_eq⟩ => ?_
  have hroot_layout : LayoutOk G.root.cap.toNat 1 := layoutOk_of_pos_lt hroot_pos hroot_lt
  obtain ⟨scw0, scw1, scw2, scw3, scw4, scw5, scw6, scw7, scw8, scw9, scw10, scw11, scw12, hsc_unpack⟩ :=
    exists_unpack64_of_length_104 (optSenderChainBytes_length tr.ratchet.senderChain hpad_len)
  obtain ⟨rkw0, rkw1, rkw2, rkw3, hrk_eq, hrk_unpack⟩ :=
    exists_unpack64_of_length_32 (bs := CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey)
      (length_keyToBytes32 _)
  clear hrk_eq
  rw [hsc_unpack (s0.readReg64 .x0 + 24#64), hrk_unpack (s0.readReg64 .x0 + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  have hlayout33 : LayoutOk 33 1 := ⟨by decide, hpow1, by decide⟩
  refine SepWPp.fold (stackAt_ext_to_gen s0.sp calleeStack stubStack hcallee hstub_le) (by sep_focus) ?_
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (104)) hinv0
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0
  · simp only [hoom1, ite_true]
    have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = true := by simp [hoom1]
    refine SepWPp_pure_elim3 fun htr_oom => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hpanic (by simp only [arm64_norm, *])
  · simp only [hoom1, ite_false, sepConj_assoc]
    have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
    refine SepWPp_pure_elim3 fun ⟨_halign1, htr1⟩ => ?_
    rw [memRegion_32_unpack (sf_1.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ =>
      SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ => ?_
    refine SepWPp.fold (hsc_stack_pack hsc_unpack) (by sep_focus) ?_
    refine SepWPp.fold (hsc_tr_pack hsc_unpack) (by sep_focus) ?_
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (140)) hinv1
    wp_steps
    wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    refine SepWPp.fold (hrk_pack hrk_unpack) (by sep_focus) ?_
    refine SepWPp.fold (hrk_tr_pack hrk_unpack) (by sep_focus) ?_
    clear hsc_unpack hrk_unpack scw0 scw1 scw2 scw3 scw4 scw5 scw6 scw7 scw8 scw9 scw10 scw11 scw12 rkw0 rkw1 rkw2 rkw3
    cases hsc : tr.ratchet.senderChain with
    | none =>
      rw [optSenderChainBytes_none_stack_eq s0.sp trG.ratchet.senderPad]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (208)) hinv2
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_208
      refine SepWPp.fold (stack_104_none_to_memRegion s0.sp trG.ratchet.senderPad hpad_len) (by sep_focus) ?_
      refine SepWPp.fold (vecU8At_fold_exact A (s0.readReg64 .x1 + 48#64) 32#64 (sf_1.readReg64 .x0)
        (CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey) 32 rfl (length_keyToBytes32 _)
        (by decide) (by decide) hoom1) (by sep_focus) ?_
      refine hdropSender s0.sp (s0.readReg64 .x1) hinv_208 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hGs_eq (by sep_focus) (by simp only [arm64_norm, *])
        fun sf_ds _ _ _ _ _ _ _ _ _ _ _ _ _ hpc_ds hrun_ds hsp_ds htr_ds hcs_ds hinv_ds => ?_
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_ds
      rcases hcs_ds with ⟨hcs_d19, hcs_d20, hcs_d21, hcs_d22, hcs_d23, hcs_d24, hcs_d25, hcs_d26, hcs_d27, hcs_d28, hcs_d29, hcs_dv⟩
      simp only [arm64_norm, *] at hcs_d19 hcs_d20 hcs_d21 hcs_d22 hcs_d23 hcs_d24 hcs_d25 hcs_d26 hcs_d27 hcs_d28 hcs_d29 hcs_dv
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_58).base + bv% (332))
      apply SepWP.of_sepWP_lscl_frozen (mid := lsmpl.base 2) hinv_ds
      wp_steps
      apply SepWP.done_frozen (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_call_dc
      wp_call (lscall_blk_cl (callerProg := (blkPC_58).rebase (blkPl_58).base H)
        (spec := dropVecChainSpecAt A chStack) hdropCh hinv_call_dc)
        ⟨s0.readReg64 .x1 + 72#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
      clear hinv_call_dc
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPp.fold (optSenderChainAt_none_fold A (s0.readReg64 .x1) _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine htail14c s0.sp (s0.readReg64 .x1) (s0.readReg64 .x0)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hchains_len (by sep_focus) (by simp only [arm64_norm, *]) fun sf_tl hpc_tl hrun_tl hsp_tl htr_tl hvregs_tl => ?_
      simp only [arm64_norm, *] at hvregs_tl
      simp only [sepConj_assoc]
      have hsc_sym : (none : Option SenderChain) = tr.ratchet.senderChain := hsc.symm
      rw [hsc_sym]
      refine SepWPp.fold (sessionStateAt_reassemble_apply A (s0.readReg64 .x1) G st trG tr
        (sf_1.readReg64 .x0) none hchains_len) (by sep_focus) ?_
      refine SepWPp.fold (trAt_in_struct_entails_memRegion (s0.readReg64 .x0) trG tr hpad_len) (by sep_focus) ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (hstack_fold s0.sp s0) (by sep_focus) ?_
      apply SepWP_instantiate_post_exists_outer (mkApplyGhost G trG (sf_1.readReg64 .x0) none)
      have hrel := trApplyRel_mkApplyGhost G trG (sf_1.readReg64 .x0) none
      wp_done
    | some sc =>
      have hclamp_sc : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes :=
        hclamp sc hsc
      obtain ⟨ckw0, ckw1, ckw2, ckw3, hck_eq, hck_unpack⟩ :=
        exists_unpack64_of_length_32 (bs := CryptoGames.HMAC.keyToBytes32 sc.chainKey.key)
          (length_keyToBytes32 _)
      clear hck_eq
      rw [optSenderChainBytes_some_stack_eq s0.sp sc trG.ratchet.senderPad,
          optSenderChainBytes_some_tr_eq (s0.readReg64 .x0) sc trG.ratchet.senderPad hck_unpack]
      simp only [sepConj_assoc]
      have horr4 : (s0.sp - 224#64) ||| 4#64 = s0.sp - 220#64 := sp_sub_224_orr_4 hsp_align
      refine SepWPp_fold_stack_gen s0.sp calleeStack stubStack pkStack hcallee hstub_le hpk_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 205) hinv2
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_pk0
      refine SepWPp.fold (vecU8At_fold_exact A (s0.readReg64 .x1 + 48#64) 32#64 (sf_1.readReg64 .x0)
        (CryptoGames.HMAC.keyToBytes32 tr.ratchet.rootKey) 32 rfl (length_keyToBytes32 _)
        (by decide) (by decide) hoom1) (by sep_focus) ?_
      refine SepWPp_call_pk_lscl hpk hinv_pk0 sc.ratchetKey.publicKey
        (ret_pc := (blkPl_58).base + bv% (180)) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by sep_focus) fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk hinv_pk => ?_
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
      rcases hcs_pk with ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28, hcs_k29, hcs_kv⟩
      simp only [arm64_norm, *] at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29 hcs_kv
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hpk_x1, hpk_tr⟩ => ?_
      refine SepWPp.fold (boxU8Buf_pk_expose A (sf_pk.readReg64 .x0) sc.ratchetKey.publicKey) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun hpk_ptr => ?_
      refine SepWPp_fold_stack_gen s0.sp calleeStack pkStack stubStack hcallee hpk_le hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (448)) hinv_pk
      wp_steps
      wp_call hshim ()
      wp_steps
      wp_call halloc (33, 1)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv4
      by_cases hoom_srk : sf_4.readReg64 Reg.x0 = 0
      · simp only [hoom_srk, ite_true]
        have hoom_srk_beq : (sf_4.readReg64 Reg.x0 == 0#64) = true := by simp [hoom_srk]
        refine SepWPp_pure_elim3 fun htr_oom_srk => ?_
        apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hpanic (by simp only [arm64_norm, *])
      · simp only [hoom_srk, ite_false, sepConj_assoc]
        have hoom_srk_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_srk
        refine SepWPp_pure_elim3 fun ⟨_halign_srk, htr_srk⟩ => ?_
        have hsrk_len : sc.ratchetKey.publicKey.serialize.length = 33 :=
          serialize_pk_length sc.ratchetKey.publicKey
        have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
          sc.ratchetKey.privateKey.bytes.toList_length
        have hfp_sub24 : s0.sp - 96#64 - 24#64 = s0.sp - 120#64 := by rw [BitVec.sub_sub]; rfl
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 208) hinv4
        wp_steps
        wp_call hmemcpy (sf_4.readReg64 .x0, sf_pk.readReg64 .x0,
          sc.ratchetKey.publicKey.serialize)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv_priv0
        refine SepWPp_fold_stack_gen s0.sp calleeStack stubStack privStack hcallee hstub_le hpriv_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
        refine SepWPp.fold (pk_buf_to_memRegion (sf_pk.readReg64 .x0) sc.ratchetKey.publicKey) (by sep_focus) ?_
        refine SepWPp_call_priv_lscl hpriv hinv_priv0 sc.ratchetKey.privateKey.bytes.toList
          (ret_pc := (blkPl_58).base + bv% (484)) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by sep_focus) fun sf_priv hpc_priv hrun_priv hsp_priv hcs_priv hinv_priv => ?_
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_priv
        rcases hcs_priv with ⟨hcs_p19, hcs_p20, hcs_p21, hcs_p22, hcs_p23, hcs_p24, hcs_p25, hcs_p26, hcs_p27, hcs_p28, hcs_p29, hcs_pv⟩
        simp only [arm64_norm, *] at hcs_p19 hcs_p20 hcs_p21 hcs_p22 hcs_p23 hcs_p24 hcs_p25 hcs_p26 hcs_p27 hcs_p28 hcs_p29 hcs_pv
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hpriv_tr => ?_
        refine SepWPp.fold (vecU8_priv_expose_stack A s0.sp sc.ratchetKey.privateKey.bytes) (by sep_focus) ?_
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun privTempCap => SepWPp.exists_elim fun privTempPtr => ?_
        refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_c0, hpt_ptr⟩ => ?_
        have hpt_layout : LayoutOk privTempCap.toNat 1 :=
          layoutOk_of_pos_lt (Nat.lt_of_lt_of_le (by decide : 0 < 32) hpt_le) hpt_lt
        refine SepWPp_fold_stack_gen s0.sp calleeStack privStack stubStack hcallee hpriv_le hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (564)) hinv_priv
        wp_steps
        wp_call hshim ()
        wp_steps
        wp_call halloc (32, 1)
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv7
        by_cases hoom_priv : sf_7.readReg64 Reg.x0 = 0
        · simp only [hoom_priv, ite_true]
          have hoom_priv_beq : (sf_7.readReg64 Reg.x0 == 0#64) = true := by simp [hoom_priv]
          refine SepWPp_pure_elim3 fun htr_oom_priv => ?_
          apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hpanic (by simp only [arm64_norm, *])
        · simp only [hoom_priv, ite_false, sepConj_assoc]
          have hoom_priv_beq : (sf_7.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_priv
          refine SepWPp_pure_elim3 fun ⟨_halign_priv, htr_priv⟩ => ?_
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (604)) hinv7
          wp_steps
          wp_call hmemcpy (sf_7.readReg64 .x0, privTempPtr, sc.ratchetKey.privateKey.bytes.toList)
          wp_steps
          wp_call hshim ()
          wp_steps
          wp_call halloc (32, 1)
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hinv10
          by_cases hoom_ck : sf_10.readReg64 Reg.x0 = 0
          · simp only [hoom_ck, ite_true]
            have hoom_ck_beq : (sf_10.readReg64 Reg.x0 == 0#64) = true := by simp [hoom_ck]
            refine SepWPp_pure_elim3 fun htr_oom_ck => ?_
            apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hpanic (by simp only [arm64_norm, *])
          · simp only [hoom_ck, ite_false, sepConj_assoc]
            have hoom_ck_beq : (sf_10.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_ck
            refine SepWPp_pure_elim3 fun ⟨_halign_ck, htr_ck⟩ => ?_
            rw [memRegion_32_unpack (sf_10.readReg64 Reg.x0)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ =>
              SepWPp.exists_elim fun _ => SepWPp.exists_elim fun _ => ?_
            refine SepWPp.fold (priv_buf_to_memRegion privTempPtr privTempCap
              sc.ratchetKey.privateKey.bytes hpt_le hpt_lt) (by sep_focus) ?_
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_58).base + bv% (208)) hinv10
            wp_steps
            wp_call hdealloc (privTempPtr, privTempCap.toNat, 1)
            wp_steps
            wp_call hdealloc (sf_pk.readReg64 .x0, 33, 1)
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv_208
            refine SepWPp.fold (hrk_pack hck_unpack) (by sep_focus) ?_
            refine SepWPp.fold (hck_tr_pack trG.ratchet.senderPad hck_unpack) (by sep_focus) ?_
            refine SepWPp.fold (stack_104_some_to_memRegion s0.sp sc trG.ratchet.senderPad hpad_len) (by sep_focus) ?_
            refine SepWPp.fold (stack_24_to_memRegion s0.sp privTempCap privTempPtr 32#64) (by sep_focus) ?_
            clear hck_unpack ckw0 ckw1 ckw2 ckw3
            refine hdropSender s0.sp (s0.readReg64 .x1) hinv_208 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hGs_eq (by sep_focus) (by simp only [arm64_norm, *])
              fun sf_ds _ _ _ _ _ _ _ _ _ _ _ _ _ hpc_ds hrun_ds hsp_ds htr_ds hcs_ds hinv_ds => ?_
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_ds
            rcases hcs_ds with ⟨hcs_d19, hcs_d20, hcs_d21, hcs_d22, hcs_d23, hcs_d24, hcs_d25, hcs_d26, hcs_d27, hcs_d28, hcs_d29, hcs_dv⟩
            simp only [arm64_norm, *] at hcs_d19 hcs_d20 hcs_d21 hcs_d22 hcs_d23 hcs_d24 hcs_d25 hcs_d26 hcs_d27 hcs_d28 hcs_d29 hcs_dv
            simp only [sepConj_assoc]
            apply SepWPp.of_sepWP (mid := (blkPl_58).base + bv% (332))
            apply SepWP.of_sepWP_lscl_frozen (mid := lsmpl.base 2) hinv_ds
            wp_steps
            apply SepWP.done_frozen (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv_call_dc
            wp_call (lscall_blk_cl (callerProg := (blkPC_58).rebase (blkPl_58).base H)
              (spec := dropVecChainSpecAt A chStack) hdropCh hinv_call_dc)
              ⟨s0.readReg64 .x1 + 72#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
            clear hinv_call_dc
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            refine SepWPp.fold (optSenderChainAt_some_fold A (s0.readReg64 .x1) sc
              (sf_4.readReg64 .x0) (sf_7.readReg64 .x0) (sf_10.readReg64 .x0)
              hclamp_sc hoom_srk hoom_priv hoom_ck) (by sep_focus) ?_
            refine htail14c s0.sp (s0.readReg64 .x1) (s0.readReg64 .x0)
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hsp_align (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hchains_len (by sep_focus) (by simp only [arm64_norm, *]) fun sf_tl hpc_tl hrun_tl hsp_tl htr_tl hvregs_tl => ?_
            simp only [arm64_norm, *] at hvregs_tl
            simp only [sepConj_assoc]
            have hsc_sym : (some sc : Option SenderChain) = tr.ratchet.senderChain := hsc.symm
            rw [hsc_sym]
            refine SepWPp.fold (sessionStateAt_reassemble_apply A (s0.readReg64 .x1) G st trG tr
              (sf_1.readReg64 .x0)
              (some (mkSenderChainGhost sc (sf_4.readReg64 .x0) (sf_7.readReg64 .x0) (sf_10.readReg64 .x0)))
              hchains_len) (by sep_focus) ?_
            refine SepWPp.fold (trAt_in_struct_entails_memRegion (s0.readReg64 .x0) trG tr hpad_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret
            wp_steps
            refine SepWP.fold (hstack_fold s0.sp s0) (by sep_focus) ?_
            apply SepWP_instantiate_post_exists_outer (mkApplyGhost G trG (sf_1.readReg64 .x0)
              (some (mkSenderChainGhost sc (sf_4.readReg64 .x0) (sf_7.readReg64 .x0) (sf_10.readReg64 .x0))))
            have hrel := trApplyRel_mkApplyGhost G trG (sf_1.readReg64 .x0)
              (some (mkSenderChainGhost sc (sf_4.readReg64 .x0) (sf_7.readReg64 .x0) (sf_10.readReg64 .x0)))
            wp_done

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

private theorem memcpyWithStack_of_framelessMemcpy {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr (memcpySpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_mono h' (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpySpec, memcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withStack, framelessMemcpySpec, memcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

/-- Relocatable `TR::apply_to_session_state` (Block `58`) meets
`withLsCodeLoaded lsmpl (trApplySpec A)`. -/
theorem trApply_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpec A))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec A))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpec A)) :=
  trApply_placed_ok_opt
    (calleeStack := extHookStack) (stubStack := allocHookStack)
    (mkStack := dropVecMessageKeyStack) (chStack := dropVecChainStack)
    (pkStack := publicKeySerializeStack) (privStack := extHookStack)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    stackAt_trApply stackAt_trApply_fold
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))
    ((ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic)
    (priv_serialize_placed_ok_at (prog := (blkPC_58).rebase (blkPl_58).base H) hshim halloc hpanic)
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain (public_key_serialize_placed_ok hshim halloc hpanic)))
    (subroutine_ok_withLsCodeLoaded_of_plain hdropMk)
    hdropCh

end ReceiveRatchetApply

end CryptoVerification.LibsignalTripleRatchet
