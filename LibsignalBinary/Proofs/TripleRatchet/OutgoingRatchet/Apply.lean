/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.OutgoingRatchetCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `OutgoingTripleRatchet::apply_to_session_state`

Verifies `<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state`
against `otrApplyRawSpec`, `otrApplySpec`, and `otrApplyPlacedSpec`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``sessionStateAt, #[1]), (``otrAt, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

/-! ## Byte and region helpers -/

theorem keyToBytes32_length (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

/-- Pack a byte list into a `w`-bit word in little-endian order. -/
@[expose] def packBV (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

/-- Pack 8 bytes into a 64-bit little-endian word. -/
@[expose] def pack64 (bs : List (BitVec 8)) : BitVec 64 := packBV 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h
  simp only [unpack64, pack64, packBV, List.foldr, List.cons.injEq, and_true]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

theorem pointsToBytes_32_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h0,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 8).take 8) h1,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 16).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha24, ha16, ha8]

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := keyToBytes32_length ck.key
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

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

/-- Stack layout for `OTR::apply_to_session_state` (`otrApplyInternalStack = 128 + allocHookStack`). -/
theorem stackAt_otrApply (sp : BitVec 64) :
    stackAt sp otrApplyInternalStack =
      stackAt (sp - 128#64) allocHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s1 : BitVec 64, (sp - 120#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      (∃∗ s3 : BitVec 32, (sp - 100#64) ↦₃₂ s3) ∗
      (∃∗ s4 : BitVec 64, (sp - 96#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (sp - 88#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (sp - 80#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (sp - 72#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (sp - 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (sp - 56#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (sp - 48#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (sp - 40#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (sp - 32#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (sp - 24#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (sp - 16#64) ↦₆₄ s14) ∗
      (∃∗ s15 : BitVec 64, (sp - 8#64) ↦₆₄ s15) := by
  dsimp only [stackAt, otrApplyInternalStack, allocHookStack]; sep_interval_eq

theorem stackAt_otrApply_fold (sp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64)
    (s3 : BitVec 32) :
    stackAt (sp - 128#64) allocHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      ((sp - 120#64) ↦₆₄ s1) ∗
      ((sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      ((sp - 100#64) ↦₃₂ s3) ∗
      ((sp - 96#64) ↦₆₄ s4) ∗
      ((sp - 88#64) ↦₆₄ s5) ∗
      ((sp - 80#64) ↦₆₄ s6) ∗
      ((sp - 72#64) ↦₆₄ s7) ∗
      ((sp - 64#64) ↦₆₄ s8) ∗
      ((sp - 56#64) ↦₆₄ s9) ∗
      ((sp - 48#64) ↦₆₄ s10) ∗
      ((sp - 40#64) ↦₆₄ s11) ∗
      ((sp - 32#64) ↦₆₄ s12) ∗
      ((sp - 24#64) ↦₆₄ s13) ∗
      ((sp - 16#64) ↦₆₄ s14) ∗
      ((sp - 8#64) ↦₆₄ s15) ⊢
    stackAt sp otrApplyInternalStack := by
  dsimp only [stackAt, otrApplyInternalStack, allocHookStack]; sep_interval

/-! ## Decomposition of `otrAt` and `sessionStateAt` for `OTR::apply_to_session_state` -/

/-- The heap part of `vecU8At A v cap ptr bs` without the 24-byte header at `v`. -/
@[expose] def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_cells_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  simp only [vecU8At, vecHeader, vecU8Buf, sepConj_assoc]

theorem vecU8Buf_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => Entails.pure_right h ?_
  split
  · exact Entails.refl _
  · refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
    rw [← memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega),
      Nat.add_sub_of_le h.1]
    exact Entails.refl _

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  sep_interval_eq

theorem cells_32_entails_memRegion (a w0 w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ⊢
      memRegion a 32 := by
  sep_interval

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Decompose `otrAt A o pqCap pqPtr ot` into the fields read by `OTR::apply_to_session_state`
and the rest as `memRegion`. -/
theorem otrAt_apply_split (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    let kbs := keyToBytes32 ot.senderChainKey.key
    otrAt A o pqCap pqPtr ot ⊢
      (o ↦₆₄ pqCap) ∗ ((o + 8#64) ↦₆₄ pqPtr) ∗
      ((o + 16#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      vecU8Buf A pqCap pqPtr ot.pqrState ∗
      memRegion (o + 0x18#64) 128 ∗
      ((o + 0x98#64) ↦₆₄ pack64 (kbs.take 8)) ∗
      ((o + 0xa0#64) ↦₆₄ pack64 ((kbs.drop 8).take 8)) ∗
      ((o + 0xa8#64) ↦₆₄ pack64 ((kbs.drop 16).take 8)) ∗
      ((o + 0xb0#64) ↦₆₄ pack64 (kbs.drop 24)) ∗
      ((o + 0xb8#64) ↦₃₂ ot.senderChainKey.index) ∗
      memRegion (o + 0xbc#64) 12 := by
  intro kbs
  unfold otrAt
  rw [vecU8At_eq_cells_buf A o pqCap pqPtr ot.pqrState,
      chainKeyBytes_pointsTo (o + 0x98#64) ot.senderChainKey,
      pointsToBytes_32_eq_pointsTo64 (o + 0x98#64) kbs (keyToBytes32_length _)]
  simp only [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  have := ot.senderRatchetKey.publicKey.bytes.toList_length
  have := ot.senderRatchetKey.privateKey.bytes.toList_length
  have := ot.localIdentityKey.publicKey.bytes.toList_length
  have := ot.remoteIdentityKey.publicKey.bytes.toList_length
  sep_interval

/-- Fold the remaining fields of `o` into `memRegion o 200`. -/
theorem otr_fold_memRegion (o w0 w1 w2 ck0 ck1 ck2 ck3 : BitVec 64) (idx : BitVec 32) :
    ((o ↦₆₄ w0) ∗ ((o + 8#64) ↦₆₄ w1) ∗ ((o + 16#64) ↦₆₄ w2) ∗
      memRegion (o + 0x18#64) 128 ∗
      ((o + 0x98#64) ↦₆₄ ck0) ∗ ((o + 0xa0#64) ↦₆₄ ck1) ∗
      ((o + 0xa8#64) ↦₆₄ ck2) ∗ ((o + 0xb0#64) ↦₆₄ ck3) ∗
      ((o + 0xb8#64) ↦₃₂ idx) ∗ memRegion (o + 0xbc#64) 12) ⊢
    memRegion o 200 := by
  sep_interval

/-- The untouched fields of `sessionStateAt A ss G st` during `OTR::apply_to_session_state`. -/
@[expose] def sessionApplyFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
    sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
    sg.srk.bytes.length = 33⌝ ∗
    vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8Buf A sg.priv.cap sg.priv.ptr sg.priv.bytes ∗
    vecBuf A 104 8 (messageKeyAt A) sg.mkCap sg.mkPtr [] ∗
    memRegion (ss + 0xf4#64) 4 ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem vecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem vecU8Buf_dealloc_32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 32) :
    vecU8Buf A cap ptr bs ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  refine Entails.trans (vecU8Buf_dealloc A cap ptr bs) ?_
  rw [hbs]
  refine Entails.pure_left fun h => Entails.pure_right h ?_
  have hne : cap ≠ 0 := by
    intro hc; subst hc; simp at h
  rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
  exact Entails.refl _

/-- Bidirectional decomposition of `sessionStateAt` exposing the `pq_ratchet_state` and
`sender_chain` cells touched by `OTR::apply_to_session_state` while framing the untouched fields
in `sessionApplyFrame`. -/
theorem sessionStateAt_eq_apply (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain)
    (pqPin : VecPin) (pqBs : List (BitVec 8)) (ckPin : VecPin) (ck : ChainKey) :
    sessionStateAt A ss
      { G with sender := some ({ sg with ck := ckPin }), pq := pqPin }
      { st with senderChain := some ({ sc with chainKey := ck }), pqRatchetState := pqBs } =
      (((ss + 0x78#64) ↦₆₄ pqPin.cap) ∗ ((ss + 0x80#64) ↦₆₄ pqPin.ptr) ∗
        ((ss + 0x88#64) ↦₆₄ BitVec.ofNat 64 pqBs.length) ∗
        vecU8Buf A pqPin.cap pqPin.ptr pqBs ∗
        ((ss + 0x90#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 0x98#64) ↦₆₄ sg.srk.ptr) ∗
        ((ss + 0xa0#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
        vecU8Buf A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
        ((ss + 0xa8#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 0xb0#64) ↦₆₄ sg.priv.ptr) ∗
        ((ss + 0xb8#64) ↦₆₄ BitVec.ofNat 64 sg.priv.bytes.length) ∗
        ((ss + 0xc0#64) ↦₆₄ sg.mkCap) ∗ ((ss + 0xc8#64) ↦₆₄ sg.mkPtr) ∗
        ((ss + 0xd0#64) ↦₆₄ 0#64) ∗
        ((ss + 0xd8#64) ↦₆₄ ckPin.cap) ∗ ((ss + 0xe0#64) ↦₆₄ ckPin.ptr) ∗
        ((ss + 0xe8#64) ↦₆₄ 32#64) ∗
        ((ss + 0xf0#64) ↦₃₂ ck.index) ∗
        vecU8Buf A ckPin.cap ckPin.ptr (keyToBytes32 ck.key) ∗
        sessionApplyFrame A ss G st sg sc) := by
  unfold sessionStateAt sessionApplyFrame optSenderChainAt vecGhostAt optChainKeyAt vecAt vecHeader
  simp only [vecU8At_eq_cells_buf, keyToBytes32_length, List.length_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

/-- Extract `G.sender = some sg` from `sessionStateAt A ss G st` when `st.senderChain = some sc`. -/
theorem sessionStateAt_sender_some (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sc : SenderChain) (hsc : st.senderChain = some sc) :
    sessionStateAt A ss G st ⊢ ∃∗ sg : SenderChainGhost, ⌜G.sender = some sg⌝ ∗ sessionStateAt A ss G st := by
  cases hGs : G.sender with
  | none =>
    unfold sessionStateAt; rw [hsc, hGs]; dsimp only [optSenderChainAt]
    refine Entails.pure_left fun _ => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    exact Entails.pure_left False.elim
  | some sg =>
    exact Entails.sepExists_right sg (Entails.pure_right rfl (Entails.refl _))

/-- Fold a freshly allocated 32-byte block with the four 64-bit words of `keyToBytes32 k` into
`vecU8Buf A 32#64 p' (keyToBytes32 k)`. -/
theorem vecU8Buf_of_cells_32 (A : RustAlloc) (p' : BitVec 64) (k : BitVec 256) (hp' : p' ≠ 0#64) :
    let kbs := keyToBytes32 k
    A.live p' 32 1 ∗
      ((p' ↦₆₄ pack64 (kbs.take 8)) ∗
       ((p' + 8#64) ↦₆₄ pack64 ((kbs.drop 8).take 8)) ∗
       ((p' + 16#64) ↦₆₄ pack64 ((kbs.drop 16).take 8)) ∗
       ((p' + 24#64) ↦₆₄ pack64 (kbs.drop 24))) ⊢
    vecU8Buf A 32#64 p' (keyToBytes32 k) := by
  intro kbs
  rw [← pointsToBytes_32_eq_pointsTo64 p' kbs (keyToBytes32_length k)]
  unfold vecU8Buf
  have hne : (32#64 : BitVec 64) ≠ 0 := by decide
  rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
  simp only [keyToBytes32_length, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨by decide, by decide, hp'⟩ (Entails.refl _)

theorem applyRel_afterOtrApply (G : SessionGhost) (sg : SenderChainGhost)
    (hGs : G.sender = some sg) (ckPtr pqCap pqPtr : BitVec 64) :
    G.AfterOutgoingRatchetApply (afterOtrApply G sg ckPtr pqCap pqPtr) ∧
      (afterOtrApply G sg ckPtr pqCap pqPtr).pq = ⟨pqCap, pqPtr⟩ := by
  refine ⟨⟨sg, { sg with ck := ⟨32#64, ckPtr⟩ }, hGs, rfl, rfl, rfl⟩, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem int64_toBitVec_ofUInt64 (u : UInt64) : (Int64.ofUInt64 u).toBitVec = u.toBitVec := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem uint64_toBitVec_ofBitVec (b : BitVec 64) : (UInt64.ofBitVec b).toBitVec = b := rfl

private theorem addsPState64_hi_false_aux {cap : BitVec 64}
    (h1 : (32#64).ule cap = true) (h2 : cap.ult 0x8000000000000000#64 = true) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  dsimp only
  bv_kernel

private theorem addsPState64_hi_false {cap ptr : BitVec 64}
    (h : 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  apply addsPState64_hi_false_aux
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq]; exact h.1
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq]; exact h.2.1

namespace ApplyFrameFacts

theorem elim_ex {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {C : α → SepProp} {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog pc s (R ∗ C x) post) :
    SepWP prog pc s ((∃∗ x, C x) ∗ R) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_elim fun x => by rw [sepConj_comm]; exact h x

theorem skip_atom {prog : Program} {pc : BitVec 64} {s : State}
    {A R : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog pc s (R ∗ A) post) :
    SepWP prog pc s (A ∗ R) post := by
  rw [sepConj_comm]
  exact h

theorem sepWP_unpack_stackAt_otrApply {prog : Program} {pc : BitVec 64} {s : State}
    (sp : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = stackAt sp otrApplyInternalStack ∗ F)
    (h : ∀ (s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64) (s3 : BitVec 32),
      SepWP prog pc s
        ((stackAt (sp - 128#64) allocHookStack ∗
          memRegion (sp - 128#64) 8 ∗
          ((sp - 120#64) ↦₆₄ s1) ∗
          ((sp - 112#64) ↦₆₄ s2) ∗
          memRegion (sp - 104#64) 4 ∗
          ((sp - 100#64) ↦₃₂ s3) ∗
          ((sp - 96#64) ↦₆₄ s4) ∗
          ((sp - 88#64) ↦₆₄ s5) ∗
          ((sp - 80#64) ↦₆₄ s6) ∗
          ((sp - 72#64) ↦₆₄ s7) ∗
          ((sp - 64#64) ↦₆₄ s8) ∗
          ((sp - 56#64) ↦₆₄ s9) ∗
          ((sp - 48#64) ↦₆₄ s10) ∗
          ((sp - 40#64) ↦₆₄ s11) ∗
          ((sp - 32#64) ↦₆₄ s12) ∗
          ((sp - 24#64) ↦₆₄ s13) ∗
          ((sp - 16#64) ↦₆₄ s14) ∗
          ((sp - 8#64) ↦₆₄ s15)) ∗ F) post) :
    SepWP prog pc s P post := by
  have hnext :=
    SepWP.exists_elim fun s1 => SepWP.exists_elim fun s2 => SepWP.exists_elim fun s4 =>
    SepWP.exists_elim fun s5 => SepWP.exists_elim fun s6 => SepWP.exists_elim fun s7 =>
    SepWP.exists_elim fun s8 => SepWP.exists_elim fun s9 => SepWP.exists_elim fun s10 =>
    SepWP.exists_elim fun s11 => SepWP.exists_elim fun s12 => SepWP.exists_elim fun s13 =>
    SepWP.exists_elim fun s14 => SepWP.exists_elim fun s15 => SepWP.exists_elim fun s3 =>
    h s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3
  rw [hf, stackAt_otrApply sp]
  bi_entail

end ApplyFrameFacts

/-- Split the 64 KiB `smallRootStack` into the 61312-byte unused prefix and the 4224-byte
`otrApplyInternalStack` frame. -/
theorem smallRootStack_split_otrApply (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 smallRootStack) smallRootStack =
      (memRegion (sp - 65536#64) 61312 ∗
       memRegion (sp - BitVec.ofNat 64 otrApplyInternalStack) otrApplyInternalStack) := by
  simp only [smallRootStack, otrApplyInternalStack, allocHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

abbrev otrApplyInternalStackX : Nat := 0x80 + extHookStack

@[expose] def otrApplyRawSpecX (A : RustAlloc) : Spec OtrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
      otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp otrApplyInternalStackX ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
        sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
      memRegion x.o 200 ∗ stackAt s0.sp otrApplyInternalStackX ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem stackAt_otrApplyX (sp : BitVec 64) :
    stackAt sp otrApplyInternalStackX =
      stackAt (sp - 128#64) extHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s1 : BitVec 64, (sp - 120#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      (∃∗ s3 : BitVec 32, (sp - 100#64) ↦₃₂ s3) ∗
      (∃∗ s4 : BitVec 64, (sp - 96#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (sp - 88#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (sp - 80#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (sp - 72#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (sp - 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (sp - 56#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (sp - 48#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (sp - 40#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (sp - 32#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (sp - 24#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (sp - 16#64) ↦₆₄ s14) ∗
      (∃∗ s15 : BitVec 64, (sp - 8#64) ↦₆₄ s15) := by
  simp only [stackAt, otrApplyInternalStackX, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

theorem stackAt_otrApplyX_fold (sp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64)
    (s3 : BitVec 32) :
    stackAt (sp - 128#64) extHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      ((sp - 120#64) ↦₆₄ s1) ∗
      ((sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      ((sp - 100#64) ↦₃₂ s3) ∗
      ((sp - 96#64) ↦₆₄ s4) ∗
      ((sp - 88#64) ↦₆₄ s5) ∗
      ((sp - 80#64) ↦₆₄ s6) ∗
      ((sp - 72#64) ↦₆₄ s7) ∗
      ((sp - 64#64) ↦₆₄ s8) ∗
      ((sp - 56#64) ↦₆₄ s9) ∗
      ((sp - 48#64) ↦₆₄ s10) ∗
      ((sp - 40#64) ↦₆₄ s11) ∗
      ((sp - 32#64) ↦₆₄ s12) ∗
      ((sp - 24#64) ↦₆₄ s13) ∗
      ((sp - 16#64) ↦₆₄ s14) ∗
      ((sp - 8#64) ↦₆₄ s15) ⊢
    stackAt sp otrApplyInternalStackX := by
  simp only [stackAt, otrApplyInternalStackX, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval

namespace ApplyFrameFacts

theorem sepWP_unpack_stackAt_otrApplyX {prog : Program} {pc : BitVec 64} {s : State}
    (sp : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = stackAt sp otrApplyInternalStackX ∗ F)
    (h : ∀ (s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64) (s3 : BitVec 32),
      SepWP prog pc s
        ((stackAt (sp - 128#64) extHookStack ∗
          memRegion (sp - 128#64) 8 ∗
          ((sp - 120#64) ↦₆₄ s1) ∗
          ((sp - 112#64) ↦₆₄ s2) ∗
          memRegion (sp - 104#64) 4 ∗
          ((sp - 100#64) ↦₃₂ s3) ∗
          ((sp - 96#64) ↦₆₄ s4) ∗
          ((sp - 88#64) ↦₆₄ s5) ∗
          ((sp - 80#64) ↦₆₄ s6) ∗
          ((sp - 72#64) ↦₆₄ s7) ∗
          ((sp - 64#64) ↦₆₄ s8) ∗
          ((sp - 56#64) ↦₆₄ s9) ∗
          ((sp - 48#64) ↦₆₄ s10) ∗
          ((sp - 40#64) ↦₆₄ s11) ∗
          ((sp - 32#64) ↦₆₄ s12) ∗
          ((sp - 24#64) ↦₆₄ s13) ∗
          ((sp - 16#64) ↦₆₄ s14) ∗
          ((sp - 8#64) ↦₆₄ s15)) ∗ F) post) :
    SepWP prog pc s P post := by
  have hnext :=
    SepWP.exists_elim fun s1 => SepWP.exists_elim fun s2 => SepWP.exists_elim fun s4 =>
    SepWP.exists_elim fun s5 => SepWP.exists_elim fun s6 => SepWP.exists_elim fun s7 =>
    SepWP.exists_elim fun s8 => SepWP.exists_elim fun s9 => SepWP.exists_elim fun s10 =>
    SepWP.exists_elim fun s11 => SepWP.exists_elim fun s12 => SepWP.exists_elim fun s13 =>
    SepWP.exists_elim fun s14 => SepWP.exists_elim fun s15 => SepWP.exists_elim fun s3 =>
    h s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3
  rw [hf, stackAt_otrApplyX sp]
  bi_entail

end ApplyFrameFacts

theorem smallRootStack_split_otrApplyX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 smallRootStack) smallRootStack =
      (memRegion (sp - 65536#64) 49024 ∗
       memRegion (sp - BitVec.ofNat 64 otrApplyInternalStackX) otrApplyInternalStackX) := by
  simp only [smallRootStack, otrApplyInternalStackX, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

/-! ## Relocatable `[LibsignalPlacement]` contracts -/

/-- Relocatable root-level specification of `OTR::apply_to_session_state`. -/
@[expose] def otrApplyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec OtrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
      otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
        sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
      memRegion x.o 200 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `OTR::apply_to_session_state` meets `otrApplyRawSpec A` from hook
`subroutine_ok` contracts. -/
theorem otrApplyRaw_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpanic : ((blkPC_20).rebase (blkPl_20).base H).externAt?
      (lsρ lsHandleErrorSym) = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec A) := by
  unfold otrApplyRawSpec
  conv => arg 3; arg 2; ext x s0 sf; rw [sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨o, pqCap, pqPtr, ot, ss, G, st⟩ := x
  dsimp only at *
  have hsc_some : ∃ sc, st.senderChain = some sc := Option.isSome_iff_exists.mp h
  obtain ⟨sc, hsc⟩ := hsc_some
  apply SepWPp.of_sepWP (mid := (blkPl_20).base + 60#64)
  refine ApplyFrameFacts.sepWP_unpack_stackAt_otrApply s0.sp (by sep_focus)
    fun s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3 => ?_
  refine SepWP.fold (otrAt_apply_split A o pqCap pqPtr ot) (by sep_focus) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  let sg_id : SenderChainGhost := { sg with ck := sg.ck }
  have hG_eq : G = { G with sender := some sg_id, pq := G.pq } := by
    cases G; dsimp only at hGs; subst hGs; rfl
  let sc_id : SenderChain := { sc with chainKey := sc.chainKey }
  have hst_eq : st = { st with senderChain := some sc_id, pqRatchetState := st.pqRatchetState } := by
    cases st; dsimp only at hsc; subst hsc; rfl
  conv =>
    arg 4
    rw [hG_eq, hst_eq,
      sessionStateAt_eq_apply A ss G st sg sc G.pq st.pqRatchetState sg.ck sc.chainKey]
  clear hG_eq hst_eq sg_id sc_id
  refine SepWP.fold (vecU8Buf_cap_lt A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_cap => ?_
  refine SepWP.fold (vecU8Buf_dealloc_32 A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)
    (keyToBytes32_length _)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bounds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bounds => ?_
  wp_steps
  wp_call hshim ()
  wp_steps
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call halloc (32, 1)
  apply SepWP.done (by exact hpc_sf_1) (by exact hrun_sf_1)
  by_cases hck_null : sf_1.readReg64 Reg.x0 = 0#64
  · have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hck_null
    have hck_eq0 : sf_1.readReg64 Reg.x0 = 0 := hck_null
    rw [ite_eq_left_iff.mpr (fun h => absurd hck_eq0 h)]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    refine SepWP.focus_pure (by sep_focus) fun htr => ?_
    wp_steps
    apply SepWP.done (by rfl) (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
    refine SepWPp.panic (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
      (by simpa only [State.pc_setPC] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, State.trace_setPC, State.trace_writeReg64, htr, h_3])) hm
  · have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hck_null
    have hck_ne0 : sf_1.readReg64 Reg.x0 ≠ 0 := hck_null
    rw [ite_eq_right_iff.mpr (fun h => absurd h hck_ne0)]
    apply SepWPp.of_sepWP_ret
    refine SepWP.focus_pure (by sep_focus) fun htr1 => ?_
    rcases htr1 with ⟨_, htr1⟩
    wp_simp_pre only [memRegion_32_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w0
    have hsrk_ne : (sg.srk.cap + 1#64 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; bv_omega
    have hck_hi : ConditionHolds CondCode.HI (addsPState64 (sg.ck.cap - 1#64) 3#64) = false :=
      addsPState64_hi_false hck_bounds
    wp_steps
    wp_call hdealloc (sg.ck.ptr, sg.ck.cap.toNat, 1)
    wp_steps
    let sc' : SenderChain := { sc with chainKey := ot.senderChainKey }
    wp_if hpq_beq
    · have hpq0 : G.pq.cap = (0 : BitVec 64) := hpq_beq
      rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
      wp_steps
      rw [hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done
    · have hpq0 : G.pq.cap ≠ (0 : BitVec 64) := hpq_beq
      rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
      wp_steps
      wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
      wp_steps
      rw [hsp_sf_1, hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done

theorem otrApplyRaw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec A) := by
  have hpanic : ((blkPC_20).rebase (blkPl_20).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := (blkPC_20).rebase (blkPl_20).base H) (sym := lsHandleErrorSym)]
    exact h_panic
  exact otrApplyRaw_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_shim) (ls_hook_ok_of_mem h_alloc)
    (ls_hook_ok_of_mem h_dealloc) hpanic

theorem otrApply_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine (otrApplyRaw_placed_ok h_shim h_alloc h_dealloc h_panic).mono_outcome x
    (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)
    s0 hpc hrun
    (by dsimp only [otrApplyPlacedSpec, otrApplyRawSpec, stackAt] at hpre ⊢
        rw [smallRootStack_split_otrApply s0.sp] at hpre
        exact Satisfies.mono (by bi_entail) hpre)
    hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · exact Or.inl ⟨h1, h2, by
      dsimp only [otrApplyRawSpec, otrApplyPlacedSpec, stackAt] at hpost ⊢
      rw [smallRootStack_split_otrApply s0.sp]
      exact Satisfies.mono (by bi_entail) hpost⟩
  · rw [← sepConj_assoc] at hpost
    exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id hpost⟩)
  · exact (allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
