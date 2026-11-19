/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Shared Keys Base

External callee hooks, `sessionStateAt` front/tail decompositions, OOM panic tails
(`+0x375c`, `+0x3768`, `+0x3774`), and OOM-aware `__rust_alloc(sz, 1)` wrappers shared across
Segments 1 and 4.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

@[expose] def sessionStatePure (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

@[expose] def frontSessionRestAt (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecAt A 104 8 (chainAt A) (coroPtr + 0x140#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
    vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x248#64) ↦ₛ G.regIds)

theorem sessionStateAt_front_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜sessionStatePure G st⌝ ∗
        vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
        vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
        vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
        ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
        ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
        frontSessionRestAt A coroPtr G st := by
  unfold sessionStateAt sessionStatePure frontSessionRestAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

@[expose] def tailSessionRestAt (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
    vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
    vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (coroPtr + 0x140#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
    ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter)

theorem sessionStateAt_tail_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜sessionStatePure G st⌝ ∗
        vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
        vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((coroPtr + 0x248#64) ↦ₛ G.regIds) ∗
        tailSessionRestAt A coroPtr G st := by
  unfold sessionStateAt sessionStatePure tailSessionRestAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

theorem cat128_lo (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := by
  bv_kernel

theorem cat128_hi (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := by
  bv_kernel

theorem chunks104W6QAt_sp_0x3e0 (sp w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0x3e0#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0x3e0#64) ↦₆₄ w0) ∗
        ((sp + 0x3e8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0x3f0#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp + 0x3f8#64) ↦₆₄ q1.extractLsb' 0 64) ∗
        ((sp + 0x400#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0x408#64) ↦₆₄ q2.extractLsb' 0 64) ∗
        ((sp + 0x410#64) ↦₆₄ q2.extractLsb' 64 64) ∗
        ((sp + 0x418#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0x420#64) ↦₆₄ q3.extractLsb' 64 64) ∗
        ((sp + 0x428#64) ↦₆₄ q4.extractLsb' 0 64) ∗
        ((sp + 0x430#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0x438#64) ↦₆₄ q5.extractLsb' 0 64) ∗
        ((sp + 0x440#64) ↦₆₄ q5.extractLsb' 64 64) := by
  unfold chunks104W6QAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 2. OOM Panic Tails (`+0x375c`, `+0x3768`, `+0x3774`) and `__rust_alloc(sz, 1)` Wrapper -/

/- OOM panic tail at `+0x375c`: `mov w0, #1; mov x1, x26; bl handle_error`. -/
theorem sepWPp_pure_4th {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 P4 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ P4) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4) Q Qp := by
  rw [show P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ P4 by ac_rfl]
  exact SepWPp.pure_elim h

theorem entails_pure_3rd {P P1 P2 P3 : SepProp} {φ : Prop}
    (hφ : φ) (h : P ⊢ P1 ∗ P2 ∗ P3) :
    P ⊢ P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact Entails.pure_right hφ h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
