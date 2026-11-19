/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Sub-Segment 3A: `pending_pre_key`

Pending/Kyber decomposition helpers, OOM tails (`+0x378c`, `+0x375c`), and CPS sub-segment
theorem `clonePendingPreKey_ok` (`+0x1a5c → +0x1ac8`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3

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

@[expose] def m3a3SessionStateRestAt (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗ vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
    vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    ((coroPtr + 0x140#64) ↦₆₄ G.chainsCap) ∗ ((coroPtr + 0x148#64) ↦₆₄ G.chainsPtr) ∗
    ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
    vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
    vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
    ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗ ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
    ((coroPtr + 0x248#64) ↦ₛ G.regIds)

theorem sessionStateAt_coro_pending_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜sessionStatePure G st⌝ ∗ optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
        optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗ m3a3SessionStateRestAt A coroPtr G st := by
  unfold sessionStateAt sessionStatePure m3a3SessionStateRestAt vecAt vecHeader
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

theorem pure_elim_2 {prog : Program} {ret : BitVec 64} {s : State}
    {P₁ P₂ : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P₁ ∗ P₂) Q Qp) :
    SepWPp prog ret s (P₁ ∗ ⌜φ⌝ ∗ P₂) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim h)

theorem pure_elim_3 {prog : Program} {ret : BitVec 64} {s : State}
    {P₁ P₂ P₃ : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P₁ ∗ P₂ ∗ P₃) Q Qp) :
    SepWPp prog ret s (P₁ ∗ P₂ ∗ ⌜φ⌝ ∗ P₃) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim h)

theorem sepWPp_done {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

theorem list_eq_nil_or_length_pos {α : Type} (xs : List α) :
    xs = [] ∨ 0 < xs.length := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons _ _ => exact Or.inr (Nat.succ_pos _)

/-! ## 2. OOM Exit Tails (`+0x378c..+0x3794` and `+0x375c..+0x3764`) -/

/- OOM tail at `+0x378c`: `mov w0, #1; mov x1, x22; bl alloc::raw_vec::handle_error`. -/
end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3
