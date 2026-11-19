/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4 Shared Store-Error Unwind Tail

Verifies the shared Stage P4 store-error unwind tail (`+0x54c` / `+0x550` / `+0x3588 → s0.readReg64 .x30`)
for `message_decrypt_prekey::<Coins>::{closure#0}`: copies the 36-byte error-staging slot,
deallocates any non-empty `ptext` buffer, drops `SessionStructure` at `coroPtr + 0xf8`, checks
empty `previous_states`, writes the 48-byte error result to `outPtr`, and restores callee-saved
registers.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem SepWPp.bind_false_frame {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P₁ F : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P₁ Q₁ (fun _ _ => False))
    (hP : P = P₁ ∗ F)
    (h2 : ∀ s1 P_f, s1.pc = mid → s1.status = .Running → Q₁ s1 P_f →
      SepWPp prog ret s1 (P_f ∗ F) Q₂ Qp) :
    SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_f, hmm, hQ1⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm P_f hpcm hrunm hQ1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

@[expose] def p4VecGhostRestAt (A : RustAlloc) (g : VecGhost) (a : BitVec 64) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem p4_vecGhostAt_split_cap (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a = (a ↦₆₄ g.cap) ∗ p4VecGhostRestAt A g a := by
  simp only [vecGhostAt, vecU8At, vecHeader, p4VecGhostRestAt, sepConj_assoc]

@[expose] def p4SessionStateRestAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  p4VecGhostRestAt A G.localIk ss ∗
  vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
  vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
    (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 0x60#64) ∗
  vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
  optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
  ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 0x150#64) ↦ₛ G.regIds)

theorem p4_sessionStateAt_expose_cap (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st = (ss ↦₆₄ G.localIk.cap) ∗ p4SessionStateRestAt A ss G st := by
  unfold sessionStateAt p4SessionStateRestAt
  rw [p4_vecGhostAt_split_cap A G.localIk ss]
  ac_rfl

theorem p4_vecGhostRestAt_cap_ne (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    p4VecGhostRestAt A g a ⊢ ⌜g.cap + 1#64 ≠ 0#64⌝ ∗ p4VecGhostRestAt A g a := by
  let rest : SepProp :=
    ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))
  have heq : p4VecGhostRestAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ rest := by
    dsimp only [p4VecGhostRestAt, rest]; ac_rfl
  rw [heq]
  refine Entails.pure_left fun hm => ?_
  have hne : g.cap + 1#64 ≠ 0#64 := by have := hm.2.1; bv_omega
  exact Entails.pure_right hne (Entails.pure_right hm (Entails.refl rest))

theorem p4_sessionStateAt_expose_cap_ne (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ⌜G.localIk.cap + 1#64 ≠ 0#64⌝ ∗ ((ss ↦₆₄ G.localIk.cap) ∗ p4SessionStateRestAt A ss G st) := by
  rw [p4_sessionStateAt_expose_cap A ss G st]
  unfold p4SessionStateRestAt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (p4_vecGhostRestAt_cap_ne A G.localIk ss)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion48_eq_exists_pollCells (p : BitVec 64) :
    memRegion p 48 =
      ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64, ∃∗ o4 : BitVec 64,
      ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o1 : BitVec 32, ∃∗ w0 : BitVec 64,
        pollCellsAt p w0 o1 o2 o3 o4 o5 o6 := by
  unfold pollCellsAt
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 40)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 4) (k := 36)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0xc#64) (n := 8) (k := 28)
        (b' := p + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x14#64) (n := 8) (k := 20)
        (b' := p + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x1c#64) (n := 8) (k := 12)
        (b' := p + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x24#64) (n := 8) (k := 4)
        (b' := p + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_four (p + 0x8#64),
      ProofLib.memRegion_eight (p + 0xc#64),
      ProofLib.memRegion_eight (p + 0x14#64),
      ProofLib.memRegion_eight (p + 0x1c#64),
      ProofLib.memRegion_eight (p + 0x24#64),
      ProofLib.memRegion_four (p + 0x2c#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem words3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16)
        (b' := a + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x8#64) (n := 8) (k := 8)
        (b' := a + 0x10#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))

theorem coro280_words3_entails_memRegion24 (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0x280#64) ↦₆₄ w0) ∗
      ((coroPtr + 0x288#64) ↦₆₄ w1) ∗
      ((coroPtr + 0x290#64) ↦₆₄ w2) ⊢
      memRegion (coroPtr + 0x280#64) 24 := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    words3_entails_memRegion24 (coroPtr + 0x280#64) w0 w1 w2

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
