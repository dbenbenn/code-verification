/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Stage P2 Matched-Session Entry Bridge (`+0x0868 → +0x094c`)

Composes the matched-session prefix `+0x0868 → +0x094c` on `tripleRatchetProgAtExt img.base ext`
(`<PublicKey>::serialize` on `pm.baseKey`, `SessionRecord::promote_matching_session` returning
`Ok(true)`, `__rust_dealloc` of the 33-byte buffer, and `<SessionState>::remote_identity_key`),
preserving `Steps` and `calleeSavedVRegs`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stack_root_to_pkSerialize_m2 (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - publicKeySerializeStack) ∗
        stackAt sp publicKeySerializeStack :=
  stackAt_split_of_le sp rootStack publicKeySerializeStack (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

private theorem stack_root_to_remoteIk_m2 (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - Getters.remoteIdentityKeyStack) ∗
        stackAt sp Getters.remoteIdentityKeyStack :=
  stackAt_split_of_le sp rootStack Getters.remoteIdentityKeyStack (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

private theorem boxU8Buf_pk_serialize_entails (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  unfold boxU8Buf
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => Entails.refl _

private theorem sessionStateAt_split_remoteIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss G st ⊢
        ⌜G.localIk.cap.toNat < 2 ^ 63 ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        R_ss) ∧
      ((ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_ss ⊢
        sessionStateAt A ss G st) := by
  have hloc :
      ∃ R_loc : SepProp,
        (vecGhostAt A G.localIk ss ⊢
          ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∧
        ((ss ↦₆₄ G.localIk.cap) ∗ R_loc ⊢ vecGhostAt A G.localIk ss) := by
    unfold vecGhostAt vecU8At vecHeader
    refine ⟨((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
            ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
            ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
              G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗
            (if G.localIk.cap = 0#64 then emp
             else A.live G.localIk.ptr G.localIk.cap.toNat 1 ∗
               (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
               memRegion (G.localIk.ptr + BitVec.ofNat 64 G.localIk.bytes.length)
                 (G.localIk.cap.toNat - G.localIk.bytes.length)), ?_, ?_⟩
    · simp only [sepConj_assoc]
      refine Entails.trans (Entails.of_eq (by sep_focus : _ =
        ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
          G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗ _)) ?_
      refine Entails.pure_left fun hp => Entails.pure_right hp.2.1
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (Entails.of_eq (by simp only [pure_sepConj_of_true hp, sepConj_assoc]; ac_rfl)))
    · simp only [sepConj_assoc]
      exact Entails.of_eq (by ac_rfl)
  obtain ⟨R_loc, hloc_f, hloc_b⟩ := hloc
  let P_pure : Prop :=
    PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)
  let R_rest : SepProp :=
    vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
      G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + asm64% ssAliceBaseKeyOff) ∗
    vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
    optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
    optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber ∗
    ((ss + asm64% ssSessionVersionOff) ↦₃₂ st.sessionVersion) ∗
    ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
    ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)
  have hss_eq : sessionStateAt A ss G st =
      ⌜P_pure⌝ ∗ vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest := by
    unfold sessionStateAt P_pure R_rest
    rfl
  refine ⟨⌜P_pure⌝ ∗ R_loc ∗ R_rest, ?_, ?_⟩
  · rw [hss_eq]
    refine Entails.pure_left fun hp => ?_
    refine Entails.trans (sepConj_mono_left hloc_f) ?_
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hcap => Entails.pure_right ⟨hcap, hp.2.1⟩ ?_
    simp only [pure_sepConj_of_true hp, sepConj_assoc]
    exact Entails.of_eq (by ac_rfl)
  · rw [hss_eq]
    refine Entails.trans (Entails.of_eq (by ac_rfl :
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ (⌜P_pure⌝ ∗ R_loc ∗ R_rest) =
      ⌜P_pure⌝ ∗ ((ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest)) ?_
    exact sepConj_mono_right (sepConj_mono_left hloc_b)

private theorem memRegion_3e0_34_split_16_18 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 16 ∗ memRegion (sp + 0x3f0#64) 18 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 16 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_3e0_34_restore (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
    memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 18 ⊢
      memRegion (sp + 0x3e0#64) 34 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 26 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 1 25 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 1#64) 7 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

theorem blackBoxHook_withPanics {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    Rust.withPanics ext "subtle::black_box::<u8>" = some blackBoxHook := by
  have hnp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by simp [Rust.isPanicSymbol]
  simp [Rust.withPanics, hnp, h_bb]

theorem processPrekeyActive10At_eq (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt : BitVec 64) :
    processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt =
    ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
    ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
    ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
    ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
    ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
    ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
    ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
    ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
    ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) :=
  rfl

private theorem bind_sepWPp_steps_frame_dep
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)) :
    SepWPp prog ret s P Q (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem stack_root_to_promoteMatch_ext32 (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - promoteMatchingSessionMatchStackExt) ∗
      stackAt sp promoteMatchingSessionMatchStackExt :=
  stackAt_split_of_le sp rootStack promoteMatchingSessionMatchStackExt (by decide) hn

theorem stack_root_to_pkSerialize_m2_x (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - publicKeySerializeStackX) ∗
        stackAt sp publicKeySerializeStackX :=
  stackAt_split_of_le sp rootStack publicKeySerializeStackX (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

theorem stack_root_to_extHook_m2b (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - extHookStack) ∗
        stackAt sp extHookStack :=
  stackAt_split_of_le sp rootStack extHookStack (by decide) hn

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
