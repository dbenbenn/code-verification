/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Top -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP3ExitFold -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Poll Path B Stage P2 Spatial Entry Unpack and Inner Frame

Defines `matchedInnerFrame` (and `matchedInnerFrameExt`) and proves `matched_entry_unpack` (and
`matched_entry_unpack_ext`) bridging `StageP2MatchedFramedCliStmt` to
`Matched.stageP2_matched_ok_framed`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

/-- Lift `ResponderClosure.PanicOomProp s0 sf Pf` across an inner frame `F_inner` into `Poll.PanicOomProp`. -/
theorem poll_panicOomProp_of_matched {s0 sf : State} {Pf : SepProp} (F_inner : SepProp)
    (h : CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf) :
    PanicOomProp s0 sf (Pf ∗ F_inner) :=
  Matched.panicOomProp_frame F_inner h

/-- Frame `s1.readReg64.x29 = s0.sp - 0x60#64` with `sp + 0xcd0#64 = s0.sp` gives `sp + 0xc70#64`. -/
theorem x29_eq_sp_add_c70 {s0 s1 : State} {sp : BitVec 64}
    (hsp0 : sp + 0xcd0#64 = s0.sp) (hx29 : s1.readReg64 .x29 = s0.sp - 0x60#64) :
    s1.readReg64 .x29 = sp + 0xc70#64 := by
  rw [hx29, ← hsp0]
  bv_omega

/-- Converse register rewrite `s2.readReg64.x29 = sp + 0xc70#64 → s0.sp - 0x60#64`. -/
theorem x29_eq_sp0_sub_60 {s0 s2 : State} {sp : BitVec 64}
    (hsp0 : sp + 0xcd0#64 = s0.sp) (hx29 : s2.readReg64 .x29 = sp + 0xc70#64) :
    s2.readReg64 .x29 = s0.sp - 0x60#64 := by
  rw [hx29, ← hsp0]
  bv_omega

/-! ## 1. Fine-Grained Coroutine, Stack, & Message Remainder Predicates -/

/-- Tail 11 words (`+0x88.. +0xe0`) of `decryptPrekeyCoroCopyAt` untouched by `stageP2MatchedPre`. -/
@[expose] def coroCopyTail11At (coroPtr sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64) : SepProp :=
  ((coroPtr + 0x88#64) ↦₆₄ sessStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ sessStoreVt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0xb8#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0xc0#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0xd8#64) ↦₆₄ rngPtr)

theorem coroCopyAt_eq_head3_tail11 (coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64) :
    decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt rngPtr =
    ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
    ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
    coroCopyTail11At coroPtr sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt rngPtr := by
  unfold decryptPrekeyCoroCopyAt coroCopyTail11At
  ac_rfl

/-- Remaining 23 words of `processPrekeyInnerInitAt` outside `+0x330` and `+0x388`. -/
@[expose] def processPrekeyInnerRem23At (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) : SepProp :=
  ((coroPtr + 0x2c8#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x2d0#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x2d8#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x2e0#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x2e8#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x2f0#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x2f8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x300#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x308#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x310#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x318#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x320#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x328#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x338#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x340#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x348#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x350#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x358#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x360#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x368#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x370#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x378#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x380#64) ↦₆₄ kyberStoreVt)

theorem processPrekeyInnerInitAt_eq_330_388_rem23 (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) :
    processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt =
    ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt := by
  unfold processPrekeyInnerInitAt processPrekeyInnerRem23At
  ac_rfl

/-- Remainder of `signalMessageAt` outside `(a + 0x70#64) ↦₈ m.messageVersion`. -/
@[expose] def signalMessageRestVerAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + asm64% smCiphertextOff) g.ctPtr m.ciphertext ∗
    boxU8At A (a + asm64% smSerializedOff) g.serPtr m.serialized ∗
    ((a + asm64% smSenderRatchetKeyOff) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + asm64% smAddressesOff) g.addrPtr m.addresses ∗
    ((a + asm64% smCounterOff) ↦₃₂ m.counter) ∗
    ((a + asm64% smPreviousCounterOff) ↦₃₂ m.previousCounter) ∗
    memRegion (a + asm64% (smMessageVersionOff + 1))
      (asm% (signalMessageSize - (smMessageVersionOff + 1)))

theorem signalMessageAt_eq_ver_sep (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x70#64) ↦₈ m.messageVersion) ∗ signalMessageRestVerAt A g a m := by
  unfold signalMessageAt signalMessageRestVerAt
  ac_rfl

/-- Remainder of `preKeyMsgRemBaseIdKeyAt` outside `(a + 0xf0#64) ↦₈ m.messageVersion`. -/
@[expose] def preKeyMsgRemMatchedAt (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) : SepProp :=
  optU32At (a + 0x78#64) m.preKeyId ∗
  boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗
  optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
  ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗
  ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
  memRegion (a + 0xf1#64) 7

theorem preKeyMsgRemBaseIdKeyAt_eq_ver_sep (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) :
    preKeyMsgRemBaseIdKeyAt A g a m =
      ((a + 0xf0#64) ↦₈ m.messageVersion) ∗ preKeyMsgRemMatchedAt A g a m := by
  unfold preKeyMsgRemBaseIdKeyAt preKeyMsgRemMatchedAt
  ac_rfl

/-! ## 2. `SepWPp` Post-Entailment Closure Combinators -/

/-- Close `SepWPp` normal postconditions under spatial entailment `Pf ⊢ P_out`. -/
theorem sepWPp_entails_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P (fun sf Pf => ∃ P_out, (Pf ⊢ P_out) ∧ Q sf P_out) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, P_out, hent, hQ⟩ | hpan | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_out,
      Arm64.Satisfies.mono (sepConj_mono_left hent) hmf, hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Lift `SepWPp... Q Qp` into `SepWPp... (fun sf Pf => ∃ P_out, (Pf ⊢ P_out) ∧ Q sf P_out) Qp`. -/
theorem sepWPp_lift_entails_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P (fun sf Pf => ∃ P_out, (Pf ⊢ P_out) ∧ Q sf P_out) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, Pf, Entails.refl Pf, hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 3. Entry Unpack Witness & Inner Frame (`matchedInnerFrame`) -/

/-- Scratch words unpacked from `stageP2PostP1At` at `+0x0868` for `stageP2MatchedPre`. -/
structure MatchedEntryWords where
  u_80 : BitVec 64
  u_88 : BitVec 64
  u_90 : BitVec 64
  u_298 : BitVec 64
  u_2a0 : BitVec 64
  u_3a0 : BitVec 64
  u_3b0 : BitVec 64
  u_3b8 : BitVec 64
  u_3c0 : BitVec 64
  u_3c8 : BitVec 64
  u_3d0 : BitVec 64
  u_3d8 : BitVec 64
  u_2a8 : BitVec 32
  b_4f1 : BitVec 8
  b_3ac : BitVec 8

private theorem step_mr8 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ u : BitVec 64, Rest ∗ ((a ↦₆₄ u) ∗ Acc) ⊢ Q) :
    (memRegion a 8 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left]
  exact Entails.sepExists_elim fun u => Entails.trans (by sep_frame) (h u)

private theorem step_mr4 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ u : BitVec 32, Rest ∗ ((a ↦₃₂ u) ∗ Acc) ⊢ Q) :
    (memRegion a 4 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [memRegion_4_eq_exists_pointsTo32 a, sepExists_sepConj_left, sepExists_sepConj_left]
  exact Entails.sepExists_elim fun u => Entails.trans (by sep_frame) (h u)

private theorem step_mr1 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ b : BitVec 8, Rest ∗ ((a ↦₈ b) ∗ Acc) ⊢ Q) :
    (memRegion a 1 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [memRegion_eq_exists_bytes a 1 (by decide), sepExists_sepConj_left, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b, _ | _⟩ <;> try (simp at hlen; done)
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact Entails.trans (by sep_frame) (h b)

private theorem elim_mr8 {a : BitVec 64} {Acc Q : SepProp}
    (h : ∀ u : BitVec 64, (a ↦₆₄ u) ∗ Acc ⊢ Q) :
    memRegion a 8 ∗ Acc ⊢ Q := by
  rw [ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left]
  exact Entails.sepExists_elim h

private theorem elim_mr1 {a : BitVec 64} {Acc Q : SepProp}
    (h : ∀ b : BitVec 8, (a ↦₈ b) ∗ Acc ⊢ Q) :
    memRegion a 1 ∗ Acc ⊢ Q := by
  rw [memRegion_eq_exists_bytes a 1 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b, _ | _⟩ <;> try (simp at hlen; done)
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact h b

theorem coro_unused_split_matched (fut : BitVec 64) :
    coroUnusedP1At fut ⊢
      ∃∗ u_298 : BitVec 64, ∃∗ u_2a0 : BitVec 64, ∃∗ u_2a8 : BitVec 32, ∃∗ b_4f1 : BitVec 8,
        cells (fut + 0x3f8#64) 6 ∗
        cells (fut + 0x468#64) 4 ∗
        ((fut + 0x298#64) ↦₆₄ u_298) ∗
        ((fut + 0x2a0#64) ↦₆₄ u_2a0) ∗
        ((fut + 0x2a8#64) ↦₃₂ u_2a8) ∗
        ((fut + 0x4f1#64) ↦₈ b_4f1) ∗
        memRegion (fut + 0x280#64) 24 ∗
        memRegion (fut + 0x2ac#64) 8 ∗
        memRegion (fut + 0x2b4#64) 12 ∗
        memRegion (fut + 0x2c1#64) 7 ∗
        memRegion (fut + 0x391#64) 7 ∗
        memRegion (fut + 0x3a8#64) 80 ∗
        memRegion (fut + 0x488#64) 8 ∗
        memRegion (fut + 0x4b0#64) 65 ∗
        memRegion (fut + 0x4f3#64) 5 ∗
        memRegion (fut + 0x4f8#64) 736 := by
  unfold coroUnusedP1At
  have h280 : memRegion (fut + 0x280#64) 64 =
      memRegion (fut + 0x280#64) 24 ∗ memRegion (fut + 0x298#64) 8 ∗
      memRegion (fut + 0x2a0#64) 8 ∗ memRegion (fut + 0x2a8#64) 4 ∗
      memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 := by
    rw [memRegion_split (fut + 0x280#64) 24 40 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64) 8 32 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64 + 8#64) 8 24 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64 + 8#64 + 8#64) 4 20 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64 + 8#64 + 8#64 + 4#64) 8 12 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h3a8 : memRegion (fut + 0x3a8#64) 128 =
      memRegion (fut + 0x3a8#64) 80 ∗ cells (fut + 0x3f8#64) 6 := by
    rw [memRegion_split (fut + 0x3a8#64) 80 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [ProofLib.memRegion_cells (fut + 0x3f8#64) 6 (by decide)]
  have h468 : memRegion (fut + 0x468#64) 40 =
      cells (fut + 0x468#64) 4 ∗ memRegion (fut + 0x488#64) 8 := by
    rw [memRegion_split (fut + 0x468#64) 32 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [ProofLib.memRegion_cells (fut + 0x468#64) 4 (by decide)]
  have h4b0 : memRegion (fut + 0x4b0#64) 66 =
      memRegion (fut + 0x4b0#64) 65 ∗ memRegion (fut + 0x4f1#64) 1 := by
    rw [memRegion_split (fut + 0x4b0#64) 65 1 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h280, h3a8, h468, h4b0]
  refine Entails.trans (show _ ⊢
      (memRegion (fut + 0x298#64) 8 ∗ memRegion (fut + 0x2a0#64) 8 ∗
        memRegion (fut + 0x2a8#64) 4 ∗ memRegion (fut + 0x4f1#64) 1) ∗
      (cells (fut + 0x3f8#64) 6 ∗ cells (fut + 0x468#64) 4 ∗
        memRegion (fut + 0x280#64) 24 ∗ memRegion (fut + 0x2ac#64) 8 ∗
        memRegion (fut + 0x2b4#64) 12 ∗ memRegion (fut + 0x2c1#64) 7 ∗
        memRegion (fut + 0x391#64) 7 ∗ memRegion (fut + 0x3a8#64) 80 ∗
        memRegion (fut + 0x488#64) 8 ∗ memRegion (fut + 0x4b0#64) 65 ∗
        memRegion (fut + 0x4f3#64) 5 ∗ memRegion (fut + 0x4f8#64) 736) by sep_frame) ?_
  refine step_mr8 fun u298 => step_mr8 fun u2a0 => step_mr4 fun u2a8 => elim_mr1 fun b4f1 => ?_
  exact Entails.sepExists_right u298 (Entails.sepExists_right u2a0
    (Entails.sepExists_right u2a8 (Entails.sepExists_right b4f1 (by sep_frame))))

theorem stack_unused_split_matched (sp v_b8 : BitVec 64) :
    ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    closStackUnusedP1OkAt sp ⊢
      ∃∗ u_80 : BitVec 64, ∃∗ u_88 : BitVec 64, ∃∗ u_90 : BitVec 64,
      ∃∗ u_3a0 : BitVec 64, ∃∗ b_3ac : BitVec 8,
      ∃∗ u_3b0 : BitVec 64, ∃∗ u_3b8 : BitVec 64, ∃∗ u_3c0 : BitVec 64,
      ∃∗ u_3c8 : BitVec 64, ∃∗ u_3d0 : BitVec 64, ∃∗ u_3d8 : BitVec 64,
        ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x90#64) ↦₆₄ u_90) ∗
        ((sp + 0xb8#64) ↦₃₂ v_b8.extractLsb' 0 32) ∗
        memRegion (sp + 0x370#64) 36 ∗
        ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
        ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
        ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
        memRegion (sp + 0x3e0#64) 34 ∗
        memRegion (sp + 0x920#64) 6 ∗
        memRegion (sp + 0xa90#64) 48 ∗
        memRegion (sp + 0x8#64) 120 ∗
        memRegion (sp + 0xbc#64) 4 ∗
        memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
        spMidGapsAt sp ∗
        memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x926#64) 10 ∗
        memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
        memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
  unfold closStackUnusedP1OkAt
  have hb8 : ((sp + 0xb8#64) ↦₆₄ v_b8) ⊢
      ((sp + 0xb8#64) ↦₃₂ v_b8.extractLsb' 0 32) ∗ memRegion (sp + 0xbc#64) 4 := by
    rw [pointsTo64_split32 (sp + 0xb8#64) v_b8]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h3b0 : memRegion (sp + 0x3b0#64) 24 =
      memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 8 ∗ memRegion (sp + 0x3c0#64) 8 := by
    rw [memRegion_split (sp + 0x3b0#64) 8 16 (by decide),
        memRegion_split (sp + 0x3b0#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h3c8 : memRegion (sp + 0x3c8#64) 24 =
      memRegion (sp + 0x3c8#64) 8 ∗ memRegion (sp + 0x3d0#64) 8 ∗ memRegion (sp + 0x3d8#64) 8 := by
    rw [memRegion_split (sp + 0x3c8#64) 8 16 (by decide),
        memRegion_split (sp + 0x3c8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h550 : memRegion (sp + 0x550#64) 1824 =
      memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0xa90#64) 48 ∗
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
    rw [sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  refine Entails.trans (sepConj_mono_left hb8) ?_
  rw [sp_8_144_split_120_words3 sp, sp_234_428_split sp, h3b0, h3c8, h3e0, h550]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => ?_
  refine Entails.trans (show _ ⊢
      (memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3b8#64) 8 ∗ memRegion (sp + 0x3c0#64) 8 ∗
        memRegion (sp + 0x3c8#64) 8 ∗ memRegion (sp + 0x3d0#64) 8 ∗ memRegion (sp + 0x3d8#64) 8) ∗
      (((sp + 0x80#64) ↦₆₄ u80) ∗ ((sp + 0x88#64) ↦₆₄ u88) ∗ ((sp + 0x90#64) ↦₆₄ u90) ∗
        ((sp + 0xb8#64) ↦₃₂ v_b8.extractLsb' 0 32) ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0xa90#64) 48 ∗
        memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xbc#64) 4 ∗
        memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
        spMidGapsAt sp ∗ memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x448#64) 240 ∗
        memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0x550#64) 976 ∗
        memRegion (sp + 0x926#64) 10 ∗ memRegion (sp + 0x930#64) 96 ∗
        memRegion (sp + 0x990#64) 256 ∗ memRegion (sp + 0xac0#64) 296 ∗
        memRegion (sp + 0xbe8#64) 136) by sep_frame) ?_
  refine step_mr8 fun u3a0 => step_mr1 fun b3ac =>
    step_mr8 fun u3b0 => step_mr8 fun u3b8 => step_mr8 fun u3c0 =>
    step_mr8 fun u3c8 => step_mr8 fun u3d0 => elim_mr8 fun u3d8 => ?_
  exact Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u90
    (Entails.sepExists_right u3a0 (Entails.sepExists_right b3ac
      (Entails.sepExists_right u3b0 (Entails.sepExists_right u3b8 (Entails.sepExists_right u3c0
        (Entails.sepExists_right u3c8 (Entails.sepExists_right u3d0
          (Entails.sepExists_right u3d8 (by sep_frame)))))))))))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
