/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc
import ProofLib.Sep
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

section CmkSavedRegsLayout

open Arm64 ProofLib CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.RustHeap

structure CmkSavedRegsSnap where
  x29 : BitVec 64
  x30 : BitVec 64
  x28 : BitVec 64
  x27 : BitVec 64
  x26 : BitVec 64
  x25 : BitVec 64
  x24 : BitVec 64
  x23 : BitVec 64
  x22 : BitVec 64
  x21 : BitVec 64
  x20 : BitVec 64
  x19 : BitVec 64

def cmkSavedRegsLayout : ProofLib.Sep.StructLayout CmkSavedRegsSnap where
  totalSz := 96
  fields := [
    .u64 0  (·.x29), .u64 8  (·.x30), .u64 16 (·.x28), .u64 24 (·.x27),
    .u64 32 (·.x26), .u64 40 (·.x25), .u64 48 (·.x24), .u64 56 (·.x23),
    .u64 64 (·.x22), .u64 72 (·.x21), .u64 80 (·.x20), .u64 88 (·.x19)
  ]

theorem cmkSavedRegs_eq_layout (sp0 : BitVec 64) (s0 : State) :
    cmkSavedRegs sp0 s0 =
      cmkSavedRegsLayout.own (sp0 - 96#64)
        ⟨s0.readReg64 .x29, s0.readReg64 .x30, s0.readReg64 .x28, s0.readReg64 .x27,
         s0.readReg64 .x26, s0.readReg64 .x25, s0.readReg64 .x24, s0.readReg64 .x23,
         s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19⟩ := by
  dsimp only [cmkSavedRegs, cmkSavedRegsLayout, ProofLib.Sep.StructLayout.own,
    ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
    ProofLib.Sep.StructField.u64, ProofLib.Sep.StructField.field64, ProofLib.Sep.fieldAddr]
  have hsub (b : BitVec 64) : (sp0 - 96#64) + b = sp0 - (96#64 - b) := by bv_omega
  simp only [hsub, Nat.reduceAdd, Nat.reduceLT, Nat.reduceBEq, ↓reduceIte, sepConj_emp]
  rfl

end CmkSavedRegsLayout

public section

namespace CryptoVerification.LibsignalSession.TooFarPath

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

theorem pointsToBytes_tooFarInFutureStr (p : BitVec 64) :
    (p ↦ₛ tooFarInFutureStr) =
      (p ↦₆₄ 0x206567617373656d#64) ∗
      ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
      ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗
      ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
      ((p + 32#64) ↦₃₂ 0x65727574#32) := by
  have heq : tooFarInFutureStr =
      unpack64 0x206567617373656d#64 ++
      (unpack64 0x6f6f74206d6f7266#64 ++
      (unpack64 0x746e692072616620#64 ++
      (unpack64 0x756620656874206f#64 ++
       unpack32 0x65727574#32))) := by rfl_kernel
  rw [heq, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo32_eq_pointsToBytes]
  simp only [unpack64_length]
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_arith
  rw [h16, h24, h32]

theorem pointsToBytesRO_tooFarInFutureStr (p : BitVec 64) :
    (p ↦ᵣ tooFarInFutureStr) =
      (p ↦₆₄ᵣ 0x206567617373656d#64) ∗
      ((p + 8#64) ↦₆₄ᵣ 0x6f6f74206d6f7266#64) ∗
      ((p + 16#64) ↦₆₄ᵣ 0x746e692072616620#64) ∗
      ((p + 24#64) ↦₆₄ᵣ 0x756620656874206f#64) ∗
      ((p + 32#64) ↦₃₂ᵣ 0x65727574#32) := by
  have heq : tooFarInFutureStr =
      unpack64 0x206567617373656d#64 ++
      (unpack64 0x6f6f74206d6f7266#64 ++
      (unpack64 0x746e692072616620#64 ++
      (unpack64 0x756620656874206f#64 ++
       unpack32 0x65727574#32))) := by rfl_kernel
  rw [heq, pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
    ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
    ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
    ← pointsTo32RO_eq_pointsToBytesRO]
  simp only [unpack64_length]
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_arith
  rw [h16, h24, h32]

theorem ratchetAt_expose_maxForwardJumps (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A self G st =
      ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
        st.maxForwardJumps < 2 ^ 64⌝ ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
      (vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
       ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) := by
  unfold ratchetAt
  sep_interval_eq

theorem memRegion_36_split (p : BitVec 64) :
    memRegion p 36 =
      ∃∗ v4 : BitVec 32, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64,
      ∃∗ v0 : BitVec 64,
        (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₆₄ v2) ∗ ((p + 24#64) ↦₆₄ v3) ∗
        ((p + 32#64) ↦₃₂ v4) := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem memRegion_88_ret_split (r : BitVec 64) :
    memRegion r 88 =
      ∃∗ r40 : BitVec 8, ∃∗ r32 : BitVec 64, ∃∗ r24 : BitVec 64, ∃∗ r16 : BitVec 64,
      ∃∗ r8 : BitVec 64, ∃∗ r0 : BitVec 32,
        (r ↦₃₂ r0) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ r8) ∗ ((r + 16#64) ↦₆₄ r16) ∗
        ((r + 24#64) ↦₆₄ r24) ∗ ((r + 32#64) ↦₆₄ r32) ∗
        ((r + 40#64) ↦₈ r40) ∗ memRegion (r + 41#64) 47 := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem resultAt_tooFar_intro (A : RustAlloc) (r p : BitVec 64) (t : MessageType) (hp : p ≠ 0) :
    ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
     ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
     A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr) ∗
     ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) ⊢
    consumeMessageKeyResultAt A r (.error (.invalidMessage t .tooFarInFuture)) := by
  simp only [consumeMessageKeyResultAt, errInvalidMessage, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp]
  have hvec :
      (((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
       A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr)) ⊢
      vecU8 A (r + 16#64) tooFarInFutureStr := by
    unfold RustHeap.vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 36#64)
    refine Entails.trans ?_ (Entails.sepExists_intro p)
    unfold RustHeap.vecU8At RustHeap.vecHeader
    have hlen : tooFarInFutureStr.length = 36 := by rfl_kernel
    have hcap_ne : (36#64 : BitVec 64) ≠ 0#64 := by decide
    have hcap_nat : (36#64 : BitVec 64).toNat = 36 := rfl
    have hpure : 36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0#64 := ⟨by decide, by decide, hp⟩
    simp only [hlen, hcap_ne, hcap_nat, ↓reduceIte, Nat.sub_self, memRegion_zero,
      BitVec.ofNat_eq_ofNat, sepConj_emp]
    bi_entail
  generalize hv : vecU8 A (r + 16#64) tooFarInFutureStr = vVec at hvec ⊢
  refine' Entails.trans (Entails.trans ?_ (sepConj_mono_left hvec)) ?_
  · bi_frame
  · bi_entail

theorem memRegion_384_tooFarPath_split (sp0 : BitVec 64) :
    memRegion (sp0 - 480#64) 384 =
      ∃∗ v9 : BitVec 64,
        memRegion (sp0 - 480#64) 152 ∗
        ((sp0 - 328#64) ↦₆₄ v9) ∗
        memRegion (sp0 - 320#64) 224 := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem stackAt_7712_split (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 =
      memRegion (sp0 - 8192#64) 3616 ∗ stackAt (sp0 - 480#64) allocHookStack := by
  dsimp only [stackAt, allocHookStack]; sep_interval_eq

theorem cmkSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    cmkSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  rw [cmkSavedRegs_eq_layout]
  exact cmkSavedRegsLayout.struct_to_memRegion (sp0 - 96#64) _

theorem stackAt_cmkStack_reassemble (sp0 : BitVec 64) (s0 : State) (v9 : BitVec 64) :
    (memRegion (sp0 - 8192#64) 3616 ∗
     stackAt (sp0 - 480#64) allocHookStack ∗
     memRegion (sp0 - 480#64) 152 ∗
     ((sp0 - 328#64) ↦₆₄ v9) ∗
     memRegion (sp0 - 320#64) 224 ∗
     cmkSavedRegs sp0 s0) ⊢
    stackAt sp0 cmkStack := by
  unfold cmkSavedRegs stackAt allocHookStack cmkStack
  sep_interval

abbrev cmkTooFarStrSym : String := "libsignal_protocol:.rodata..Lanon.292"

theorem rodata_placed_tooFarInFuture_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

end CryptoVerification.LibsignalSession.TooFarPath

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

@[expose] def TooFarPathPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index ≤ x.counter →
      x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
      CmkTooFarState_placed A x ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

end CryptoVerification.LibsignalSession
