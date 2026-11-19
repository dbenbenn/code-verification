/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Entry Prefix and Pending-Key Clearing Helpers of `archive_current_state_inner`

Shared cut offsets (`archiveShimCutOff`, `archiveEncodeRawCutOff`), mid-segment spatial predicates
(`archiveMidShimPre`, `archiveMidRawPre`), and signed-comparison / `tailPinDealloc` splitting
helpers for `<SessionRecord>::archive_current_state_inner`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Function-relative byte offset of `bl __rust_no_alloc_shim_is_unstable_v2` in `archive_current_state_inner`. -/
abbrev archiveShimCutOff : BitVec 64 := 0xe4#64

/-- Function-relative byte offset of `bl encode_raw` in `archive_current_state_inner`. -/
abbrev archiveEncodeRawCutOff : BitVec 64 := 0x118#64

/-- Panic postcondition on `allocPanic` with frame `R`. -/
abbrev archiveQp (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

/-- Spatial state right after `bl __rust_no_alloc_shim_is_unstable_v2` in `archive_current_state_inner`. -/
@[expose] def archiveMidShimPre (A : RustAlloc) (s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    sessionStateReprAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 88#64) ↦₆₄ c1) ∗
    ((s0.sp - 80#64) ↦₆₄ c2) ∗
    ((s0.sp - 72#64) ↦₆₄ c3) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-- Spatial state right after `bl encode_raw` in `archive_current_state_inner`. -/
@[expose] def archiveMidRawPre (A : RustAlloc) (s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    vecU8At A (s0.sp - 88#64) capEnc ptrEnc
      (encSessionMem (clearPendingGhost G) (clearPending sess)) ∗
    sessionStateReprAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-! ## Signed-Comparison and `tailPinDealloc` Helpers -/

theorem tailPinDealloc_of_slt_true (A : RustAlloc) {cap ptr : BitVec 64}
    (h : cap.slt 1#64 = true) :
    tailPinDealloc A cap ptr = emp := by
  simp [tailPinDealloc, h]

theorem tailPinDealloc_of_slt_false (A : RustAlloc) {cap ptr : BitVec 64}
    (h : cap.slt 1#64 = false) :
    tailPinDealloc A cap ptr =
      (⌜1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  simp [tailPinDealloc, h]

theorem cap_slt_conds_of_true {cap : BitVec 64} (h : cap.slt 1#64 = true) :
    (0#64).slt cap = false ∧ cap.sle 0#64 = true ∧ (1#64).sle cap = false := by
  have hz : (0#64).toInt = 0 := rfl
  have ho : (1#64).toInt = 1 := rfl
  rw [BitVec.slt_iff_toInt_lt, ho] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.slt_iff_toInt_lt, hz] at hc; omega
  · rw [BitVec.sle_iff_toInt_le, hz]; omega
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.sle_iff_toInt_le, ho] at hc; omega

theorem cap_slt_conds_of_false {cap : BitVec 64} (h : cap.slt 1#64 = false) :
    (0#64).slt cap = true ∧ cap.sle 0#64 = false ∧ (1#64).sle cap = true := by
  have hz : (0#64).toInt = 0 := rfl
  have ho : (1#64).toInt = 1 := rfl
  have hn : ¬ (cap.toInt < 1) := by
    intro hc
    have h' : cap.slt 1#64 = true := BitVec.slt_iff_toInt_lt.mpr (by rw [ho]; exact hc)
    rw [h] at h'; contradiction
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.slt_iff_toInt_lt, hz]; omega
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.sle_iff_toInt_le, hz] at hc; omega
  · rw [BitVec.sle_iff_toInt_le, ho]; omega

theorem heap_split_tt (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = true)
    (hks : (optTailCap G.kyber).slt 1#64 = true) :
    sessionAtHeap A G sess ⊢ sessionAtHeap A (clearPendingGhost G) (clearPending sess) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_true A hps, tailPinDealloc_of_slt_true A hks, emp_sepConj, sepConj_emp]
  exact Entails.refl _

theorem heap_split_tf (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = true)
    (hks : (optTailCap G.kyber).slt 1#64 = false) :
    sessionAtHeap A G sess ⊢
      ⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
        (A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_true A hps, tailPinDealloc_of_slt_false A hks, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem heap_split_ft (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = false)
    (hks : (optTailCap G.kyber).slt 1#64 = true) :
    sessionAtHeap A G sess ⊢
      ⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_false A hps, tailPinDealloc_of_slt_true A hks, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem heap_split_ff (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = false)
    (hks : (optTailCap G.kyber).slt 1#64 = false) :
    sessionAtHeap A G sess ⊢
      ⌜(1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63) ∧
        (1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63)⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_false A hps, tailPinDealloc_of_slt_false A hks]
  have hpull :
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        (⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
          A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat) ∗
        (⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat) =
      ⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
        ⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hp
  apply Entails.pure_left; intro hk
  exact Entails.pure_right ⟨hp, hk⟩ (Entails.refl _)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
