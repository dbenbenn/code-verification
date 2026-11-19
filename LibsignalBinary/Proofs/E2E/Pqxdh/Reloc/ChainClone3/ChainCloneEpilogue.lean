/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Common.HookTrace
import ProofLib.SepLogic.WPp

/-!
# Epilogue, Spec Lifts, and Panic Tails for `Chain::clone [local#3]` (`0x766c8`)

Lifts `protoChainCloneSpec` to `chainCloneSpec` and `senderChainCloneSpec`, and proves the return
epilogue and allocation-failure panic-tail lemmas for `Chain::clone [local#3]`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem chainAt_eq_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a) := by
  simp only [chainAt, protoChainAt, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) =
      ((gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) ∧
        PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
      fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩
  rw [hp]

theorem optSenderChainAt_some_eq_chainAt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
        protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
          ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a) := by
  simp only [optSenderChainAt, protoChainAt, optChainKeyAt, List.length_nil, Nat.zero_le,
    true_and, and_true, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey ∧
        g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) =
      ((g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) ∧
        PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1⟩,
      fun ⟨⟨h2, h3, h4⟩, h1⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hp]; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

structure Slots104 where
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64
  v8 : BitVec 64
  v9 : BitVec 64
  v10 : BitVec 64
  v11 : BitVec 64
  w12 : BitVec 32

theorem entails_sepExists_left {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  apply Entails.sepExists_elim
  exact h

theorem entails_sepExists_sepConj_left {α : Type} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem entails_pull_exists {α : Type} {A : SepProp} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, (A ∗ P x) ∗ Q ⊢ R) : A ∗ (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem memRegion_104_eq_slots104 (ptr : BitVec 64) :
    memRegion ptr 104 =
      ∃∗ d : Slots104,
        (ptr ↦₆₄ d.v0) ∗
        ((ptr + 8#64) ↦₆₄ d.v1) ∗
        ((ptr + 16#64) ↦₆₄ d.v2) ∗
        ((ptr + 24#64) ↦₆₄ d.v3) ∗
        ((ptr + 32#64) ↦₆₄ d.v4) ∗
        ((ptr + 40#64) ↦₆₄ d.v5) ∗
        ((ptr + 48#64) ↦₆₄ d.v6) ∗
        ((ptr + 56#64) ↦₆₄ d.v7) ∗
        ((ptr + 64#64) ↦₆₄ d.v8) ∗
        ((ptr + 72#64) ↦₆₄ d.v9) ∗
        ((ptr + 80#64) ↦₆₄ d.v10) ∗
        ((ptr + 88#64) ↦₆₄ d.v11) ∗
        ((ptr + 96#64) ↦₃₂ d.w12) ∗
        memRegion (ptr + 100#64) 4 := by
  rw [memRegion_104_eq_slots ptr]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun v1 => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    refine entails_pull_exists fun v7 => ?_
    refine entails_pull_exists fun v8 => ?_
    refine entails_pull_exists fun v9 => ?_
    refine entails_pull_exists fun v10 => ?_
    refine entails_pull_exists fun v11 => ?_
    refine entails_pull_exists fun w12 => ?_
    apply Entails.sepExists_right ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, w12⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun d => ?_
    exact sepConj_mono (Entails.sepExists_right d.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v6 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v7 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v8 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v9 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v10 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v11 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right d.w12 (Entails.refl _))))))))))))))

theorem epilogue_post_entails (A : RustAlloc) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace) :
    ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
      ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 32#64) ↦₆₄ privPtr') ∗
      ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
      ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 72#64) ↦₆₄ x25) ∗
      ((x.dst + 80#64) ↦₆₄ x28) ∗
      ((x.dst + 88#64) ↦₆₄ x25) ∗
      ((x.dst + 96#64) ↦₃₂ w27) ∗
      memRegion (x.dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
        (keys'.zip x.gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
      protoChainAt A x.gc x.src ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpec A).post x s0 sf := by
  unfold protoChainCloneSpec
  dsimp only
  apply Entails.pure_right htrace
  let g' := clonedChainGhost x.gc srkPtr' privPtr'
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' keys' ckPin'
  have hg' :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ⊢
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) := by
    refine Entails.trans
      (fold_chainAt_dst A x.gc x.dst srkPtr' privPtr' mkPtr' x25 x28 w27 keys' ckPin'
        hsrk hmax hklen) ?_
    apply Entails.sepExists_right g'
    exact Entails.pure_right ⟨rfl, rfl, hklen.trans hsrc_klen.symm⟩ (Entails.refl _)
  have hst := fold_stackAt_chainClone s0
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) v9 v10 v13
  have hgroup :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ∗
       protoChainAt A x.gc x.src ∗
       A.pool ∗
       (stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

/-! ## 5. Extern Hook and Panic Tail Lemmas for `tripleRatchetProgAt` at `chainClone3Name` -/

/-- No-op shim spec that records trace preservation. -/
@[expose] def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

/-- Region `memcpy` spec that records trace preservation. -/
@[expose] def sessionMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs)

theorem sessionMemcpy_hookOk : HookOk hookMemcpy sessionMemcpySpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, sessionMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

theorem sepWP_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (A ∗ B ∗ C) post) :
    SepWP prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWP.pure_elim h

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
