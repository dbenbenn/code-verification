/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Phase 1 Prologue and Shared Epilogues (`0x3085c`, `0x31a5c..0x31a94`)

Proves `.rodata` jump-table extraction from `img.FrozenLoaded`, the prologue (`+0..+76`),
the register-restore epilogue (`+4632`), and the shared cleanup epilogues at `+4608` and `+904`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_16 (sp0 : BitVec 64) : (sp0 - 96#64) + 16#64 = sp0 - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_32 (sp0 : BitVec 64) : (sp0 - 96#64) + 32#64 = sp0 - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_48 (sp0 : BitVec 64) : (sp0 - 96#64) + 48#64 = sp0 - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_64 (sp0 : BitVec 64) : (sp0 - 96#64) + 64#64 = sp0 - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_80 (sp0 : BitVec 64) : (sp0 - 96#64) + 80#64 = sp0 - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_4096 (sp0 : BitVec 64) : (sp0 - 96#64) - 4096#64 = sp0 - 4192#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4192_sub_3872 (sp0 : BitVec 64) : (sp0 - 4192#64) - 3872#64 = sp0 - 8064#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_4096 (sp0 : BitVec 64) : (sp0 - 8064#64) + 4096#64 = sp0 - 3968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_3968_add_3872 (sp0 : BitVec 64) : (sp0 - 3968#64) + 3872#64 = sp0 - 96#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7968 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7968#64 = sp0 - 96#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7976 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7976#64 = sp0 - 88#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7984 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7984#64 = sp0 - 80#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7992 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7992#64 = sp0 - 72#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8000 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8000#64 = sp0 - 64#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8008 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8008#64 = sp0 - 56#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8016 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8016#64 = sp0 - 48#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8024 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8024#64 = sp0 - 40#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8032 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8032#64 = sp0 - 32#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8040 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8040#64 = sp0 - 24#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8048 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8048#64 = sp0 - 16#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8056 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8056#64 = sp0 - 8#64 := by bv_omega

theorem spqrSendSavedRegs_eq_sp0 (s0 : State) :
    spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold spqrSendSavedRegs
  simp only [BitVec.ofNat_eq_ofNat, sp_sub_8064_add_7968, sp_sub_8064_add_7976,
    sp_sub_8064_add_7984, sp_sub_8064_add_7992, sp_sub_8064_add_8000, sp_sub_8064_add_8008,
    sp_sub_8064_add_8016, sp_sub_8064_add_8024, sp_sub_8064_add_8032, sp_sub_8064_add_8040,
    sp_sub_8064_add_8048, sp_sub_8064_add_8056]

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_3968_add_608 (sp0 : BitVec 64) :
    (sp0 - 3968#64) + 608#64 = (sp0 - 8064#64) + 0x1260#64 := by bv_omega

theorem memRegion_7968_split_probes (sp0 : BitVec 64) :
    memRegion (sp0 - 0x1f80#64) 0x1f20 =
      (∃∗ v0 : BitVec 64, ((sp0 - 0x1f80#64) ↦₆₄ v0)) ∗
      memRegion (sp0 - 8056#64) 3864 ∗
      (∃∗ v_probe : BitVec 64, ((sp0 - 4192#64) ↦₆₄ v_probe)) ∗
      memRegion (sp0 - 4184#64) 4088 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 0xf20) (k := 4096)
        (b' := sp0 - 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 8) (k := 3864)
        (b' := sp0 - 8056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4192#64) (n := 8) (k := 4088)
        (b' := sp0 - 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp0 - 0x1f80#64),
      ProofLib.memRegion_eight (sp0 - 4192#64),
      sepConj_assoc]

theorem probes_entails_memRegion_7968 (sp0 v0 v_probe : BitVec 64) :
    ((sp0 - 0x1f80#64) ↦₆₄ v0) ∗
      memRegion (sp0 - 8056#64) 3864 ∗
      ((sp0 - 4192#64) ↦₆₄ v_probe) ∗
      memRegion (sp0 - 4184#64) 4088 ⊢
      memRegion (sp0 - 0x1f80#64) 0x1f20 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 0xf20) (k := 4096)
        (b' := sp0 - 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 8) (k := 3864)
        (b' := sp0 - 8056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4192#64) (n := 8) (k := 4088)
        (b' := sp0 - 4184#64) rfl (by bv_omega) (by decide),
      sepConj_assoc]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (sp0 - 0x1f80#64) v0)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp0 - 4192#64) v_probe)))

theorem optChainPBAt_none_entails_memRegion_80' (A : RustAlloc) (a : BitVec 64) :
    ProtoRepr.optChainPBAt A a none ⊢ memRegion a 80 := by
  unfold ProtoRepr.optChainPBAt
  rw [ProofLib.memRegion_split a 8 72 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a LibsignalTripleRatchetRepr.noneCap)

theorem memRegion_rejoin_60_80 (fsp : BitVec 64) :
    memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 80 ∗ memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion fsp 0x1f20 := by
  rw [← ProofLib.memRegion_split' (b := fsp + 0x60#64) (n := 80) (k := 0x1f20 - 0xb0)
        (b' := fsp + 0xb0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp) (n := 0x60) (k := 0x1f20 - 0x60)
        (b' := fsp + 0x60#64) rfl rfl (by decide)]

/-! ## Prologue (`+0..+76`, `0x3085c..0x308a8`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_add_30_add_30 (fsp : BitVec 64) :
    (fsp + 0x30#64) + 0x30#64 = fsp + 0x60#64 := by bv_omega

theorem stackAt_spqrSendCallee_split_dropStack48 (fsp : BitVec 64) :
    stackAt fsp spqrSendCalleeStack =
      memRegion (fsp - 123008#64) (spqrSendCalleeStack - dropStack48) ∗
      stackAt fsp dropStack48 :=
  ProofLib.stackAt_split_bottom fsp dropStack48 (spqrSendCalleeStack - dropStack48) (by decide)

theorem stackAt_spqrSendCallee_split_allocHook (fsp : BitVec 64) :
    stackAt fsp spqrSendCalleeStack =
      memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
      stackAt fsp allocHookStack :=
  ProofLib.stackAt_split_bottom fsp allocHookStack (spqrSendCalleeStack - allocHookStack) (by decide)

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

@[expose] def chainPBRestAt (A : RustAlloc) (a cap ptr : BitVec 64) (ch : ChainPB) : SepProp :=
  ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
    vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr ch.links ∗
    rustBytesVecAt A (a + 0x18#64) ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    ProtoRepr.optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

theorem vecBuf_chainEpochPB_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (links : List ChainEpochPB) :
    vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr links ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr links := by
  unfold vecBuf
  apply Entails.pure_left; intro hp
  have hlt : cap.toNat < 2 ^ 63 := by
    have hmul := hp.2.1
    have hsz : chainEpochPBSize = 112 := rfl
    rw [hsz] at hmul
    omega
  exact Entails.pure_right hlt (Entails.pure_right hp (Entails.refl _))

theorem chainPBAt_entails_first_word (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    ProtoRepr.chainPBAt A a ch ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap) ∗
        chainPBRestAt A a cap ptr ch := by
  unfold ProtoRepr.chainPBAt ProtoRepr.chainLinksVecAt vecOf vecAt vecHeader chainPBRestAt
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (vecBuf_chainEpochPB_cap_lt A cap ptr ch.links))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem first_word_entails_chainPBAt (A : RustAlloc) (a cap ptr : BitVec 64) (ch : ChainPB) :
    (a ↦₆₄ cap) ∗ chainPBRestAt A a cap ptr ch ⊢ ProtoRepr.chainPBAt A a ch := by
  unfold ProtoRepr.chainPBAt ProtoRepr.chainLinksVecAt vecOf vecAt vecHeader chainPBRestAt
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem versionNegotiationPBTailAt_entails_memRegion_32 (a16 : BitVec 64) (v : VersionNegotiationPB) :
    DecodeState.versionNegotiationPBTailAt a16 v ⊢ memRegion a16 32 := by
  unfold DecodeState.versionNegotiationPBTailAt
  have hcp : ProtoRepr.optChainParamsPBAt (a16 + 8#64) v.chainParams ⊢ memRegion (a16 + 8#64) 12 := by
    cases v.chainParams with
    | none =>
      unfold ProtoRepr.optChainParamsPBAt
      dsimp only
      rw [ProofLib.memRegion_split' (b := a16 + 8#64) (n := 4) (k := 8)
            (b' := (a16 + 8#64) + 4#64) rfl rfl (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)
    | some cp =>
      unfold ProtoRepr.optChainParamsPBAt ProtoRepr.chainParamsPBAt
      dsimp only
      have ha8 : ((a16 + 8#64) + 4#64) + 4#64 = (a16 + 8#64) + 8#64 := by bv_omega
      rw [ha8,
          ProofLib.memRegion_split' (b := a16 + 8#64) (n := 4) (k := 8)
            (b' := (a16 + 8#64) + 4#64) rfl rfl (by decide),
          ProofLib.memRegion_split' (b := (a16 + 8#64) + 4#64) (n := 4) (k := 4)
            (b' := (a16 + 8#64) + 8#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
          (ProofLib.pointsTo32_entails_memRegion _ _))
  rw [ProofLib.memRegion_split' (b := a16) (n := 8) (k := 24) (b' := a16 + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a16 + 8#64) (n := 12) (k := 12) (b' := a16 + 20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a16 + 20#64) (n := 4) (k := 8) (b' := a16 + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a16 + 24#64) (n := 4) (k := 4) (b' := a16 + 28#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono hcp
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))))

theorem optVersionNegotiationPBTail_cleanup_entails (A : RustAlloc) (a30 w0 w1 : BitVec 64)
    (optVn : Option VersionNegotiationPB) :
    (a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) optVn ⊢
      if BitVec.slt w0 1#64 then
        memRegion a30 48
      else
        ⌜0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
        ((a30 + 8#64) ↦₆₄ w1) ∗
        memRegion a30 8 ∗
        memRegion (a30 + 16#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat := by
  cases optVn with
  | none =>
    unfold DecodeState.optVersionNegotiationPBTailAt
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          memRegion (a30 + 16#64) 32) =
        ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hw0
    subst hw0
    have hslt : BitVec.slt LibsignalTripleRatchetRepr.noneCap 1#64 = true := by decide
    simp only [hslt, ↓reduceIte]
    rw [ProofLib.memRegion_split' (b := a30) (n := 8) (k := 40) (b' := a30 + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  | some v =>
    unfold DecodeState.optVersionNegotiationPBTailAt vecU8Heap
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (versionNegotiationPBTailAt_entails_memRegion_32 (a30 + 16#64) v)))) ?_
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗
         ⌜v.authKey.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
         (if w0 = 0 then emp
          else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ v.authKey) ∗
            memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length))) =
        ⌜v.authKey.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗
           (if w0 = 0 then emp
            else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ v.authKey) ∗
              memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length))) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    by_cases hw0 : w0 = 0#64
    · subst hw0
      have hslt : BitVec.slt 0#64 1#64 = true := by decide
      have h0eq : (0#64 : BitVec 64) = 0 := rfl
      simp only [h0eq, hslt, ↓reduceIte, sepConj_emp]
      rw [ProofLib.memRegion_split' (b := a30) (n := 8) (k := 40) (b' := a30 + 8#64) rfl rfl (by decide),
          ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    · have hw0_pos : 0 < w0.toNat := by bv_omega
      have hslt : BitVec.slt w0 1#64 = false := by
        revert hw0 hcap_lt
        bv_bits
      have hw0' : w0 ≠ 0 := hw0
      simp only [hw0', hslt, Bool.false_eq_true, ↓reduceIte]
      apply Entails.pure_right ⟨hw0_pos, hcap_lt, hptr_ne⟩
      have hbuf : (w1 ↦ₛ v.authKey) ∗
          memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length) ⊢
          memRegion w1 w0.toNat := by
        have hsplit : w0.toNat = v.authKey.length + (w0.toNat - v.authKey.length) := by omega
        conv_rhs => rw [hsplit]
        rw [ProofLib.memRegion_split w1 v.authKey.length (w0.toNat - v.authKey.length) (by omega)]
        exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion w1 v.authKey)
      have ha30 := ProofLib.pointsTo64_entails_memRegion a30 w0
      refine Entails.trans
        (Entails.of_eq (show _ =
          (a30 ↦₆₄ w0) ∗
          (((w1 ↦ₛ v.authKey) ∗
            memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length)) ∗
           (((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗ A.live w1 w0.toNat 1)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono ha30 (sepConj_mono_left hbuf)) ?_
      exact Entails.of_eq (by ac_rfl)

theorem memRegion_rejoin_30_48 (fsp : BitVec 64) :
    memRegion fsp 0x30 ∗ memRegion (fsp + 0x30#64) 48 = memRegion fsp 0x60 := by
  rw [← ProofLib.memRegion_split' (b := fsp) (n := 0x30) (k := 48)
        (b' := fsp + 0x30#64) rfl rfl (by decide)]

theorem memRegion_rejoin_30_8_8_32 (fsp w1 : BitVec 64) :
    memRegion fsp 0x30 ∗ memRegion (fsp + 0x30#64) 8 ∗
      ((fsp + 0x38#64) ↦₆₄ w1) ∗ memRegion (fsp + 0x40#64) 32 ⊢
      memRegion fsp 0x60 := by
  rw [← memRegion_rejoin_30_48 fsp,
      ProofLib.memRegion_split' (b := fsp + 0x30#64) (n := 8) (k := 40)
        (b' := fsp + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x38#64) (n := 8) (k := 32)
        (b' := fsp + 0x40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x38#64) w1)))

end CryptoVerification.SpqrV1.Top.Send
