/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.SymWP
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segLoad` Prologue, `load_session` Shim, and Poll (`+0x000..+0x160`)

Steps from entry (`+0x000`) of `session_message_encrypt_with_stores` through prologue spills,
`loadShim`, `loadPoll`, 312-byte tail `memcpy`, future drop, and 24-byte future box deallocation
to the post-poll dispatch point `+0x160`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, arm64_norm, wp_norm]
theorem spAligned_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).spAligned = s.spAligned := rfl

@[simp, arm64_norm, wp_norm]
theorem loadBoxSize_ofNat_toNat {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    (BitVec.ofNat 64 kit.loadBoxSize).toNat = kit.loadBoxSize :=
  Nat.mod_eq_of_lt kit.loadBoxSize_lt

/-! ## Frame Fold Helpers -/

theorem out368_fold (sp w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((sp + 0x5b0#64) ↦₆₄ w6) ∗ ((sp + 0x5b8#64) ↦ₛ tail) ⊢
      memRegion (sp + 0x580#64) 368 := by
  have h1 :
      ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗ ((sp + 0x5b8#64) ↦ₛ tail) =
      recordWords56At (sp + 0x580#64) w0 w1 w2 w3 w4 w5 w6 ∗
        ((sp + 0x580#64 + 0x38#64) ↦ₛ tail) := by
    unfold recordWords56At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [h1, memRegion_split (sp + 0x580#64) 56 312 (by decide)]
  have h38 : sp + 0x580#64 + BitVec.ofNat 64 56 = sp + 0x580#64 + 0x38#64 := rfl
  rw [h38]
  refine sepConj_mono (recordWords56At_entails_memRegion _ _ _ _ _ _ _ _) ?_
  have ht := pointsToBytes_entails_memRegion (sp + 0x580#64 + 0x38#64) tail
  rwa [htail] at ht

theorem pointsTo128_concat_eq_pair (p w4 w5 : BitVec 64) :
    (p ↦₁₂₈ (w5 ++ w4)) = (p ↦₆₄ w4) ∗ ((p + 8#64) ↦₆₄ w5) :=
  (pointsTo64_pair p w4 w5).symm

theorem loadPollOutAtS_decompose_sp (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b sp : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    loadPollOutAtS Scope A b (sp + 0x580#64) ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗ ((sp + 0x5b8#64) ↦ₛ tail) ∗
        LoadOutRes Scope A b ans w0 w1 w2 w3 w4 w5 w6 tail := by
  have h := loadPollOutAtS_decompose Scope A b (sp + 0x580#64) ans
  simpa only [pointsTo128_concat_eq_pair, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem ne_neg3_add3_ne_zero {w0 : BitVec 64} (hne : w0 ≠ 0xFFFFFFFFFFFFFFFD#64) :
    (w0 + 3#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h1 : w0 + 3#64 - 3#64 = 0#64 - 3#64 := congrArg (· - 3#64) h
  simpa [BitVec.add_sub_cancel] using h1

theorem stack_encSub_poll_to_dealloc_eq {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    {sp sp1 : BitVec 64} (h : sp1 = sp) :
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
      stackAt sp kit.loadPollStack =
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
      stackAt sp1 allocHookStack := by
  rw [h]
  exact (stack_encSubV_split kit ikit sp kit.loadPollStack (loadPollStack_le_encSubStackV kit ikit) hsub).symm.trans
    (stack_encSubV_split kit ikit sp allocHookStack (allocHookStack_le_encSubStackV kit ikit) hsub)

theorem stack_encSub_dealloc_back_eq {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    {sp sp1 : BitVec 64} (h : sp1 = sp) :
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
      stackAt sp1 allocHookStack =
    stackAt sp (encSubStackV kit ikit) := by
  rw [h]
  exact (stack_encSubV_split kit ikit sp allocHookStack (allocHookStack_le_encSubStackV kit ikit) hsub).symm

/-! ## Poll Ready Path (`+0x0ac..+0x160`) -/

theorem sepWP_conseq {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post post' : State → SepProp → Prop}
    (hpre : P = P')
    (h : SepWP prog target_pc s P' post)
    (himp : ∀ sf P_f, post sf P_f → post' sf P_f) :
    SepWP prog target_pc s P post' := by
  rw [hpre]
  exact SepWP.mono h fun sf P_f _ _ hp => himp sf P_f hp

theorem stack_encSub_shim_to_poll_eq {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    {sp sp1 : BitVec 64} (h : sp1 = sp) :
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      stackAt sp1 kit.loadShimStack =
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
      stackAt sp kit.loadPollStack := by
  rw [h]
  exact stack_encSub_shim_to_poll kit ikit sp hsub

theorem exists_pointsTo128_eq_two_pointsTo64 (p : BitVec 64) :
    (∃∗ q : BitVec 128, p ↦₁₂₈ q) =
      (∃∗ v0 : BitVec 64, p ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (p + 8#64) ↦₆₄ v1) := by
  rw [← memRegion_sixteen p, memRegion_split p 8 8 (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]

theorem sub_60_sub_11_eq_sub_be0_add_b6f (sp0 : BitVec 64) :
    sp0 - 96#64 - 17#64 = (sp0 - 0xbe0#64) + 0xb6f#64 := by
  bv_omega

theorem add_60_cancel (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_omega

theorem add_68_eq_add_8 (sp0 : BitVec 64) :
    sp0 - 96#64 + 104#64 = sp0 + 8#64 := by
  bv_omega

theorem fold_sp50_sub (sp0 : BitVec 64) :
    ((sp0 - 3040#64) ↦₆₄ 0#64) ∗ memRegion (sp0 - 3032#64) 72 ⊢
      memRegion (sp0 - 0xbe0#64) 0x50 := by
  rw [show sp0 - 3032#64 = (sp0 - 0xbe0#64) + 8#64 by bv_omega]
  exact fold_sp50 (sp0 - 0xbe0#64) 0#64

theorem encSpillsInit_sub_fold (ss_vt id_vt sp0 : BitVec 64) (x : WithStoresEncGhost) :
    ((sp0 - 2952#64) ↦₆₄ x.now.tvSec) ∗ ((sp0 - 2944#64) ↦₃₂ x.now.tvNsec) ∗
    memRegion (sp0 - 2940#64) 4 ∗ ((sp0 - 2936#64) ↦₆₄ x.ptA) ∗
    ((sp0 - 2928#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp0 - 2920#64) ↦₆₄ x.remA) ∗
    ((sp0 - 2912#64) ↦₆₄ x.locA) ∗ ((sp0 - 2904#64) ↦₆₄ x.ssA) ∗
    ((sp0 - 2896#64) ↦₆₄ ss_vt) ∗
    ((sp0 - 2888#64) ↦₆₄ x.idA) ∗ ((sp0 - 2880#64) ↦₆₄ id_vt) ∗
    ((sp0 - 2872#64) ↦₆₄ (sp0 - 113#64)) ∗ ((sp0 - 2864#64) ↦₆₄ x.ptA) ∗
    ((sp0 - 2856#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp0 - 2848#64) ↦₆₄ x.remA) ∗
    ((sp0 - 2840#64) ↦₆₄ x.locA) ∗ ((sp0 - 2832#64) ↦₆₄ x.ssA) ∗
    ((sp0 - 2824#64) ↦₆₄ ss_vt) ∗
    ((sp0 - 2816#64) ↦₆₄ x.idA) ∗ ((sp0 - 2808#64) ↦₆₄ id_vt) ∗
    ((sp0 - 2800#64) ↦₆₄ x.now.tvSec) ∗ ((sp0 - 2792#64) ↦₃₂ x.now.tvNsec) ∗
    memRegion (sp0 - 2788#64) 4 ∗ ((sp0 - 2784#64) ↦₆₄ (sp0 - 113#64)) ⊢
      encSpillsInit ss_vt id_vt (sp0 - 0xbe0#64) x := by
  unfold encSpillsInit
  simp only [arm64_norm]
  exact Entails.refl _

theorem pointsTo16_zero_sub (sp0 : BitVec 64) :
    ((sp0 - 1912#64) ↦₁₆ 0#16) ⊢
      ((sp0 - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((sp0 - 0xbe0#64 + 0x469#64) ↦₈ 0#8) := by
  rw [show sp0 - 1912#64 = sp0 - 0xbe0#64 + 0x468#64 by bv_omega,
      pointsTo16_zero_eq_pointsTo8_pair, BitVec.add_assoc]
  exact Entails.refl _

theorem encSubStack_split_store {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A b)
    (x : WithStoresEncGhost) (s0 : State) (hsp : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt x.ssA st0 ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ⊢
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        (kit.storeAt x.ssA st0 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - encSubStack)) := by
  have hlt := s0.sp.isLt
  have hle := encSubStack_le_encSubStackV kit ikit
  have hsp' : encSubStackV kit ikit + 3040 ≤ s0.sp.toNat := hsp
  have hsplit := stackAt_split_bottom (s0.sp - 0xbe0#64) encSubStack
    (encSubStackV kit ikit - encSubStack) (by omega)
  rw [Nat.add_sub_of_le hle] at hsplit
  rw [hsplit]
  exact Entails.of_eq (by ac_rfl)

theorem tapeAt_eq_pure_sep_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest = ⌜rest.length < 2 ^ 63⌝ ∗ tapeAfter ctl cur rest 0 := by
  simp [tapeAt, tapeAfter]

theorem sepWP_conseq_pc_run {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post post' : State → SepProp → Prop}
    (hpre : P = P')
    (h : SepWP prog target_pc s P' post)
    (himp : ∀ sf P_f, sf.pc = target_pc → sf.status = .Running → post sf P_f → post' sf P_f) :
    SepWP prog target_pc s P post' := by
  rw [hpre]
  exact SepWP.mono h himp

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
