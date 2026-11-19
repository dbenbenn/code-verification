/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsDeserialize
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddresses
import LibsignalBinary.Proofs.E2E.Bin.SegCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.E2E.StoreNew.Proof
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.CodeLayout

/-! # Store-Initialization and Save-Identity Segment Proofs for `libsignal_e2e::open` (`0x43bfc..0x43c6c`) -/

public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

namespace OpenStoreSegsCombinators

theorem segExit_of_subroutine_ok_codeLoaded {α β : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {calleeEntry : BitVec 64} {calleeSpec : Spec β} {gc : β} {Rc : SepProp} {s0 s1 : State} {next : State → Prop}
    (hCallee : subroutine_ok prog calleeEntry calleeSpec)
    (hpc : s1.pc = calleeEntry) (hrun : s1.status = .Running) (hal : s1.spAligned = true)
    (hpre : s1.mem ⊨ calleeSpec.pre gc s1 ∗ Rc)
    (hpost : ∀ s2, prog.CodeLoaded s1.mem → Steps prog s1 s2 →
      (Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧ s2.mem ⊨ calleeSpec.post gc s1 s2 ∗ Rc) →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hpanic : ∀ s2, s2.status = .Panicked → s2.mem ⊨ calleeSpec.onPanic gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hexit : ∀ code s2, s2.mem ⊨ calleeSpec.onExit gc code s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onExit g code s0 s2 ∗ R)
    (hoom : ∀ s2, s2.mem ⊨ calleeSpec.onOom gc s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onOom g s0 s2 ∗ R := by intro _ h; exact (not_satisfies_false_sepConj (h : _ ⊨ ⌜False⌝ ∗ _)).elim) :
    SegExit prog spec g R s0 s1 next := by
  intro hL
  exact segExit_of_subroutine_ok hCallee hpc hrun hal hpre
    (fun s2 hst hok => hpost s2 hL hst hok)
    hpanic hexit
    (fun s2 hoom_s2 hmo => Or.inr (Or.inr (Or.inr (Or.inr ⟨hoom_s2, hoom s2 hmo⟩))))
    hL

theorem memRegion_24_eq_three_words (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply RawByteMove.sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u0 =>
      Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.of_eq (by ac_rfl))))
  · exact Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_right u2 (Entails.sepExists_right u1 (Entails.sepExists_right u0 (Entails.of_eq (by ac_rfl))))

theorem memRegion_open_0x258_poll_split (sp : BitVec 64) :
    memRegion (sp + 0x258#64) 0x138 =
      memRegion (sp + 0x258#64) 0xe8 ∗ memRegion (sp + 0x340#64) 48 ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u0) ∗ ((sp + 0x378#64) ↦₆₄ u1) ∗ ((sp + 0x380#64) ↦₆₄ u2)) ∗
      memRegion (sp + 0x388#64) 8 := by
  rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x340#64) (N := 0x138) (n := 0xe8) (k := 80) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x370#64) (N := 80) (n := 48) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x388#64) (N := 32) (n := 24) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_24_eq_three_words (sp + 0x370#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_open_0x258_poll_join (sp w0 w1 w2 w3 : BitVec 64) :
    (memRegion (sp + 0x258#64) 0xe8 ∗ ((sp + 0x340#64) ↦₆₄ w0) ∗ memRegion (sp + 0x348#64) 40 ∗
     ((sp + 0x370#64) ↦₆₄ w1) ∗ ((sp + 0x378#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
     memRegion (sp + 0x388#64) 8) ⊢ memRegion (sp + 0x258#64) 0x138 := by
  have h48 : (((sp + 0x340#64) ↦₆₄ w0) ∗ memRegion (sp + 0x348#64) 40) ⊢ memRegion (sp + 0x340#64) 48 := by
    rw [memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x348#64) (N := 48) (n := 8) (k := 40) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  rw [memRegion_open_0x258_poll_split sp]; refine sepConj_mono_right ?_
  rw [← sepConj_assoc ((sp + 0x340#64) ↦₆₄ w0)]; refine sepConj_mono h48 ?_
  rw [← sepConj_assoc ((sp + 0x370#64) ↦₆₄ w1), ← sepConj_assoc (((sp + 0x370#64) ↦₆₄ w1) ∗ _)]
  exact sepConj_mono_left (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl)))))

end OpenStoreSegsCombinators

open OpenStoreSegsCombinators

/-! ## Segment 5: `open_seg_stores_init'` (`+0x1c4..+0x1e0`, 7 insns) -/

private theorem memRegion_bottom_storesInit_sessionStoreNew (sp0 sp1 : BitVec 64) (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0x20 + extHookStack)) ∗ stackAt sp1 (0x20 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0x20 + extHookStack) hsp (by decide) (by decide)

private theorem memRegion_bottom_storesInit_identityStoreNew (sp0 sp1 : BitVec 64) (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - 0x30) ∗ stackAt sp1 0x30 :=
  memRegion_bottom_open_split sp0 sp1 0x30 hsp (by decide) (by decide)

private theorem memRegion_open_0x170_stores_split (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x170 =
      memRegion (sp + 0x170#64) 0x20 ∗ memRegion (sp + 0x190#64) 0x20 ∗
      memRegion (sp + 0x1b0#64) 48 ∗ memRegion (sp + 0x1e0#64) 120 ∗ memRegion (sp + 0x258#64) 0x88 := by
  rw [memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x190#64) (N := 0x170) (n := 0x20) (k := 0x150) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x1b0#64) (N := 0x150) (n := 0x20) (k := 0x130) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1e0#64) (N := 0x130) (n := 48) (k := 256) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x1e0#64) (b' := sp + 0x258#64) (N := 256) (n := 120) (k := 0x88) (by decide) (by bv_lin) (by decide)]

private theorem memRegion_open_0x258_join_0xc8 (sp : BitVec 64) (role : Role) :
    (memRegion (sp + 0x258#64) 0x88 ∗ ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes)) ⊢
      memRegion (sp + 0x258#64) 0xc8 := by
  have hkp : ((sp + 0x2e0#64) ↦ₛ role.keyPairBytes) ⊢ memRegion (sp + 0x2e0#64) 0x40 := by
    have hlen : role.keyPairBytes.length = 0x40 := by cases role <;> decide
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 0x2e0#64) role.keyPairBytes; rwa [hlen] at h
  rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x2e0#64) (N := 0xc8) (n := 0x88) (k := 0x40) (by decide) (by bv_lin) (by decide)]
  exact sepConj_mono_right hkp

private theorem truncate32_truncate8 (v : BitVec 64) :
    (v.truncate 32).truncate 8 = v.truncate 8 := by bv_omega

private theorem role_peer_keyBytes_length (r : Role) :
    r.peer.idKey.publicKey.bytes.toList.length = 32 := r.peer.idKey.publicKey.bytes.toList_length

private theorem memRegion_open_0x340_poll_split (sp : BitVec 64) :
    memRegion (sp + 0x340#64) 0x50 =
      memRegion (sp + 0x340#64) 48 ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u0) ∗ ((sp + 0x378#64) ↦₆₄ u1) ∗ ((sp + 0x380#64) ↦₆₄ u2)) ∗
      memRegion (sp + 0x388#64) 8 := by
  rw [memRegion_split' (b := sp + 0x340#64) (b' := sp + 0x370#64) (N := 0x50) (n := 48) (k := 32) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x388#64) (N := 32) (n := 24) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_24_eq_three_words (sp + 0x370#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_open_0x258_save_join (sp w0 w1 w2 w3 : BitVec 64) (v32 : BitVec 32)
    (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    (memRegion (sp + 0x258#64) 0xc8 ∗ ((sp + 0x320#64) ↦ₛ bs) ∗
     ((sp + 0x340#64) ↦₆₄ w0) ∗ ((sp + 0x348#64) ↦₃₂ v32) ∗ memRegion (sp + 0x34c#64) 36 ∗
     ((sp + 0x370#64) ↦₆₄ w1) ∗ ((sp + 0x378#64) ↦₆₄ w2) ∗ ((sp + 0x380#64) ↦₆₄ w3) ∗
     memRegion (sp + 0x388#64) 8) ⊢ memRegion (sp + 0x258#64) 0x138 := by
  have h32 : ((sp + 0x320#64) ↦ₛ bs) ⊢ memRegion (sp + 0x320#64) 0x20 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 0x320#64) bs; rwa [hbs] at h
  have h40 : (((sp + 0x348#64) ↦₃₂ v32) ∗ memRegion (sp + 0x34c#64) 36) ⊢ memRegion (sp + 0x348#64) 40 := by
    rw [memRegion_split' (b := sp + 0x348#64) (b' := sp + 0x34c#64) (N := 40) (n := 4) (k := 36) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have he8 : (memRegion (sp + 0x258#64) 0xc8 ∗ ((sp + 0x320#64) ↦ₛ bs)) ⊢ memRegion (sp + 0x258#64) 0xe8 := by
    rw [memRegion_split' (b := sp + 0x258#64) (b' := sp + 0x320#64) (N := 0xe8) (n := 0xc8) (k := 0x20) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono_right h32
  refine Entails.trans ?_ (memRegion_open_0x258_poll_join sp w0 w1 w2 w3)
  rw [← sepConj_assoc (memRegion (sp + 0x258#64) 0xc8)]
  refine sepConj_mono he8 (sepConj_mono_right ?_)
  rw [← sepConj_assoc ((sp + 0x348#64) ↦₃₂ v32)]; exact sepConj_mono_left h40

end CryptoVerification.E2E.Bin
