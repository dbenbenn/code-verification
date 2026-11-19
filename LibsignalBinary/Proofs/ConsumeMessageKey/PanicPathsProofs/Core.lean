/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Fetch
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import

public section

namespace CryptoVerification.LibsignalSession.PanicPaths

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[expose] def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem pointsTo8_eq_pointsToBytes (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsToBytes1_seven_entails_cell64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦ₛ [b]) ∗ memRegion (a + 1#64) 7 ⊢ ∃∗ v : BitVec 64, a ↦₆₄ v := by
  rw [← pointsTo8_eq_pointsToBytes, ← memRegion_eight]
  have hsplit := memRegion_split a 1 7 (by decide)
  change memRegion a 8 = memRegion a 1 ∗ memRegion (a + 1#64) 7 at hsplit
  rw [hsplit, memRegion_one]
  exact sepConj_mono_left (Entails.sepExists_intro b)

theorem memRegion_frame_panicPaths (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp0 - 320#64) ↦₈ b0) ∗
        memRegion (sp0 - 319#64) 7 ∗
        ((sp0 - 312#64) ↦₆₄ u1) ∗
        ((sp0 - 304#64) ↦₆₄ u2) ∗
        ((sp0 - 296#64) ↦₆₄ u3) ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 352#64) 32 ∗ memRegion (sp0 - 288#64) 64 ∗ memRegion (sp0 - 192#64) 96) := by
  have h1 := memRegion_split (sp0 - BitVec.ofNat 64 352) 32 224 (by decide)
  have h2 := memRegion_split (sp0 - BitVec.ofNat 64 320) 1 223 (by decide)
  have h3 := memRegion_split (sp0 - BitVec.ofNat 64 319) 7 216 (by decide)
  have h4 := memRegion_split (sp0 - BitVec.ofNat 64 312) 24 192 (by decide)
  have h5 := memRegion_split (sp0 - BitVec.ofNat 64 288) 64 128 (by decide)
  have h6 := memRegion_split (sp0 - BitVec.ofNat 64 224) 32 96 (by decide)
  rw [bv_sub_add_lit sp0 352 32] at h1
  rw [bv_sub_add_lit sp0 320 1] at h2
  rw [bv_sub_add_lit sp0 319 7] at h3
  rw [bv_sub_add_lit sp0 312 24] at h4
  rw [bv_sub_add_lit sp0 288 64] at h5
  rw [bv_sub_add_lit sp0 224 32] at h6
  change memRegion (sp0 - 352#64) 256 = memRegion (sp0 - 352#64) 32 ∗ memRegion (sp0 - 320#64) 224 at h1
  change memRegion (sp0 - 320#64) 224 = memRegion (sp0 - 320#64) 1 ∗ memRegion (sp0 - 319#64) 223 at h2
  change memRegion (sp0 - 319#64) 223 = memRegion (sp0 - 319#64) 7 ∗ memRegion (sp0 - 312#64) 216 at h3
  change memRegion (sp0 - 312#64) 216 = memRegion (sp0 - 312#64) 24 ∗ memRegion (sp0 - 288#64) 192 at h4
  change memRegion (sp0 - 288#64) 192 = memRegion (sp0 - 288#64) 64 ∗ memRegion (sp0 - 224#64) 128 at h5
  change memRegion (sp0 - 224#64) 128 = memRegion (sp0 - 224#64) 32 ∗ memRegion (sp0 - 192#64) 96 at h6
  have hc3 : memRegion (sp0 - 312#64) 24 =
      ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp0 - 312#64) ↦₆₄ u1) ∗ ((sp0 - 304#64) ↦₆₄ u2) ∗ ((sp0 - 296#64) ↦₆₄ u3) := by
    rw [show (24 : Nat) = 8 * 3 from rfl, memRegion_cells _ 3 (by decide)]
    cells_unfold
  rw [h1, h2, h3, h4, h5, h6, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  rw [hc3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun b0 => congrArg sepExists (funext fun u1 =>
    congrArg sepExists (funext fun u2 => congrArg sepExists (funext fun u3 => ?_))))
  ac_rfl

theorem ratchetAt_expose_panicPaths (A : RustAlloc) (self : BitVec 64) (Gc : RatchetGhost) (stc : RatchetState) :
    ratchetAt A self Gc stc ⊢
      ⌜Gc.chains.length = stc.receiverChains.length ∧
        (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63⌝ ∗
      ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
      arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
      ((self ↦₆₄ Gc.chainsCap) ∗
        (if Gc.chainsCap = 0 then emp
         else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
           memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
             ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) := by
  unfold ratchetAt vecAt vecHeader
  apply Entails.pure_left
  rintro ⟨hlen, _, _⟩
  have h_exp := vecBuf_expose_arrayAt A 104 8 (chainAt A) Gc.chainsCap Gc.chainsPtr
    (Gc.chains.zip stc.receiverChains)
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right h_exp)) ?_
  have heq1 :
      (((self ↦₆₄ Gc.chainsCap ∗
          (self + 8#64) ↦₆₄ Gc.chainsPtr ∗
          (self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
        (⌜(Gc.chains.zip stc.receiverChains).length ≤ Gc.chainsCap.toNat ∧
            Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧
            (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
          arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
          (if Gc.chainsCap = 0 then emp
           else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
             memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
               ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)))) ∗
        (self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad ∗
        (self + 128#64) ↦ₛ keyToBytes32 stc.rootKey ∗
        (self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps ∗
        (self + 168#64) ↦₃₂ stc.previousCounter ∗ memRegion (self + 172#64) 4) =
      (⌜(Gc.chains.zip stc.receiverChains).length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧
          (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
        (((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
          arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
          ((self ↦₆₄ Gc.chainsCap) ∗
            (if Gc.chainsCap = 0 then emp
             else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
               memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
                 ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)) ∗
            ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
            ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
            ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
            ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4))) := by
    ac_rfl
  rw [heq1]
  apply Entails.pure_left
  rintro ⟨_, _, hxs_lt, _⟩
  exact Entails.pure_right ⟨hlen, hxs_lt⟩ (Entails.refl _)

@[expose] def cmkPanicPathsUsed [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State)
    (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) : SepProp :=
  ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
  arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 4096 ∗
  ((s0.sp - 320#64) ↦₈ b0) ∗
  memRegion (s0.sp - 319#64) 7 ∗
  ((s0.sp - 312#64) ↦₆₄ u1) ∗
  ((s0.sp - 304#64) ↦₆₄ u2) ∗
  ((s0.sp - 296#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 224#64) 32 ∗
  A.pool

theorem cmkLoopHeap_decompose_panicPaths [LibsignalPlacement] {A : RustAlloc} {img : Unit} {x : ConsumeMessageKeyGhost}
    {Gc : RatchetGhost} {stc : RatchetState} {ckc : ChainKey} {s0 : State}
    {R : SepProp} {m : Memory}
    (h : m ⊨ cmkLoopHeap A img x Gc stc ckc s0 ∗ R) :
    ∃ (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) (R_unused : SepProp),
      Gc.chains.length = stc.receiverChains.length ∧
      (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 ∧
      (m ⊨ cmkPanicPathsUsed A img x Gc stc ckc s0 b0 u1 u2 u3 ∗ (R_unused ∗ R)) := by
  unfold cmkLoopHeap chainKeyBytes cmkLoopFrame at h
  have h_stk := stackAt_split_bottom (s0.sp - 480#64) 4096 3616 (by decide)
  change stackAt (s0.sp - 480#64) 7712 =
    memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗ stackAt (s0.sp - 480#64) 4096 at h_stk
  rw [pointsToBytes_append, h_stk, memRegion_frame_panicPaths s0.sp] at h
  have h' := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_panicPaths A x.self Gc stc))) h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at h'
  obtain ⟨b0, u1, u2, u3, ⟨hlen, hxs_lt⟩, hm⟩ := h'
  refine ⟨b0, u1, u2, u3,
    ((x.self ↦₆₄ Gc.chainsCap) ∗
      (if Gc.chainsCap = 0 then emp
       else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
         memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
           ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)) ∗
      ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
      ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
      ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
      ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
      ((x.ckA + BitVec.ofNat 64 (keyToBytes32 ckc.key).length) ↦ₛ leBytes 4 ckc.index.toNat) ∗
      memRegion x.ret 88 ∗
      memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
      memRegion (s0.sp - 480#64) 112 ∗ ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
      memRegion (s0.sp - 360#64) 4 ∗ ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
      memRegion (s0.sp - 352#64) 32 ∗ memRegion (s0.sp - 288#64) 64 ∗
      memRegion (s0.sp - 192#64) 96 ∗ cmkSavedRegs s0.sp s0),
    hlen, hxs_lt, ?_⟩
  unfold cmkPanicPathsUsed
  convert hm using 1
  ac_rfl

@[expose] def cmkPanicPathsUsedAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State)
    (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) : SepProp :=
  ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (Gc.chains.zip stc.receiverChains).length) ∗
  arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 4096 ∗
  ((s0.sp - 320#64) ↦₈ b0) ∗
  memRegion (s0.sp - 319#64) 7 ∗
  ((s0.sp - 312#64) ↦₆₄ u1) ∗
  ((s0.sp - 304#64) ↦₆₄ u2) ∗
  ((s0.sp - 296#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 224#64) 32 ∗
  A.pool

theorem cmkLoopHeapAt_decompose_panicPaths {A : RustAlloc} {logAddr : BitVec 64} {x : ConsumeMessageKeyGhost}
    {Gc : RatchetGhost} {stc : RatchetState} {ckc : ChainKey} {s0 : State}
    {R : SepProp} {m : Memory}
    (h : m ⊨ cmkLoopHeapAt A logAddr x Gc stc ckc s0 ∗ R) :
    ∃ (b0 : BitVec 8) (u1 u2 u3 : BitVec 64) (R_unused : SepProp),
      Gc.chains.length = stc.receiverChains.length ∧
      (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 ∧
      (m ⊨ cmkPanicPathsUsedAt A logAddr x Gc stc ckc s0 b0 u1 u2 u3 ∗ (R_unused ∗ R)) := by
  unfold cmkLoopHeapAt chainKeyBytes cmkLoopFrame at h
  have h_stk := stackAt_split_bottom (s0.sp - 480#64) 4096 3616 (by decide)
  change stackAt (s0.sp - 480#64) 7712 =
    memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗ stackAt (s0.sp - 480#64) 4096 at h_stk
  rw [pointsToBytes_append, h_stk, memRegion_frame_panicPaths s0.sp] at h
  have h' := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_panicPaths A x.self Gc stc))) h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at h'
  obtain ⟨b0, u1, u2, u3, ⟨hlen, hxs_lt⟩, hm⟩ := h'
  refine ⟨b0, u1, u2, u3,
    ((x.self ↦₆₄ Gc.chainsCap) ∗
      (if Gc.chainsCap = 0 then emp
       else A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
         memRegion (Gc.chainsPtr + BitVec.ofNat 64 ((Gc.chains.zip stc.receiverChains).length * 104))
           ((Gc.chainsCap.toNat - (Gc.chains.zip stc.receiverChains).length) * 104)) ∗
      ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
      ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
      ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
      ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
      ((x.ckA + BitVec.ofNat 64 (keyToBytes32 ckc.key).length) ↦ₛ leBytes 4 ckc.index.toNat) ∗
      memRegion x.ret 88 ∗
      memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
      memRegion (s0.sp - 480#64) 112 ∗ ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
      memRegion (s0.sp - 360#64) 4 ∗ ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
      memRegion (s0.sp - 352#64) 32 ∗ memRegion (s0.sp - 288#64) 64 ∗
      memRegion (s0.sp - 192#64) 96 ∗ cmkSavedRegs s0.sp s0),
    hlen, hxs_lt, ?_⟩
  unfold cmkPanicPathsUsedAt
  convert hm using 1
  ac_rfl

theorem reaches_outcome_panic_of_sepWPp {α : Type} {prog : Program} {ret : BitVec 64}
    {spec : Spec α} {x : α} {s0 s : State} {P R_unused R : SepProp}
    (hm : s.mem ⊨ P ∗ (R_unused ∗ R))
    (hwp : SepWPp prog ret s P (fun _ _ => False)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (R_unused ∗ R)) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨_, _, _, _, hfalse⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp (R_unused ∗ R) hm hL
  · exact hfalse.elim
  · exact reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan (hqp hmf))
  · exact (not_satisfies_false_sepConj hoom).elim

theorem steps_outcome_panic_of_sepWPp {α : Type} {prog : Program} {ret : BitVec 64}
    {spec : Spec α} {x : α} {s0 s : State} {P R_unused R : SepProp}
    (hm : s.mem ⊨ P ∗ (R_unused ∗ R)) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWPp prog ret s P (fun _ _ => False)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (R_unused ∗ R)) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    ∃ sf, Steps prog s sf ∧ SubroutineOutcome spec x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨_, _, _, _, hfalse⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp (R_unused ∗ R) hm hL
  · exact hfalse.elim
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem allowPanic_unused {φ : Prop} {P R_unused R : SepProp} {m : Memory}
    (hφ : φ) (h : m ⊨ P ∗ (R_unused ∗ R)) : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  rw [← sepConj_assoc] at h
  exact allowPanic_panicked hφ h

theorem keyToBytes32_length (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem sha256With_length (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  rcases (chunks64 (sha256Pad m)).foldl F sha256IV with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩ <;>
    try (cases hl)
  rfl

theorem hmacWith_length (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 :=
  sha256With_length F _

theorem SepWPp.fold_cell64_320 {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {b : BitVec 8} {P Fr : SepProp} {Q Qp : State → SepProp → Prop}
    (hframe : SepFrame (((sp0 - 320#64) ↦ₛ [b]) ∗ memRegion (sp0 - 319#64) 7) P Fr)
    (hnext : ∀ u0 : BitVec 64, SepWPp prog ret s (((sp0 - 320#64) ↦₆₄ u0) ∗ Fr) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h1 := pointsToBytes1_seven_entails_cell64 (sp0 - 320#64) b
  rw [bv_sub_add_lit sp0 320 1] at h1
  change ((sp0 - 320#64) ↦ₛ [b]) ∗ memRegion (sp0 - 319#64) 7 ⊢
    ∃∗ u0 : BitVec 64, (sp0 - 320#64) ↦₆₄ u0 at h1
  refine SepWPp.fold h1 hframe.eq ?_
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim hnext

theorem SepWPp.panic_cmk {prog : Program} {ret panic_pc : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {x : ConsumeMessageKeyGhost}
    {s0 s : State} {P R_unused R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (hpan : (x.model F).1 = .error .panic)
    (htr : s0.trace <+: s.trace) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (R_unused ∗ R)) →
        (sf.mem ⊨ (⌜((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun (hpc ▸ hext) fun hmf => ?_
  refine allowPanic_unused ⟨Or.inl hpan, ?_⟩ hmf
  simpa [Rust.panicked] using htr

/-! ## Relocatable `[LibsignalPlacement]` Panic Paths (Block 24) -/

theorem epiloguePanic_placed_ok' [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    EpiloguePanicPlacedSpec F A H := by
  intro hexp hovf hfind hhmac x Gc stc ckc R s0 s hidx hcond hpan hstate
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _, hmem⟩ := hstate
  rw [cmkLoopHeap_placed_eq_at] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeapAt_decompose_panicPaths hmem
  have hpan_ovf : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkPanicAddOverflowSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hovf
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hexp
  have hpc' : s.pc = (blkPl_24).base + 1244#64 := hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsedAt
  apply sepWPp_seq_lscl hcl (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 2#8]
  refine SepWPp.call_hmac_placed ((blkPl_24).base + bv% (1276)) (s0.sp - 224#64) x.ckA (keyToBytes32 ckc.key)
    (s0.sp - 320#64) [2#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length ckc.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hcl2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : s1.readReg64 .x28 = BitVec.zeroExtend 64 ckc.index := by
    simpa [CalleeSavedPreserved, hx28, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1
  by_cases hc : x.counter = BitVec.allOnes 32
  · have hckc_max : ckc.index = 0xffffffff#32 := hidx.trans hc
    rw [hckc_max] at hx28_1
    apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkPanicAddOverflowSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) hpan_ovf hpan
      (by simp [htr1, htrace, arm64_norm])
  · have hnone : stc.findReceiverChainIndex x.their = none := hcond.resolve_left hc
    have hz2 : (x.counter + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hc; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := x.counter.isLt
      rw [BitVec.toNat_add] at h1
      change (x.counter.toNat + 1) % 4294967296 = 0 at h1
      change x.counter.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 ckc.key) [2#8])
    rw [hw32 (s0.sp - 224#64)]
    refine SepWPp.fold_cell64_320 (by wp_sep_access) fun u0 => ?_
    apply sepWPp_seq_lscl hcl2 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro hcl3
    refine SepWPp.call_findIndex_none_placed ((blkPl_24).base + bv% (1312)) Gc.chainsPtr x.theirA (s0.sp - 480#64)
      Gc stc x.their hfind
      (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
      (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
      hcl3 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hcl4 _ hx0_2
    apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) hpan_exp hpan
      (by simp [htr2, htr1, htrace, arm64_norm])

theorem loopNoChainPanic_placed_ok' [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedSpec F A H := by
  intro hA hfind hhmac x R s0 s _ hnone hpan hstate
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hloop_x19, hmem⟩ := hstate
  have hx19 : s.readReg64 .x19 = 1#64 := hloop_x19 rfl
  rw [cmkLoopHeap_placed_eq_at] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeapAt_decompose_panicPaths hmem
  have halloc' : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem hA.1
  have hshim' : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have hpan_oom : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkHandleErrorSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.1
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.2.1
  have hpc' : s.pc = (blkPl_24).base + 820#64 := hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsedAt
  apply sepWPp_seq_lscl hcl (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 1#8]
  refine SepWPp.call_hmac_placed ((blkPl_24).base + bv% (848)) (s0.sp - 224#64) x.ckA (keyToBytes32 x.ck.key)
    (s0.sp - 320#64) [1#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length x.ck.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hcl2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
  intro hcl3
  refine SepWPp.call_shim_placed ((blkPl_24).base + bv% (852)) (s0.sp - 480#64) hshim'
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
    hcl3 (by simp [arm64_norm]) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hcl4 hcs2
  have hx23_2 : s2.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_1, arm64_norm] using hcs2.2.2.2.2.1
  have hx26_2 : s2.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.1
  have hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkRustAllocSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
  intro hcl5
  refine SepWPp.call_alloc_32_placed ((blkPl_24).base + bv% (864)) (s0.sp - 480#64) halloc'
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simp [hsp2, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp2_align)
    hcl5 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by wp_sep_access) ?_ ?_
  · intro s3 hpc3 hrun3 hsp3 hsp3_align htr3 hcl6 _ hx0_3
    apply sepWPp_seq_lscl hcl6 (mid := lsρ cmkHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun3, arm64_norm]) hpan_oom hpan
      (by simp [htr3, htr2, htr1, htrace, arm64_norm])
  · intro s3 a0 a1 a2 a3 hpc3 hrun3 hsp3 hsp3_align htr3 hcl6 hcs3 hx0_3
    have hx23_3 : s3.readReg64 .x23 = x.self := by
      simpa [CalleeSavedPreserved, hx23_2, arm64_norm] using hcs3.2.2.2.2.1
    have hx26_3 : s3.readReg64 .x26 = x.theirA := by
      simpa [CalleeSavedPreserved, hx26_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.1
    have hx27_3 : s3.readReg64 .x27 = s0.sp - 224#64 := by
      simpa [CalleeSavedPreserved, hx27_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.2.1
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 x.ck.key) [1#8])
    rw [hw32 (s0.sp - 224#64)]
    apply sepWPp_seq_lscl hcl6 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro hcl7
    refine SepWPp.call_findIndex_none_placed ((blkPl_24).base + bv% (900)) x.G.chainsPtr x.theirA (s0.sp - 480#64)
      x.G x.st x.their hfind
      (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
      (by simp [hsp3, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp3_align)
      hcl7 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s4 hpc4 hrun4 hsp4 hsp4_align htr4 hcl8 _ hx0_4
    apply sepWPp_seq_lscl hcl8 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) hpan_exp hpan
      (by simp [htr4, htr3, htr2, htr1, htrace, arm64_norm])

end CryptoVerification.LibsignalSession.PanicPaths
