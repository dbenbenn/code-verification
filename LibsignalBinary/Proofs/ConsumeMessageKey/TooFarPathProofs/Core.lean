/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.LibsignalSession.TooFarPath

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem reaches_outcome_of_sepWPp_post {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {R : SepProp} {s0 s : State} {P Drop : SepProp} {Post : State → SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hpost_imp : ∀ sf, Post sf ⊢ spec.post x s0 sf)
    (hwp : SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (Drop ∗ Post sf) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s :=
  Arm64.ReachesOutcome.reaches_outcome_of_sepWPp_post hm hpost_imp hwp

theorem cs_maxForwardJumps_eq_false {mfj : Nat} {d : BitVec 32} (h : mfj < d.toNat) :
    (d.zeroExtend 64).ule (BitVec.ofNat 64 mfj) = false := by
  have hd : d.toNat < 2 ^ 32 := d.isLt
  have h1 : (BitVec.ofNat 64 mfj).toNat = mfj := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (d.zeroExtend 64).toNat = d.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, h1, h2]
  omega

theorem chainKeyBytes_length (ck : ChainKey) : (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

theorem chainKeyBytes_entails_memRegion (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) ⊢ memRegion a 36 := by
  have h := pointsToBytes_entails_memRegion a (chainKeyBytes ck)
  rwa [chainKeyBytes_length] at h

theorem allocFailedIn_of_eq {F : ShaState → List (BitVec 8) → ShaState} {x : ConsumeMessageKeyGhost}
    {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    ((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace := by
  refine ⟨Or.inr ?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

@[expose] def ratchetRest (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) : SepProp :=
  ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
    st.maxForwardJumps < 2 ^ 64⌝ ∗
  vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

theorem ratchetAt_split_mfj (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A self G st =
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗ ratchetRest A self G st := by
  unfold ratchetAt ratchetRest
  ac_rfl

theorem ratchetAt_mfj_intro (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    (((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗ ratchetRest A self G st) ⊢
    ratchetAt A self G st := by
  rw [← ratchetAt_split_mfj]
  exact Entails.refl _

theorem resultAt_tooFar_words_intro (A : RustAlloc) (r p : BitVec 64) (t : MessageType) (hp : p ≠ 0) :
    (A.live p 36 1 ∗
     (p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
     ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
     ((p + 32#64) ↦₃₂ 0x65727574#32) ∗
     (r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
     ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
     ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) ⊢
    consumeMessageKeyResultAt A r (.error (.invalidMessage t .tooFarInFuture)) := by
  have h1 := pointsToBytes_tooFarInFutureStr p
  have h2 := resultAt_tooFar_intro A r p t hp
  refine Entails.trans ?_ h2
  rw [h1]
  have heq :
      (A.live p 36 1 ∗
       ((p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
        ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
        ((p + 32#64) ↦₃₂ 0x65727574#32)) ∗
       (r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
       ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
       ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) =
      ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
       ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
       A.live p 36 1 ∗
       ((p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
        ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
        ((p + 32#64) ↦₃₂ 0x65727574#32)) ∗
       ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) := by ac_rfl
  rw [← heq]
  exact Entails.of_eq (by ac_rfl)

@[expose] def tooFarPathPost [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  ratchetAt A x.self x.G x.st ∗
  consumeMessageKeyResultAt A x.ret (.error (.invalidMessage x.msgType .tooFarInFuture)) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ckA 36 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt s0.sp cmkStack ∗
  A.pool

@[expose] def tooFarPathPostRaw [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost) (s0 : State) (p : BitVec 64)
    (sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  (((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 x.st.maxForwardJumps) ∗ ratchetRest A x.self x.G x.st) ∗
  (A.live p 36 1 ∗
   (p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
   ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
   ((p + 32#64) ↦₃₂ 0x65727574#32) ∗
   (x.ret ↦₃₂ 2#32) ∗ memRegion (x.ret + 4#64) 4 ∗
   ((x.ret + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
   ((x.ret + 16#64) ↦₆₄ 36#64) ∗ ((x.ret + 24#64) ↦₆₄ p) ∗ ((x.ret + 32#64) ↦₆₄ 36#64) ∗
   ((x.ret + 40#64) ↦₈ msgTypeByte x.msgType) ∗ memRegion (x.ret + 41#64) 47) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  (memRegion (s0.sp - 8192#64) 3616 ∗
   stackAt (s0.sp - 480#64) allocHookStack ∗
   memRegion (s0.sp - 480#64) 152 ∗
   ((s0.sp - 328#64) ↦₆₄ (x.counter - x.ck.index).zeroExtend 64) ∗
   memRegion (s0.sp - 320#64) 224 ∗
   cmkSavedRegs s0.sp s0) ∗
  A.pool

theorem tooFarPathPostRaw_entails_tooFarPathPost [LibsignalPlacement] (A : RustAlloc) (img : Unit) (x : ConsumeMessageKeyGhost)
    (s0 : State) (p : BitVec 64) (hp : p ≠ 0) (sf : State) :
    tooFarPathPostRaw A img x s0 p sf ⊢ tooFarPathPost A img x s0 sf := by
  unfold tooFarPathPostRaw tooFarPathPost
  apply sepConj_mono_right
  refine sepConj_mono (ratchetAt_mfj_intro A x.self x.G x.st) ?_
  refine sepConj_mono (resultAt_tooFar_words_intro A x.ret p x.msgType hp) ?_
  apply sepConj_mono_right
  refine sepConj_mono (chainKeyBytes_entails_memRegion x.ckA x.ck) ?_
  apply sepConj_mono_right
  refine sepConj_mono (stackAt_cmkStack_reassemble s0.sp s0 ((x.counter - x.ck.index).zeroExtend 64))
    (Entails.refl _)

@[expose] def tooFarPathPostAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  ratchetAt A x.self x.G x.st ∗
  consumeMessageKeyResultAt A x.ret (.error (.invalidMessage x.msgType .tooFarInFuture)) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ckA 36 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt s0.sp cmkStack ∗
  A.pool

@[expose] def tooFarPathPostRawAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (s0 : State)
    (p : BitVec 64) (sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗
  (((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 x.st.maxForwardJumps) ∗ ratchetRest A x.self x.G x.st) ∗
  (A.live p 36 1 ∗
   (p ↦₆₄ 0x206567617373656d#64) ∗ ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
   ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗ ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
   ((p + 32#64) ↦₃₂ 0x65727574#32) ∗
   (x.ret ↦₃₂ 2#32) ∗ memRegion (x.ret + 4#64) 4 ∗
   ((x.ret + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
   ((x.ret + 16#64) ↦₆₄ 36#64) ∗ ((x.ret + 24#64) ↦₆₄ p) ∗ ((x.ret + 32#64) ↦₆₄ 36#64) ∗
   ((x.ret + 40#64) ↦₈ msgTypeByte x.msgType) ∗ memRegion (x.ret + 41#64) 47) ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  (logAddr ↦₆₄ 0#64) ∗
  (memRegion (s0.sp - 8192#64) 3616 ∗
   stackAt (s0.sp - 480#64) allocHookStack ∗
   memRegion (s0.sp - 480#64) 152 ∗
   ((s0.sp - 328#64) ↦₆₄ (x.counter - x.ck.index).zeroExtend 64) ∗
   memRegion (s0.sp - 320#64) 224 ∗
   cmkSavedRegs s0.sp s0) ∗
  A.pool

theorem tooFarPathPostRawAt_entails_tooFarPathPostAt (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (s0 : State) (p : BitVec 64) (hp : p ≠ 0) (sf : State) :
    tooFarPathPostRawAt A logAddr x s0 p sf ⊢ tooFarPathPostAt A logAddr x s0 sf := by
  unfold tooFarPathPostRawAt tooFarPathPostAt
  apply sepConj_mono_right
  refine sepConj_mono (ratchetAt_mfj_intro A x.self x.G x.st) ?_
  refine sepConj_mono (resultAt_tooFar_words_intro A x.ret p x.msgType hp) ?_
  apply sepConj_mono_right
  refine sepConj_mono (chainKeyBytes_entails_memRegion x.ckA x.ck) ?_
  apply sepConj_mono_right
  refine sepConj_mono (stackAt_cmkStack_reassemble s0.sp s0 ((x.counter - x.ck.index).zeroExtend 64))
    (Entails.refl _)

theorem SepWP.conseq_tooFarPathPost {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R D1 D2 D3 D4 D5 : SepProp} {Post₁ Post₂ : State → SepProp} {rest : State → Prop}
    (himp : ∀ sf, Post₁ sf ⊢ Post₂ sf)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ D1 ∗ D2 ∗ D3 ∗ D4 ∗ D5 ∗ Post₁ sf ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ D1 ∗ D2 ∗ D3 ∗ D4 ∗ D5 ∗ Post₂ sf ∗ R) ∧ rest sf) :=
  SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (himp sf))))))) (h1 hm), h2⟩

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block 24) -/

attribute [local irreducible] cmkDummyImg
attribute [-simp, -arm64_norm, -wp_norm] logFilterAddr_cmkDummyImg

theorem tooFarPathPostAt_entails_cmkPlacedSpec [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {x : ConsumeMessageKeyGhost}
    (hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture))
    (hm2 : (x.model F).2 = x.st)
    (htouch : x.touched F = none)
    (s0 sf : State) :
    tooFarPathPostAt A lsLogFilterAddr x s0 sf ⊢ (cmkPlacedSpec F A).post x s0 sf := by
  unfold tooFarPathPostAt cmkPlacedSpec withLsCodeLoaded
  dsimp only
  rw [hm1, hm2, htouch]
  apply Entails.pure_left
  intro htr
  apply Entails.pure_right ⟨by nofun, htr⟩
  apply sepConj_mono_left
  refine Entails.trans ?_ (Entails.sepExists_intro x.G)
  exact Entails.pure_right (RatchetGhost.AgreeExcept.refl x.G none) (Entails.refl _)

theorem tooFarPathPost_entails_cmkPlacedSpec [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {x : ConsumeMessageKeyGhost}
    (hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture))
    (hm2 : (x.model F).2 = x.st)
    (htouch : x.touched F = none)
    (s0 sf : State) :
    tooFarPathPost A cmkDummyImg x s0 sf ⊢ (cmkPlacedSpec F A).post x s0 sf := by
  simpa only [tooFarPathPost, tooFarPathPostAt, logFilterAddr_cmkDummyImg] using
    tooFarPathPostAt_entails_cmkPlacedSpec hm1 hm2 htouch s0 sf

theorem tooFarPath_placed_ok' [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    TooFarPathPlacedSpec F A H := by
  intro hA x R s0 s hle hjump hstate
  rcases hA with ⟨halloc_sat, _, hshim_sat, hhandle_err, _, _⟩
  rcases hstate with
    ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
     ⟨hx2, hx4, hx9, hx20, hx22, hx23, hx26, hx27, hx28⟩, hmem⟩
  have hmodel : x.model F = (.error (.invalidMessage x.msgType .tooFarInFuture), x.st) :=
    consumeMessageKey_tooFar F x.st x.their x.ck x.counter x.msgType hle hjump
  have hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture) := by rw [hmodel]
  have hm2 : (x.model F).2 = x.st := by rw [hmodel]
  have htouch : x.touched F = none := by unfold ConsumeMessageKeyGhost.touched; rw [hm1]
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem halloc_sat
  have hpanic : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkHandleErrorSym) = some Rust.panicked :=
    (cmk_externAt?_of_mem).trans hhandle_err
  have hpc' : s.pc = (blkPl_24).base + 368#64 := hpc
  clear hpc
  have hpc := hpc'
  clear hpc'
  have hmem_ro : s.mem ⊨ ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ cmkPreLoopHeap_placed A x s0) ∗ R := by
    have heq : cmkPreLoopHeap_placed A x s0 ∗ ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) =
        ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ cmkPreLoopHeap_placed A x s0) ∗ R := by ac_rfl
    rwa [← heq]
  clear hmem
  refine reaches_outcome_of_sepWPp_post
    (Drop := (lsρ cmkTooFarStrSym ↦₆₄ᵣ 0x206567617373656d#64) ∗
      ((lsρ cmkTooFarStrSym + 8#64) ↦₆₄ᵣ 0x6f6f74206d6f7266#64) ∗
      ((lsρ cmkTooFarStrSym + 16#64) ↦₆₄ᵣ 0x746e692072616620#64) ∗
      ((lsρ cmkTooFarStrSym + 24#64) ↦₆₄ᵣ 0x756620656874206f#64) ∗
      ((lsρ cmkTooFarStrSym + 32#64) ↦₃₂ᵣ 0x65727574#32))
    (Post := tooFarPathPostAt A lsLogFilterAddr x s0)
    hmem_ro (tooFarPathPostAt_entails_cmkPlacedSpec hm1 hm2 htouch s0) ?_
  clear halloc_sat hshim_sat hhandle_err hmodel hm1 hm2 htouch hcl hmem_ro
  unfold cmkPreLoopHeap_placed cmkSavedRegs
  rw [pointsToBytesRO_tooFarInFutureStr (lsρ cmkTooFarStrSym),
      ratchetAt_split_mfj A x.self x.G x.st,
      memRegion_88_ret_split x.ret,
      stackAt_7712_split s0.sp,
      memRegion_384_tooFarPath_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r40 => SepWPp.exists_elim fun r32 =>
    SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r16 =>
    SepWPp.exists_elim fun r8 => SepWPp.exists_elim fun r0 =>
    SepWPp.exists_elim fun v9 => ?_
  have hcs := cs_maxForwardJumps_eq_false hjump
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  apply SepWPp.of_sepWP (mid := (blkPl_24).base + bv% (556))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  rw [sepConj_left_comm (stackAt sf.sp allocHookStack), sepConj_left_comm A.pool]
  by_cases hoom : sf_1.readReg64 .x0 = 0#64
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := lsρ cmkHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [cmkPlacedSpec, withLsCodeLoaded, sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom' : sf_1.readReg64 .x0 ≠ 0 := hoom
    have hcbz_oom : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [hoom', ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrace_ok⟩ => ?_
    rw [memRegion_36_split (sf_1.readReg64 .x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p4 => SepWPp.exists_elim fun p3 =>
      SepWPp.exists_elim fun p2 => SepWPp.exists_elim fun p1 =>
      SepWPp.exists_elim fun p0 => ?_
    apply SepWPp.of_sepWP_ret
    apply SepWP.conseq_tooFarPathPost (tooFarPathPostRawAt_entails_tooFarPathPostAt A lsLogFilterAddr x s0 (sf_1.readReg64 .x0) hoom')
    unfold tooFarPathPostRawAt cmkSavedRegs
    wp_steps
    rw [h_1, hsp]
    wp_done

end CryptoVerification.LibsignalSession.TooFarPath
