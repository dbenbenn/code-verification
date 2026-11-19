/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGc
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAdd
import LibsignalBinary.Proofs.CodeLayout

/-!
# `ChainEpochDirection.keyAdvanceLoop` Proofs for `<spqr::chain::Chain>::recv_key`

Proves the forward-ratchet `keyAdvanceLoop` (`+448`, `0x60a90`) and its entry block (`+360`,
`0x60a38`) for `<spqr::chain::Chain>::recv_key` (Block `366`) in fixed-image and relocatable
`[LibsignalPlacement]` forms.
-/

public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open AgreeStateSimp NextKeyInternalFacts ChainNewFacts ChainAddEpochFacts ChainSendKeyFacts
open CryptoVerification.CodeLayout


set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

/-! ## `keyAdvanceLoop` at `+448` (`0x60a90`) and Entry at `+360` (`0x60a38`) -/

set_option maxHeartbeats 800000 in
theorem recvKey_advance_loop_step_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0)
    (rem : Nat) (recv : ChainEpochDirection) (prevPin : VecPin)
    (hrem : x.index.toNat - recv.ctr.toNat ≤ rem)
    (hgt : recv.ctr.toNat < x.index.toNat)
    (hn_le : recv.next.length ≤ gce.recv.next.cap.toNat)
    (hp_le : recv.prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hp_fit : recv.prev.data.length + 36 * (x.index.toNat - recv.ctr.toNat) + 128 < 2 ^ 62)
    (h_ih : ∀ (recv' : ChainEpochDirection) (prevPin' : VecPin),
      x.index.toNat - recv'.ctr.toNat < rem →
      recv'.ctr.toNat < x.index.toNat →
      recv'.next.length ≤ gce.recv.next.cap.toNat →
      recv'.prev.data.length ≤ prevPin'.cap.toNat →
      prevPin'.cap.toNat < 2 ^ 63 → prevPin'.ptr ≠ 0 →
      recv'.prev.data.length + 36 * (x.index.toNat - recv'.ctr.toNat) + 128 < 2 ^ 62 →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv' x.index x.self.params
        let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
        let self2 := { self1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
        let recv_f := { self2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s' : State),
        RecvKeyPlacedStateInv lsmpl s0 s' →
        s'.pc = (blkPl_366).base + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = recv'.ctr →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv'.next.length) ∗
            (gce.recv.next.ptr ↦ₛ recv'.next) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv'.next.length ∗
            ((epPtr + 0x50#64) ↦₆₄ prevPin'.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ prevPin'.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv'.prev.data.length) ∗
            (prevPin'.ptr ↦ₛ recv'.prev.data) ∗
            vecU8Rest A prevPin'.cap prevPin'.ptr recv'.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv x.index x.self.params
      let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
      let self2 := { self1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
      let recv_f := { self2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 448#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = recv.ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv.next.length) ∗
        (gce.recv.next.ptr ↦ₛ recv.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (prevPin.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have h_gc616 := @recvKey_gc_from_616_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc
    hoom_ext hslice_ext hpanic_ext x s0 c3 R epochIndex hi_ep gce prevPin recv
    hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr
  have h_add496 := @recvKey_add_from_496_placed _ hkdf A H hdoRes x s0 c3 R epochIndex hi_ep gce prevPin
  clear hshim halloc hdoRes hoom_ext hslice_ext hpanic_ext
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨hctr_ne, _, _, _, hctr1_toNat, hule_idx, hult_idx⟩ := advance_hdr_props hgt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hule_idx; wp_norm_hyp hult_idx
  by_cases hlt1 : recv.ctr.toNat + 1 < x.index.toNat
  · have hlt1_t : decide (recv.ctr.toNat + 1 < x.index.toNat) = true := decide_eq_true hlt1
    wp_norm_hyp hlt1_t
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 362) hF ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
    by_cases hbad : recv.next.length ≠ 32
    · obtain ⟨p, hp_err⟩ := nextKeyInternal_isError_of_bad hkdf (Or.inl hbad)
      have hpan_eq : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyAdvanceLoop_step_err hkdf recv x.index x.self.params p hlt1 hp_err]; rfl
      have hlen_lt64 : recv.next.length < 2 ^ 64 := by omega
      change subroutine_ok _ _ (withLsCallInv lsmpl nextKeyInternalPanicSpecX) at hnextKeyPanic
      wpp_call_nextKeyPanic_recv_placed hnextKeyPanic
        (⟨s0.sp - 120#64, gce.recv.next.ptr, recv.next, epPtr + 0x68#64, recv.ctr⟩ : NextKeyInternalGhost)
        hinv1 hpan_eq
    · have hlen32 : recv.next.length = 32 := by omega
      have hlen32_bv : BitVec.ofNat 64 recv.next.length = 32#64 := by rw [hlen32]
      wp_norm_hyp hlen32_bv
      change subroutine_ok _ _ (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)) at hnextKey
      wpp_call_nextKey_recv_placed hnextKey
        (⟨s0.sp - 120#64, gce.recv.next.ptr, recv.next, epPtr + 0x68#64, recv.ctr⟩ : NextKeyInternalGhost)
        hinv1
      let next1 := nextKeyNext hkdf recv.next recv.ctr
      let ctr1 := recv.ctr + 1#32
      let key := nextKeyOut hkdf recv.next recv.ctr
      have hgt1 : ctr1.toNat < x.index.toNat := by dsimp [ctr1]; omega
      have ⟨_, hovf1, hbeq0, hbne0, _, _, _⟩ := advance_hdr_props hgt1
      have ⟨hovf_ooo, hult_ooo1, hult_ooo2, hult_ooo_idx, hule_ooo_idx⟩ :=
        advance_ooo_props ctr1 x.index x.self.params
      have hsp_sf : sf.sp = s0.sp - 128#64 := by rw [‹sf.sp = s.sp›, hsp]
      have hsp_sf_align : sf.spAligned = true := by
        simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
      have hstack_s : stackAt s.sp nextKeyInternalStackX = stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
        rw [hsp]
      refine SepWPp.fold (Entails.of_eq hstack_s) (by sep_focus) ?_
      refine SepWPp.fold (recvKey_nextKeyOutAt_dup_len (s0.sp - 120#64) ctr1 key) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hkey_len => ?_
      unfold nextKeyOutAt
      refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
      have hnext1_len : next1.length = 32 := recvKey_nextKeyNext_length_of_nextKeyOut_length hkey_len
      wp_norm_hyp hsp_sf; wp_norm_hyp hsp_sf_align
      dsimp only [ctr1] at hovf1 hbeq0 hbne0 hovf_ooo hult_ooo1 hult_ooo2 hult_ooo_idx hule_ooo_idx
      wp_norm_hyp hovf1; wp_norm_hyp hbeq0; wp_norm_hyp hbne0
      wp_norm_hyp hovf_ooo; wp_norm_hyp hult_ooo1; wp_norm_hyp hult_ooo2
      wp_norm_hyp hult_ooo_idx; wp_norm_hyp hule_ooo_idx
      have hok_nk := nextKeyInternal_eq_ok hkdf hlen32 hctr_ne
      by_cases hovf : ctr1.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
      · have hovf_t : decide (ctr1.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = true :=
          decide_eq_true hovf
        dsimp only [ctr1] at hovf_t
        rw [hctr1_toNat] at hovf_t
        wp_norm_hyp hovf_t
        apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hadd_ext) fun hm => ?_
        have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
          rw [hres, keyAdvanceLoop_step_overflow hkdf recv x.index x.self.params next1 ctr1 (ctr1, key) hlt1 hok_nk hovf]
          rfl
        exact allowPanic_recvKey_panic (A := A) hpan (by simp only [Rust.panicked, arm64_norm, htr_sf, htrace]) hm
      · have hovf_f : decide (ctr1.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = false :=
          decide_eq_false hovf
        dsimp only [ctr1] at hovf_f
        rw [hctr1_toNat] at hovf_f
        wp_norm_hyp hovf_f
        by_cases hkeep : ctr1 + x.self.params.maxOooKeysOrDefault ≥ x.index
        · have hkeep_t : decide (ctr1 + x.self.params.maxOooKeysOrDefault ≥ x.index) = true :=
            decide_eq_true hkeep
          dsimp only [ctr1] at hkeep_t
          wp_norm_hyp hkeep_t
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 496#64) hF_sf ?_
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF2
          have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
            ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
             by rw [← hx26, ← h_7]; wp_norm_goal,
             by rw [← hx27, ← h_8]; wp_norm_goal,
             by wp_norm_goal,
             by simp only [arm64_norm, htr_sf, htrace],
             by wp_norm_goal⟩
          have hp_fit0 : recv.prev.data.length + 128 < 2 ^ 62 := by omega
          refine SepWPp.mono_pre _ ?_
            (h_add496 recv.prev next1 key ctr1 hgt1 hkey_len hp_fit0 hp_le hp_cap hp_ptr
              (fun cap2 ptr2 hle2 hcap2 hptr2 s' hinv' hpc' hw8' hx19' hw20' hx21' hx22' hw23' hx24' => ?_)
              _ hinv2 (by wp_norm_goal) (by rw [← hx19, ← h]; wp_norm_goal)
              (by rw [← hw20, ← h_1]; wp_norm_goal) (by rw [← hx21, ← h_2]; wp_norm_goal)
              (by rw [← hx22, ← h_3]; wp_norm_goal) (by rw [← hw23, ← h_4]; wp_norm_goal)
              (by rw [← hx24, ← h_5]; wp_norm_goal))
          · rw [hlen32, hnext1_len]; sep_frame
          · let recv' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := recv.prev.add (ctr1, key) x.self.params }
            have hrem' : x.index.toNat - recv'.ctr.toNat < rem := by dsimp [recv', ctr1]; omega
            have hn_le' : recv'.next.length ≤ gce.recv.next.cap.toNat := by dsimp [recv']; omega
            have hprev'_len : recv'.prev.data.length = recv.prev.data.length + 36 := by
              dsimp [recv', KeyHistory.add]
              rw [List.length_append, List.length_append, NextKeyInternalFacts.toBEBytes_4_length, hkey_len]
            have hp_fit' : recv'.prev.data.length + 36 * (x.index.toNat - recv'.ctr.toNat) + 128 < 2 ^ 62 := by
              rw [hprev'_len]; dsimp [recv', ctr1]
              have hmul : 36 * (x.index.toNat - (recv.ctr.toNat + 1)) + 36 = 36 * (x.index.toNat - recv.ctr.toNat) := by
                have : x.index.toNat - recv.ctr.toNat = (x.index.toNat - (recv.ctr.toNat + 1)) + 1 := by omega
                rw [this, Nat.mul_add]
              omega
            have hres' : Chain.recvKey hkdf x.self x.epoch x.index = (do
                let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv' x.index x.self.params
                let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
                let self2 := { self1 with prev := prevGc }
                let (next', ctr', (_, outKey)) ←
                  ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
                let recv_f := { self2 with next := next', ctr := ctr' }
                let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
                return ({ x.self with links := links' }, outKey)) := by
              rw [hres, keyAdvanceLoop_step_ok hkdf recv x.index x.self.params next1 ctr1 (ctr1, key) hlt1 hok_nk hovf]
              simp only [hkeep, ↓reduceIte]; rfl
            exact h_ih recv' ⟨cap2, ptr2⟩ hrem' hgt1 hn_le' hle2 hcap2 hptr2 hp_fit' hres'
              s' hinv' hpc' hw8' hx19' hw20' hx21' hx22' hw23' hx24'
        · have hkeep_f : decide (ctr1 + x.self.params.maxOooKeysOrDefault ≥ x.index) = false :=
            decide_eq_false hkeep
          dsimp only [ctr1] at hkeep_f
          wp_norm_hyp hkeep_f
          obtain ⟨k0, k1, k2, k3, hkey_pack⟩ := exists_cells4_of_length_32 hkey_len
          have hkey_sp : ((s0.sp - 116#64) ↦ₛ key) =
              ((s0.sp - 116#64) ↦₆₄ k0) ∗ ((s0.sp - 108#64) ↦₆₄ k1) ∗
              ((s0.sp - 100#64) ↦₆₄ k2) ∗ ((s0.sp - 92#64) ↦₆₄ k3) := by
            have h := hkey_pack (s0.sp - 116#64)
            rw [show s0.sp - 116#64 + 8#64 = s0.sp - 108#64 by bv_kernel,
                show s0.sp - 116#64 + 16#64 = s0.sp - 100#64 by bv_kernel,
                show s0.sp - 116#64 + 24#64 = s0.sp - 92#64 by bv_kernel] at h
            exact h
          refine SepWPp.fold (Entails.of_eq hkey_sp) (by sep_focus) ?_
          refine SepWPp.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr1 k0 k1 k2 k3) (by sep_focus) ?_
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 448#64) hF_sf ?_
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF2
          have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
            ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
             by rw [← hx26, ← h_7]; wp_norm_goal,
             by rw [← hx27, ← h_8]; wp_norm_goal,
             by wp_norm_goal,
             by simp only [arm64_norm, htr_sf, htrace],
             by wp_norm_goal⟩
          let recv' : ChainEpochDirection := { ctr := ctr1, next := next1, prev := recv.prev }
          have hrem' : x.index.toNat - recv'.ctr.toNat < rem := by dsimp [recv', ctr1]; omega
          have hn_le' : recv'.next.length ≤ gce.recv.next.cap.toNat := by dsimp [recv']; omega
          have hp_fit' : recv'.prev.data.length + 36 * (x.index.toNat - recv'.ctr.toNat) + 128 < 2 ^ 62 := by
            dsimp [recv', ctr1]
            have : 36 * (x.index.toNat - (recv.ctr.toNat + 1)) ≤ 36 * (x.index.toNat - recv.ctr.toNat) :=
              Nat.mul_le_mul_left 36 (by omega)
            omega
          have hres' : Chain.recvKey hkdf x.self x.epoch x.index = (do
              let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv' x.index x.self.params
              let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
              let self2 := { self1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
              let recv_f := { self2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
              return ({ x.self with links := links' }, outKey)) := by
            rw [hres, keyAdvanceLoop_step_ok hkdf recv x.index x.self.params next1 ctr1 (ctr1, key) hlt1 hok_nk hovf]
            simp only [hkeep, ↓reduceIte]; rfl
          refine SepWPp.mono_pre _ ?_
            (h_ih recv' prevPin hrem' hgt1 hn_le' hp_le hp_cap hp_ptr hp_fit' hres'
              _ hinv2 (by wp_norm_goal) (by dsimp [recv', ctr1]; wp_norm_goal)
              (by rw [← hx19, ← h]; wp_norm_goal) (by rw [← hw20, ← h_1]; wp_norm_goal)
              (by rw [← hx21, ← h_2]; wp_norm_goal) (by rw [← hx22, ← h_3]; wp_norm_goal)
              (by rw [← hw23, ← h_4]; wp_norm_goal) (by rw [← hx24, ← h_5]; wp_norm_goal))
          dsimp only [recv']
          rw [hlen32, hnext1_len]; sep_frame
  · have hlt1_f : decide (recv.ctr.toNat + 1 < x.index.toNat) = false := decide_eq_false hlt1
    wp_norm_hyp hlt1_f
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 616#64) hF ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres_gc : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (recv.prev.gc recv.ctr x.self.params)
        let self2 := { recv with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
        let recv_f := { self2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
        return ({ x.self with links := links' }, outKey)) := by
      rw [hres, keyAdvanceLoop_done hkdf recv x.index x.self.params hlt1 hctr_ne]
      rfl
    refine SepWPp.mono_pre _ ?_
      (h_gc616 hres_gc _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

theorem recvKey_advance_loop_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) :
    ∀ (rem : Nat) (recv : ChainEpochDirection) (prevPin : VecPin),
      x.index.toNat - recv.ctr.toNat ≤ rem →
      recv.ctr.toNat < x.index.toNat →
      recv.next.length ≤ gce.recv.next.cap.toNat →
      recv.prev.data.length ≤ prevPin.cap.toNat →
      prevPin.cap.toNat < 2 ^ 63 → prevPin.ptr ≠ 0 →
      recv.prev.data.length + 36 * (x.index.toNat - recv.ctr.toNat) + 128 < 2 ^ 62 →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv x.index x.self.params
        let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
        let self2 := { self1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
        let recv_f := { self2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State),
        RecvKeyPlacedStateInv lsmpl s0 s →
        s.pc = (blkPl_366).base + 448#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = recv.ctr →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv.next.length) ∗
            (gce.recv.next.ptr ↦ₛ recv.next) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv.next.length ∗
            ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (prevPin.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A prevPin.cap prevPin.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R) := by
  intro rem
  induction rem with
  | zero =>
    intro recv prevPin hrem hgt
    omega
  | succ rem ih =>
    intro recv prevPin hrem hgt hn_le hp_le hp_cap hp_ptr hp_fit hres
      s hinv hpc hw8 hx19 hw20 hx21 hx22 hw23 hx24
    exact recvKey_advance_loop_step_placed hnextKey hnextKeyPanic hshim halloc hdoRes
      hoom_ext hslice_ext hpanic_ext hadd_ext
      x s0 c3 epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hn_cap hn_ptr
      (rem + 1) recv prevPin hrem hgt hn_le hp_le hp_cap hp_ptr hp_fit
      (fun recv' prevPin' hlt => ih recv' prevPin' (by omega))
      hres s hinv hpc hw8 hx19 hw20 hx21 hx22 hw23 hx24

set_option maxHeartbeats 800000 in
theorem recvKey_advance_from_360_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : (x.self.links[epochIndex]'hi_ep).recv.next.length ≤ gce.recv.next.cap.toNat)
    (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hp_fit0 : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 61)
    (hgt : (x.self.links[epochIndex]'hi_ep).recv.ctr < x.index)
    (hjump : ¬ (x.index - (x.self.links[epochIndex]'hi_ep).recv.ctr > x.self.params.maxJumpOrDefault))
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let (recv', outKey) ← (x.self.links[epochIndex]'hi_ep).recv.key hkdf x.index x.self.params
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 360#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = (x.self.links[epochIndex]'hi_ep).recv.ctr)
    (hw10 : (s.readReg64 (.gpr 10#5)).setWidth 32 = x.self.params.maxOooKeys)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv.next.length) ∗
        (gce.recv.next.ptr ↦ₛ recv.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr recv.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have h_loop := @recvKey_advance_loop_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hdoRes
    hoom_ext hslice_ext hpanic_ext hadd_ext
    x s0 c3 R epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hn_cap hn_ptr
  clear hnextKey hnextKeyPanic hshim halloc hdoRes hoom_ext hslice_ext hpanic_ext
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  let recv := (x.self.links[epochIndex]'hi_ep).recv
  have hgt_nat : recv.ctr.toNat < x.index.toNat := BitVec.lt_def.mp hgt
  have hat_lt := x.index.isLt
  have ⟨_, hovf1, hbeq0, hbne0, _, _, _⟩ := advance_hdr_props hgt_nat
  have hmaxOoo_eq := maxOooKeysOrDefault_eq_ite x.self.params
  have ⟨hovf_ooo, hult_ooo1, hult_ooo2, hult_ooo_idx, hule_ooo_idx⟩ :=
    advance_ooo_props recv.ctr x.index x.self.params
  dsimp only [recv] at hovf1 hbeq0 hbne0 hovf_ooo hult_ooo1 hult_ooo2 hult_ooo_idx hule_ooo_idx
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hw8; wp_norm_hyp hw10; wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hovf1; wp_norm_hyp hbeq0; wp_norm_hyp hbne0
  wp_norm_hyp hmaxOoo_eq; wp_norm_hyp hovf_ooo; wp_norm_hyp hult_ooo1; wp_norm_hyp hult_ooo2
  wp_norm_hyp hult_ooo_idx; wp_norm_hyp hule_ooo_idx
  by_cases hovf : recv.ctr.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
  · have hovf_t : decide (recv.ctr.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = true :=
      decide_eq_true hovf
    dsimp only [recv] at hovf_t
    wp_norm_hyp hovf_t
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hadd_ext) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, ced_key_of_gt_overflow hkdf recv x.index x.self.params hgt hjump hovf]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
  · have hovf_f : decide (recv.ctr.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = false :=
      decide_eq_false hovf
    dsimp only [recv] at hovf_f
    wp_norm_hyp hovf_f
    by_cases hkeep : recv.ctr + x.self.params.maxOooKeysOrDefault ≥ x.index
    · have hkeep_t : decide (recv.ctr + x.self.params.maxOooKeysOrDefault ≥ x.index) = true :=
        decide_eq_true hkeep
      have hgt_ooo : ¬ (x.index > recv.ctr + x.self.params.maxOooKeysOrDefault) := by
        have h1 := BitVec.le_def.mp hkeep
        intro h2; have h3 := BitVec.lt_def.mp h2; omega
      dsimp only [recv] at hkeep_t
      wp_norm_hyp hkeep_t
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 448#64) hF ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
      have hp_fit : recv.prev.data.length + 36 * (x.index.toNat - recv.ctr.toNat) + 128 < 2 ^ 62 := by
        have hidx_lt : x.index.toNat < 2 ^ 32 := x.index.isLt
        dsimp [recv] at *; omega
      have hres_loop : Chain.recvKey hkdf x.self x.epoch x.index = (do
          let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv x.index x.self.params
          let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
          let self2 := { self1 with prev := prevGc }
          let (next', ctr', (_, outKey)) ←
            ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
          let recv_f := { self2 with next := next', ctr := ctr' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
          return ({ x.self with links := links' }, outKey)) := by
        rw [hres, ced_key_of_gt_ok hkdf recv x.index x.self.params hgt hjump hovf]
        simp only [hgt_ooo, ↓reduceIte, bind_assoc, pure_bind]
      refine SepWPp.mono_pre _ ?_
        (h_loop (x.index.toNat - recv.ctr.toNat) recv gce.recv.prev (Nat.le_refl _) hgt_nat
          hn_le hp_le hp_cap hp_ptr hp_fit hres_loop
          _ hinv' (by wp_norm_goal) (by dsimp [recv]; wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
    · have hkeep_f : decide (recv.ctr + x.self.params.maxOooKeysOrDefault ≥ x.index) = false :=
        decide_eq_false hkeep
      have hgt_ooo : x.index > recv.ctr + x.self.params.maxOooKeysOrDefault := by
        apply BitVec.lt_def.mpr
        have h1 : ¬ (x.index.toNat ≤ (recv.ctr + x.self.params.maxOooKeysOrDefault).toNat) :=
          fun hle => hkeep (BitVec.le_def.mpr hle)
        omega
      dsimp only [recv] at hkeep_f
      wp_norm_hyp hkeep_f
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 448#64) hF ?_
      wp_steps
      refine SepWP.fold (vecU8Rest_clear_entails A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data hp_le) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
      let recv0 : ChainEpochDirection := { recv with prev := { data := [] } }
      have hp_fit : recv0.prev.data.length + 36 * (x.index.toNat - recv0.ctr.toNat) + 128 < 2 ^ 62 := by
        have hidx_lt : x.index.toNat < 2 ^ 32 := x.index.isLt
        dsimp [recv0]; omega
      have hres_loop : Chain.recvKey hkdf x.self x.epoch x.index = (do
          let self1 ← ChainEpochDirection.keyAdvanceLoop hkdf recv0 x.index x.self.params
          let prevGc ← ChainResult.ofPanic (self1.prev.gc self1.ctr x.self.params)
          let self2 := { self1 with prev := prevGc }
          let (next', ctr', (_, outKey)) ←
            ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self2.next self2.ctr)
          let recv_f := { self2 with next := next', ctr := ctr' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv_f }
          return ({ x.self with links := links' }, outKey)) := by
        rw [hres, ced_key_of_gt_ok hkdf recv x.index x.self.params hgt hjump hovf]
        dsimp only [recv0, KeyHistory.clear]
        simp only [hgt_ooo, ↓reduceIte, bind_assoc, pure_bind]
      refine SepWPp.mono_pre _ ?_
        (h_loop (x.index.toNat - recv0.ctr.toNat) recv0 gce.recv.prev (Nat.le_refl _) hgt_nat
          hn_le (by dsimp [recv0]; omega) hp_cap hp_ptr hp_fit hres_loop
          _ hinv' (by wp_norm_goal) (by dsimp [recv0, recv]; wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      dsimp only [recv0, recv, List.length_nil, BitVec.ofNat_eq_ofNat]
      sep_frame

end CryptoVerification.SpqrV1.ChainProofs
