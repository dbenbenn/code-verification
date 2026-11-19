/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Return Epilogue (`+0x77c .. +0x798`) and `DuplicatedMessage` Path (`+0x0b4 .. +0x16c`)
-/

public section

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem cmkStack_recombine (sp0 : BitVec 64) (s0 : State) :
    (stackAt (sp0 - 480#64) 7712 ∗ memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0) ⊢
      stackAt sp0 cmkStack := by
  unfold cmkSavedRegs stackAt cmkStack
  sep_interval

theorem memRegion_88_entails_dup_slots (ret : BitVec 64) :
    memRegion ret 88 ⊢
      (∃∗ v0 : BitVec 32, (ret ↦₃₂ v0)) ∗
      memRegion (ret + 4#64) 4 ∗
      (∃∗ v8 : BitVec 64, ((ret + 8#64) ↦₆₄ v8)) ∗
      (∃∗ v16 : BitVec 32, ((ret + 16#64) ↦₃₂ v16)) ∗
      (∃∗ v20 : BitVec 32, ((ret + 20#64) ↦₃₂ v20)) ∗
      memRegion (ret + 24#64) 64 := by
  sep_interval

theorem chainKeyBytes_entails_memRegion (ckA : BitVec 64) (ck : ChainKey) :
    (ckA ↦ₛ chainKeyBytes ck) ⊢ memRegion ckA 36 := by
  have hlen : (chainKeyBytes ck).length = 36 := by simp [chainKeyBytes, keyToBytes32, leBytes]
  sep_interval

theorem sepWP_to_reaches_pc {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP prog target_pc s P post)
    (hm : s.mem ⊨ P ∗ R)
    (hL : prog.CodeLoaded s.mem) :
    ∃ sf, Steps prog s sf ∧ sf.pc = target_pc ∧ sf.status = .Running ∧
      ∃ P_f, sf.mem ⊨ P_f ∗ R ∧ post sf P_f := by
  rcases hwp.elim hm hL with ⟨sf, hsteps, h | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, h⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem cmk_epilogue_77c_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        sf.trace = s0.trace ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ stackAt s0.sp cmkStack)) := by
  rcases htrace with ⟨htrace, hvregs⟩
  unfold cmkSavedRegs
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
  · exact cmkStack_recombine s0.sp s0

theorem cmk_epilogue_77c_placed_outcome [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {A : RustAlloc}
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnpan : (x.model F).1 ≠ .error .panic)
    (hG' : x.G.AgreeExcept G' (x.touched F))
    (hm : s.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗ R)) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hpc_sf, hrun_sf, P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩ :=
    sepWP_to_reaches_pc (cmk_epilogue_77c_placed_wp s0 s hpc hrun hsp hsp_align htrace) hm hL
  refine reaches_outcome_steps hsteps
    (reaches_outcome_refl_return hpc_sf hrun_sf ⟨?_, hsp_sf, hcc_sf⟩)
  have hm1 : sf.mem ⊨ stackAt s0.sp cmkStack ∗
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗ R) :=
    Satisfies.mono (sepConj_mono_left hP_f) hm_sf
  simp only [cmkPlacedSpec, withLsCodeLoaded]
  exact Satisfies.mono (Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_left (Entails.pure_right ⟨hnpan, htrace_sf⟩
      (sepConj_mono_left (Entails.sepExists_right G' (Entails.pure_right hG' (Entails.refl _))))))) hm1

theorem cmk_dup_0xb4_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)} {A : RustAlloc}
    (x : ConsumeMessageKeyGhost) (s0 s : State)
    (v0 v16 v20 : BitVec 32) (v8 : BitVec 64)
    (hpc : s.pc = (blkPl_24).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      ((blkPl_24).base + 1916#64) s
      ((x.ret ↦₃₂ v0) ∗
       memRegion (x.ret + 4#64) 4 ∗
       ((x.ret + 8#64) ↦₆₄ v8) ∗
       ((x.ret + 16#64) ↦₃₂ v16) ∗
       ((x.ret + 20#64) ↦₃₂ v20) ∗
       memRegion (x.ret + 24#64) 64 ∗
       (lsLogFilterAddr ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        (P_f ⊢ consumeMessageKeyResultAt A x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
          (lsLogFilterAddr ↦₆₄ 0#64))) := by
  rcases htrace with ⟨htrace, hvregs⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  simp only [consumeMessageKeyResultAt, errDuplicatedMessage]
  bi_entail

theorem cmk_dup_0xb4_placed_outcome [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {A : RustAlloc}
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64)
    (hmodel : x.model F = (.error (.duplicatedMessage x.ck.index x.counter), x.st))
    (hm : s.mem ⊨ cmkPreLoopHeap_placed A x s0 ∗ R) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s := by
  unfold cmkPreLoopHeap_placed at hm
  have hm_slots : s.mem ⊨
      ∃∗ v0 : BitVec 32, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 32, ∃∗ v20 : BitVec 32,
        ((x.ret ↦₃₂ v0) ∗
         memRegion (x.ret + 4#64) 4 ∗
         ((x.ret + 8#64) ↦₆₄ v8) ∗
         ((x.ret + 16#64) ↦₃₂ v16) ∗
         ((x.ret + 20#64) ↦₃₂ v20) ∗
         memRegion (x.ret + 24#64) 64 ∗
         (lsLogFilterAddr ↦₆₄ 0#64)) ∗
        (ratchetAt A x.self x.G x.st ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         memRegion x.ckA 36 ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool ∗ R) := by
    have hck_len : (chainKeyBytes x.ck).length = 36 := by simp [chainKeyBytes, keyToBytes32, leBytes]
    refine Satisfies.mono (Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (memRegion_88_entails_dup_slots x.ret)))))) ?_) hm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    generalize hrat : ratchetAt A x.self x.G x.st = vRat
    generalize hsr : cmkSavedRegs s0.sp s0 = vSr
    bi_entail
  simp only [satisfies_sepExists] at hm_slots
  rcases hm_slots with ⟨v0, v8, v16, v20, hm_slots⟩
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, htrace1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_dup_0xb4_placed_wp (A := A) x s0 s v0 v16 v20 v8 hpc hrun hsp hsp_align htrace hx20 hx22 hx28)
      hm_slots hL
  have hm1' : s1.mem ⊨
      (consumeMessageKeyResultAt A x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
       (lsLogFilterAddr ↦₆₄ 0#64)) ∗
      (ratchetAt A x.self x.G x.st ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool ∗ R) :=
    Satisfies.mono (sepConj_mono_left hP1) hm1
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self x.G (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗ R) := by
    rw [hmodel]
    exact Satisfies.of_eq hm1' (by dsimp only; ac_rfl)
  have hnpan : (x.model F).1 ≠ .error .panic := by
    rw [hmodel]; intro h; cases h
  have htouch : x.touched F = none := by
    unfold ConsumeMessageKeyGhost.touched; rw [hmodel]
  have hG' : x.G.AgreeExcept x.G (x.touched F) := by
    rw [htouch]; exact RatchetGhost.AgreeExcept.refl_none x.G
  exact reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_placed_outcome x x.G R s0 s1 hpc1 hrun1 hsp1 hsp1_align htrace1 hnpan hG' hm1_ep)

end CryptoVerification.LibsignalSession.TakePath
