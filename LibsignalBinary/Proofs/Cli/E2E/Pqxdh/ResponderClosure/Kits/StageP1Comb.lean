/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Stage P1 `SepWPp` Combinators and Kit Algebra

Shared OOM-prefix transport, `Steps`-carrying `SepWPp` sequencing combinators, stack-splitting and
kit precondition introducers, and `SessionRecord` / `trustPollOutAt` packing lemmas for Stage P1.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. OOM Prefix Transport & `Steps`-Carrying `SepWPp` Combinators -/

theorem allocFailedIn_trans {s0 s sf : State}
    (h0s : s0.trace <+: s.trace) (hsf : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at hsf ⊢
  obtain ⟨pre, hpre⟩ := h0s
  have hlen : (s0.trace ++ pre).length = s0.trace.length + pre.length := List.length_append
  have hle : s0.trace.length ≤ s.trace.length := by rw [← hpre]; omega
  have hdrop : sf.trace.drop s.trace.length =
      (sf.trace.drop s0.trace.length).drop (s.trace.length - s0.trace.length) := by
    rw [List.drop_drop, Nat.add_sub_of_le hle]
  rw [hdrop] at hsf
  exact List.mem_of_mem_drop hsf

theorem allowPanic_oom_of_prefix {s0 s sf : State} {F : SepProp}
    (htr : s0.trace <+: s.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  exact allowPanic_frame (fun ⟨ha, hp⟩ => ⟨allocFailedIn_trans htr ha, htr.trans hp⟩) hm

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.bind_sepWPp_steps_frame
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem stack_loadCall_to_loadShim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack :=
  stackAt_split_of_le sp (loadCallStack kit) kit.loadShimStack (Nat.le_max_left _ _) hn

theorem stack_loadCall_to_loadPoll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack :=
  stackAt_split_of_le sp (loadCallStack kit) kit.loadPollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_loadCall_to_alloc {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp (loadCallStack kit) allocHookStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_trustCall_to_trustPoll {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : trustCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (trustCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (trustCallStack ikit))
        (trustCallStack ikit - ikit.trustPollStack) ∗
        stackAt sp ikit.trustPollStack :=
  stackAt_split_of_le sp (trustCallStack ikit) ikit.trustPollStack
    (trustPollStack_le_trustCall ikit) hn

theorem stack_trustCall_to_alloc {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : trustCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (trustCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (trustCallStack ikit))
        (trustCallStack ikit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp (trustCallStack ikit) allocHookStack
    (allocHookStack_le_trustCall ikit) hn

theorem stack_stageP1_to_load {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1CallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1CallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1CallStack kit ikit))
        (stageP1CallStack kit ikit - loadCallStack kit) ∗
        stackAt sp (loadCallStack kit) :=
  stackAt_split_of_le sp (stageP1CallStack kit ikit) (loadCallStack kit)
    (Nat.le_max_left _ _) hn

theorem stack_stageP1_to_trust {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1CallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1CallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1CallStack kit ikit))
        (stageP1CallStack kit ikit - trustCallStack ikit) ∗
        stackAt sp (trustCallStack ikit) :=
  stackAt_split_of_le sp (stageP1CallStack kit ikit) (trustCallStack ikit)
    (Nat.le_max_right _ _) hn

theorem recordHeap_prevCap_lt {A : RustAlloc} {g : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} :
    recordHeap A g r ⊢ ⌜g.prevCap.toNat < 2 ^ 63⌝ ∗ recordHeap A g r := by
  unfold recordHeap vecBuf
  sep_norm
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

theorem loadPollOut_some_unpack (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b sp : BitVec 64) (r : SessionRecord (List (BitVec 8))) :
    loadPollOutAtS Scope A b (sp + 0x3e0#64) (.ok (some r)) ⊢
      ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜Scope r ∧ g.prevCap.toNat < 2 ^ 63 ∧ RecordTailInline g r w4 w5 w6 tail ∧
          tail.length = 312⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ g.prevCap) ∗
        ((sp + 0x3e8#64) ↦₆₄ g.prevPtr) ∗
        ((sp + 0x3f0#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₆₄
          ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
        ((sp + 0x3fc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
        ((sp + 0x404#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 0x40c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((sp + 0x414#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        ((sp + 0x418#64) ↦ₛ tail) ∗
        recordHeap A g r := by
  dsimp only [loadPollOutAtS, loadPollOutAt]
  apply Entails.pure_left; intro hscope
  apply Entails.sepExists_elim; intro g
  rw [sessionRecordAt_eq_words56_sep_tail A (sp + 0x3e0#64) g r]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro tail
  apply Entails.pure_left; intro htail
  have hlen : tail.length = 312 := htail.1
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right recordHeap_prevCap_lt)) ?_
  dsimp only [recordWords56At]
  sep_norm
  repeat (simp only [sepConj_pure_left_comm])
  apply Entails.pure_left; intro hprev
  refine Entails.sepExists_right g
    (Entails.sepExists_right w4
      (Entails.sepExists_right w5
        (Entails.sepExists_right w6
          (Entails.sepExists_right tail
            (Entails.pure_right ⟨hscope, hprev, htail, hlen⟩ ?_)))))
  have hrep := words5_repack_sp3e0 sp 0#64 (recordCurCap g) w4 w5 w6
  refine Entails.of_eq ?_
  calc
    _ = ((sp + 992#64) ↦₆₄ g.prevCap) ∗ ((sp + 1000#64) ↦₆₄ g.prevPtr) ∗
        (((sp + 1008#64) ↦₆₄ 0#64) ∗ ((sp + 1016#64) ↦₆₄ recordCurCap g) ∗
          ((sp + 1024#64) ↦₆₄ w4) ∗ ((sp + 1032#64) ↦₆₄ w5) ∗ ((sp + 1040#64) ↦₆₄ w6)) ∗
        ((sp + 1048#64) ↦ₛ tail) ∗ recordHeap A g r := by ac_rfl
    _ = _ := by rw [hrep]; ac_rfl

theorem sp3e0_368_fold (sp w0 w1 w2 w3 w4 w5 : BitVec 64) (d0 d6 : BitVec 32)
    (tail : List (BitVec 8)) (htail : tail.length = 312) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗
      ((sp + 0x3e8#64) ↦₆₄ w1) ∗
      ((sp + 0x3f0#64) ↦₃₂ d0) ∗
      ((sp + 0x3f4#64) ↦₆₄ w2) ∗
      ((sp + 0x3fc#64) ↦₆₄ w3) ∗
      ((sp + 0x404#64) ↦₆₄ w4) ∗
      ((sp + 0x40c#64) ↦₆₄ w5) ∗
      ((sp + 0x414#64) ↦₃₂ d6) ∗
      ((sp + 0x418#64) ↦ₛ tail) ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 360 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 8 352 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 4 348 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64) 8 340 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64) 8 332 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64) 8 324
        (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 316
        (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64)
        4 312 (by decide)]
  sep_norm
  have hb := pointsToBytes_entails_memRegion (sp + 1048#64) tail
  rw [htail] at hb
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _) hb)))))))

theorem sp_d8_bytes_rejoin (sp v0 v1 v2 v3 : BitVec 64) (dv4 : BitVec 32)
    (tail : List (BitVec 8)) (htail : tail.length = 312) :
    ((sp + 0xd8#64) ↦ₛ tail) ∗
      ((sp + 0x210#64) ↦₆₄ v0) ∗ ((sp + 0x218#64) ↦₆₄ v1) ∗
      ((sp + 0x220#64) ↦₆₄ v2) ∗ ((sp + 0x228#64) ↦₆₄ v3) ∗
      ((sp + 0x230#64) ↦₃₂ dv4) ⊢
      memRegion (sp + 0xd8#64) 348 := by
  have hb := pointsToBytes_entails_memRegion (sp + 0xd8#64) tail
  rw [htail] at hb
  exact Entails.trans (sepConj_mono_left hb) (sp_d8_348_rejoin sp v0 v1 v2 v3 dv4)

theorem coro_e0_some_pack (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8)))
    (w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (hscope : Scope r) (htail : RecordTailInline g r w4 w5 w6 tail) :
    ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
      ((coroPtr + 0xf4#64) ↦₆₄
        ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((coroPtr + 0xfc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
      ((coroPtr + 0x104#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
      ((coroPtr + 0x10c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
      ((coroPtr + 0x114#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      ((coroPtr + 0x118#64) ↦ₛ tail) ∗
      recordHeap A g r ⊢
      p1LoadedRecordAt Scope A coroPtr (some r) := by
  dsimp only [p1LoadedRecordAt]
  refine Entails.pure_right hscope (Entails.sepExists_right g ?_)
  have hunp := words5_unpack_coro_e0 coroPtr 0#64 (recordCurCap g) w4 w5 w6
  have hrec := sessionRecordAt_of_words56_sep_tail A (coroPtr + 0xe0#64) g r htail
  dsimp only [recordWords56At] at hrec
  (try simp only [BitVec.add_assoc] at hunp hrec ⊢); (try simp only [BitVec.reduceAdd] at hunp hrec ⊢); (try simp only [sepConj_assoc] at hunp hrec ⊢)
  refine Entails.trans (Entails.of_eq ?_) hrec
  calc
    _ = ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
        (((coroPtr + 240#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
          ((coroPtr + 244#64) ↦₆₄
            ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((coroPtr + 252#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
          ((coroPtr + 260#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((coroPtr + 268#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
          ((coroPtr + 276#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
        ((coroPtr + 280#64) ↦ₛ tail) ∗ recordHeap A g r := by ac_rfl
    _ = _ := by rw [hunp]; ac_rfl

theorem cells2_fold_398 (coroPtr w0 w1 : BitVec 64) :
    ((coroPtr + 0x398#64) ↦₆₄ w0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ w1) ⊢
      cells (coroPtr + 0x398#64) 2 := by
  dsimp only [cells]
  sep_norm
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))

theorem SepWPp.mono_run {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q₁ Qp)
    (himp : ∀ sf P_f, Q₁ sf P_f → Q₂ sf P_f) :
    SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hrest⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, himp sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hrest⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
