/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2

/-!
# Stage P2 Substage P2.3 Helpers and Shared Tail

Provides `KyberPreKeyRecord` layout/rodata helpers and proves the shared Substage P2.3 tail
`stageP2_sub3_tail_kits` (`+0x0d04 → +0x0d5c`, allocating and dropping the 21-byte `"missing pq
ciphertext"` error buffer).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_pointsToBytes_1569_entails_memRegion (ptr : BitVec 64) (pk : List (BitVec 8))
    (h : pk.length = 1568) :
    (ptr ↦ₛ (8#8 :: pk)) ⊢ memRegion ptr 1569 := by
  have h1 := ProofLib.pointsToBytes_entails_memRegion ptr (8#8 :: pk)
  have hlen : (8#8 :: pk).length = 1569 := by simp [h]
  rwa [hlen] at h1

theorem p2_pointsToBytes_3169_entails_memRegion (ptr : BitVec 64) (sk : List (BitVec 8))
    (h : sk.length = 3168) :
    (ptr ↦ₛ (8#8 :: sk)) ⊢ memRegion ptr 3169 := by
  have h1 := ProofLib.pointsToBytes_entails_memRegion ptr (8#8 :: sk)
  have hlen : (8#8 :: sk).length = 3169 := by simp [h]
  rwa [hlen] at h1

theorem p2_stackAt_kemKeyPair_eq (sp : BitVec 64) :
    stackAt sp (64 + allocHookStack) =
      (memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack) := by
  have h1 := ResponderStore.stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  rw [h2] at h1
  exact h1

theorem p2_kemStack_le_pure : 64 + allocHookStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 64 + allocHookStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_dropSpe_le_pure : dropSpeStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : dropSpeStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_memRegion_65_split_cells5 (p : BitVec 64) :
    memRegion p 65 = cells p 5 ∗ memRegion (p + 40#64) 25 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 40) (k := 25)
        (b' := p + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells p 5 (by decide)]

theorem p2_sp_a90_5words_entails_memRegion (p w0 w1 w2 w3 w4 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
    ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ memRegion (p + 40#64) 25 ⊢
      memRegion p 65 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 57) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 49) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 41) (b' :=
        p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 8) (k := 33) (b' :=
        p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 25) (b' :=
        p + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

theorem p2_errStr_21_split16_eq (p : BitVec 64) :
    memRegion p 21 =
      (∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ memRegion (p + 16#64) 5) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_errStr_overlap13_entails (p ro8 : BitVec 64) :
    ((p + 8#64) ↦₆₄ ro8) ∗ memRegion (p + 16#64) 5 ⊢
      memRegion (p + 8#64) 5 ∗ (∃∗ u13 : BitVec 64, (p + 13#64) ↦₆₄ u13) := by
  rw [← ProofLib.memRegion_eight (p + 13#64),
      ← ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (p + 8#64) ro8)

theorem p2_errStr_21_rejoin_entails (p ro0 ro13 : BitVec 64) :
    (p ↦₆₄ ro0) ∗ memRegion (p + 8#64) 5 ∗ ((p + 13#64) ↦₆₄ ro13) ⊢
      memRegion p 21 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p ro0)
    (sepConj_mono_right (pointsTo64_entails_memRegion (p + 13#64) ro13))

theorem p2_memRegion_88_spe_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 88 =
      (∃∗ b_400 : BitVec 8, ∃∗ u_3f8 : BitVec 64, ∃∗ u_3f0 : BitVec 64,
       ∃∗ u_3e8 : BitVec 64, ∃∗ u_3e0 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
        ((sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
        ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
        ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
        ((sp + 0x400#64) ↦₈ b_400) ∗
        memRegion (sp + 0x401#64) 15 ∗
        memRegion (sp + 0x410#64) 40) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 80) (b' :=
    sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 72) (b' :=
        sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 64) (b' :=
        sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 56) (b' :=
        sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 1) (k := 55) (b' :=
        sp + 0x401#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x401#64) (n := 15) (k := 40) (b' :=
        sp + 0x410#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x3e0#64),
      ProofLib.memRegion_eight (sp + 0x3e8#64),
      ProofLib.memRegion_eight (sp + 0x3f0#64),
      ProofLib.memRegion_eight (sp + 0x3f8#64),
      ProofLib.memRegion_one (sp + 0x400#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_speAt_badCiphertext_preKey_intro (A : RustAlloc) (sp errStrPtr : BitVec 64)
    (herr_nz : errStrPtr ≠ 0#64) :
    ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
    ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x400#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x401#64) 15 ∗
    A.live errStrPtr 21 1 ∗
    memRegion errStrPtr 21 ⊢
      speAt A [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) := by
  rw [ProofLib.memRegion_eq_exists_bytes errStrPtr 21 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro bs
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 ∗
        A.live errStrPtr 21 1 ∗
        ⌜bs.length = 21⌝ ∗ (errStrPtr ↦ₛ bs) =
      ⌜bs.length = 21⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  apply Entails.pure_left; intro hbs
  dsimp only [speAt, invalidMessageStrAt, RustHeap.vecU8, RustHeap.vecU8At, RustHeap.vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_right bs (Entails.sepExists_right 21#64 (Entails.sepExists_right
    errStrPtr ?_))
  have h21_nat : (21#64).toNat = 21 := rfl
  have hspe24 : speWord 24 = 0x8000000000000018#64 := rfl
  have hmsg_pk : msgTypeByte MessageType.preKey = 3#8 := rfl
  have h21_sub : (21 : Nat) - 21 = 0 := rfl
  simp only [hbs, show (21#64 = 0#64) = False by decide, show (21#64 = 0) = False by decide,
    ↓reduceIte,
    h21_nat, hspe24, hmsg_pk, h21_sub,
    BitVec.ofNat_eq_ofNat, ProofLib.memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e8#64) + 8#64 = sp + 0x3f0#64 by bv_omega,
      show (sp + 0x3e8#64) + 16#64 = sp + 0x3f8#64 by bv_omega,
      show (sp + 0x3e0#64) + 32#64 = sp + 0x400#64 by bv_omega,
      show (sp + 0x3e0#64) + 33#64 = sp + 0x401#64 by bv_omega]
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        A.live errStrPtr 21 1 ∗
        (errStrPtr ↦ₛ bs) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 =
      ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  refine Entails.pure_right ⟨by decide, by decide, herr_nz⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem p2_bind_sepWPp_steps_frame_oom {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
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

theorem p2_drop_left_sepWPp {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_drop_sep_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ p2_drop_left_sepWPp h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
