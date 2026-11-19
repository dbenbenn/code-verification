/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3

/-!
# Stage P2 Substages 1–3 Composition

Proves `stageP2_sub1_to_3_kits_ext` and `stageP2_sub1_to_3_kits` (`+0x0868 → +0x0d5c` or error exit
to `s0.readReg64 .x30` via Arms 1–2), threading `FsAt` via `stageP2Quiet` and `calleeSavedVRegs`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_ro_intro_mid {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → s.mem ⊨ Ro ∗ R)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (Ro ∗ P) ∗ R := by rw [sepConj_assoc]; exact hro hm
  exact h R hm' hL

theorem p2_drop_frame_mid {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest)
    (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_finish_err_arm {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre ArmOut Rest : SepProp} {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ ArmOut ∗ Rest) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := SepWPp.mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  exact SepWPp.done hpcf hrunf (hQ sf (ArmOut ∗ Rest) hst hpcf hrunf htrf (Entails.refl _) hΦ)

theorem p2_finish_err_arm_drop {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre ArmOut Rest Drop Keep : SepProp} {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ArmOut ∗ Rest ⊢ Drop ∗ Keep)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := SepWPp.mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  refine SepWPp.weaken_frame hSplit (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  refine p2_drop_frame_mid (Drop := Drop) rfl ?_
  exact SepWPp.done hpcf hrunf (hQ sf Keep hst hpcf hrunf htrf (Entails.refl _) hΦ)

theorem p2_bind_sepWPp_oom_frame {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  have hstage' : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ sm' : State, (sm' = sm ∧ Q_regs sm) ∧ (P_m ⊢ P_stage_post sm'))
      (PanicOomProp s0) :=
    SepWPp.mono_run hstage fun sm _ ⟨hent, hregs⟩ => ⟨sm, ⟨rfl, hregs⟩, hent⟩
  exact p2_bind_sepWPp_exists_frame hstage' hP fun sm' sm hst hpcm hrunm ⟨heq, hregs⟩ => by
    cases heq
    exact hnext sm' hst hpcm hrunm hregs

theorem p2_bytes7_937_to_cells8_930 (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At (sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (sp + 0x937#64) 57 ⊢
      cells (sp + 0x930#64) 8 := by
  rw [p2_cells8_930_split_7_57 sp]
  exact sepConj_mono_left (p2_bytes7At_to_memRegion7 (sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6)

theorem p2_pt64_to_bytes7_1 (p u : BitVec 64) :
    (p ↦₆₄ u) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 := by
  refine Entails.trans (pointsTo64_entails_memRegion p u) ?_
  rw [ProofLib.memRegion_split p 7 1 (by decide)]
  refine Entails.trans (sepConj_mono_left (p2_memRegion7_to_bytes7At p)) ?_
  sep_norm
  exact Entails.refl _

theorem p2_bytes7_1_to_pt64 (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 ⊢
      ∃∗ u : BitVec 64, (p ↦₆₄ u) := by
  refine Entails.trans (sepConj_mono_left (p2_bytes7At_to_memRegion7 p b0 b1 b2 b3 b4 b5 b6)) ?_
  rw [← ProofLib.memRegion_split p 7 1 (by decide), ProofLib.memRegion_eight p]
  exact Entails.refl _

theorem p2_pt64_to_memRegion7_1 (p u : BitVec 64) :
    (p ↦₆₄ u) ⊢ memRegion p 7 ∗ memRegion (p + 7#64) 1 := by
  rw [← ProofLib.memRegion_split p 7 1 (by decide)]
  exact pointsTo64_entails_memRegion p u

theorem p2_memRegion7_1_to_pt64 (p : BitVec 64) :
    memRegion p 7 ∗ memRegion (p + 7#64) 1 ⊢ ∃∗ u : BitVec 64, (p ↦₆₄ u) := by
  rw [← ProofLib.memRegion_split p 7 1 (by decide), ProofLib.memRegion_eight p]
  exact Entails.refl _

theorem p2_sepWPp_frame_eq {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog target s P' Q Qp)
    (hP : P = P') :
    SepWPp prog target s P Q Qp :=
  hP ▸ hw

theorem p2_keyPair64UnalignedAt_to_memRegion (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ⊢
      memRegion a 64 := by
  dsimp only [keyPair64UnalignedAt]
  have hm := sepConj_mono (p2_bytes7At_to_memRegion7 a b0 b1 b2 b3 b4 b5 b6)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x07#64) w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x0f#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x17#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x1f#64) w3)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x27#64) w4)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x2f#64) w5)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x37#64) w6)
      (pointsTo8_entails_memRegion (a + 0x3f#64) b63))))))))
  have heq :
      memRegion a 7 ∗ (memRegion (a + 0x07#64) 8 ∗ (memRegion (a + 0x0f#64) 8 ∗
      (memRegion (a + 0x17#64) 8 ∗ (memRegion (a + 0x1f#64) 8 ∗ (memRegion (a + 0x27#64) 8 ∗
      (memRegion (a + 0x2f#64) 8 ∗ (memRegion (a + 0x37#64) 8 ∗ memRegion (a + 0x3f#64) 1))))))) =
      memRegion a 64 := by
    rw [← ProofLib.memRegion_split' (b := a + 0x37#64) (n := 8) (k := 1)
          (b' := a + 0x3f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x2f#64) (n := 8) (k := 9)
          (b' := a + 0x37#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x27#64) (n := 8) (k := 17)
          (b' := a + 0x2f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x1f#64) (n := 8) (k := 25)
          (b' := a + 0x27#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x17#64) (n := 8) (k := 33)
          (b' := a + 0x1f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x0f#64) (n := 8) (k := 41)
          (b' := a + 0x17#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x07#64) (n := 8) (k := 49)
          (b' := a + 0x0f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a) (n := 7) (k := 57)
          (b' := a + 0x07#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
