/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA

/-!
# Stage P2 Shared Error Funnel and Unwind Arms 1–2

Proves the unified 6-word `SignalProtocolError` unwind funnel `stageP2_err_funnel_ext_ok`
(`+0x1648 → s0.readReg64 .x30`) and store-error unwinds `p2_arm1_err_ext_ok`
(`get_signed_pre_key` at `+0x0f38`) and `p2_arm2_err_ext_ok` (`get_kyber_pre_key` at `+0x0998`).
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
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

/-! ## 1. `SepProp` Layout, Read-Only Vtable Intro, and `SpeErrSpec` Unpacking Helpers -/

theorem p2_bind_sepWPp_steps_frame {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpanm
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Unfolds `spkGetPollOutAt` / `kpkGetPollOutAt` (`88` B) on `.error e` into
`preKeyRecordOut64At out 0xffffffffffffffff#64 (S.w0 e) ... u_38 ∗ S.heap e ∗ memRegion (out + 0x40#64) 24`. -/
theorem p2_err88_to_preKeyRecordOut64 {E : Type} (S : SpeErrSpec E) (out : BitVec 64) (e : E) :
    (out ↦₆₄ errTag) ∗ speErrAt S (out + 8#64) e ∗ memRegion (out + 0x38#64) 32 ⊢
      ∃∗ u_38 : BitVec 64,
        preKeyRecordOut64At out 0xffffffffffffffff#64
          (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e) u_38 ∗
        S.heap e ∗
        memRegion (out + 0x40#64) 24 := by
  rw [ProofLib.memRegion_split (out + 0x38#64) 8 24 (by decide),
      ProofLib.memRegion_eight (out + 0x38#64)]
  dsimp only [speErrAt, speWordsAt, preKeyRecordOut64At, errTag]
  sep_norm
  refine Entails.sepExists_elim fun u_38 => Entails.sepExists_right u_38 ?_
  exact Entails.of_eq (by ac_rfl)

/-- Unfolds `preKeyGetPollOutAt` (`56` B) on `.error e` together with trailing `8` B at `out + 0x38`
into `preKeyRecordOut64At out 0xffffffffffffffff#64 (S.w0 e) ... u_38 ∗ S.heap e`. -/
theorem p2_err56_to_preKeyRecordOut64 {E : Type} (S : SpeErrSpec E) (out : BitVec 64) (e : E) :
    ((out ↦₆₄ errTag) ∗ speErrAt S (out + 8#64) e) ∗ memRegion (out + 0x38#64) 8 ⊢
      ∃∗ u_38 : BitVec 64,
        preKeyRecordOut64At out 0xffffffffffffffff#64
          (S.w0 e) (S.w1 e) (S.w2 e) (S.w3 e) (S.w4 e) (S.w5 e) u_38 ∗
        S.heap e := by
  rw [ProofLib.memRegion_eight (out + 0x38#64)]
  dsimp only [speErrAt, speWordsAt, preKeyRecordOut64At, errTag]
  sep_norm
  refine Entails.sepExists_elim fun u_38 => Entails.sepExists_right u_38 ?_
  exact Entails.of_eq (by ac_rfl)

/-- Folds `preKeyRecordOut64At (sp + 0x3e0#64) ... ∗ memRegion (sp + 0x420#64) 304` back into
`memRegion (sp + 0x3e0#64) 368`. -/
theorem p2_preKeyRecordOut64_to_memRegion368 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At (sp + 0x3e0#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
      memRegion (sp + 0x420#64) 304 ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 64 304 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono_left ?_
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 56 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

/-- Joins `memRegion (sp + 0x420#64) 24 ∗ memRegion (sp + 0x438#64) 280` into
`memRegion (sp + 0x420#64) 304`. -/
theorem p2_memRegion_420_join (sp : BitVec 64) :
    memRegion (sp + 0x420#64) 24 ∗ memRegion (sp + 0x438#64) 280 ⊢
      memRegion (sp + 0x420#64) 304 := by
  rw [ProofLib.memRegion_split (sp + 0x420#64) 24 280 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

/-- Splits `preKeyRecordOut64At (sp + 0xa90#64) ...` (`64` B) into
`cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16`. -/
theorem p2_preKeyRecordOut64_to_cells6_a90 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At (sp + 0xa90#64) w0 w1 w2 w3 w4 w5 w6 w7 ⊢
      cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 := by
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split (sp + 0xac0#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc6 := cells6_fold (sp + 0xa90#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc6); repeat (simp only [BitVec.reduceAdd] at hc6)
  rw [show (sp + 2704#64) ↦₆₄ w0 ∗ ((sp + 2712#64) ↦₆₄ w1 ∗ ((sp + 2720#64) ↦₆₄ w2 ∗
        ((sp + 2728#64) ↦₆₄ w3 ∗ ((sp + 2736#64) ↦₆₄ w4 ∗ ((sp + 2744#64) ↦₆₄ w5 ∗
          ((sp + 2752#64) ↦₆₄ w6 ∗ (sp + 2760#64) ↦₆₄ w7)))))) =
      ((sp + 2704#64) ↦₆₄ w0 ∗ ((sp + 2712#64) ↦₆₄ w1 ∗ ((sp + 2720#64) ↦₆₄ w2 ∗
        ((sp + 2728#64) ↦₆₄ w3 ∗ ((sp + 2736#64) ↦₆₄ w4 ∗ (sp + 2744#64) ↦₆₄ w5))))) ∗
        ((sp + 2752#64) ↦₆₄ w6 ∗ (sp + 2760#64) ↦₆₄ w7) by ac_rfl]
  exact sepConj_mono hc6
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

/-! ## 2. Unified 6-Word `SignalProtocolError` Unwind Funnel (`+0x1648 -> s0.readReg64 .x30`) -/

theorem p2_zeroExtend32_extractLsb_lo (w : BitVec 64) :
    ((w.extractLsb' 0 32).zeroExtend 64).extractLsb' 0 32 = w.extractLsb' 0 32 := by
  bv_bits

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

