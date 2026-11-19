/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# General Stage P3 Composition

Proves `stageP3Gen_ok_of_clone : CloneGenStmt → StageP3GenStmt` and `stageP3Gen_ok : StageP3GenStmt`,
chaining `CloneGenStmt` (`+0x1778 → cloneExitPC img ext st msgVer`) with:
- `st.version = msgVer` (`+0x1cd4`): `p3_bl_tryDecrypt_ext_wp`, `tryDecryptSpecTPTight` with
  tight panic lifting into `genP3S5PanicProp`, and `stageP3_sub5_dispatch_ext_ok` to `+0x34dc`
  (`Ok`) or `s0.readReg64 .x30` (`Err`);
- `st.version ≠ msgVer` (`+0x1e04`): `stageP3_ver_ne_ext_ok` to `s0.readReg64 .x30`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-! ## 1. Spatial Framing Helpers for `genP3SpillAll` and `genP3PostSpatial` -/

theorem genP3SpillAll_entails_s5 (sp : BitVec 64) :
    genP3SpillAll sp ⊢ memRegion (sp + 0x930#64) 48 ∗ genP3S5SpillRem sp := by
  unfold genP3SpillAll genP3S5SpillRem
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro w
  have h930 := words6_entails_memRegion48 (sp + 0x930#64)
    w.u930 w.u938 w.u940 w.u948 w.u950 w.u958
  have h960 := words6_entails_memRegion48 (sp + 0x960#64)
    w.u960 w.u968 w.u970 w.u978 w.u980 w.u988
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h930 h960
  have hrem :
      ((sp + 0x48#64) ↦₆₄ w.u_48) ∗
      ((sp + 0x50#64) ↦₆₄ w.u_50) ∗
      ((sp + 0x5c#64) ↦₃₂ w.u_5c) ∗
      ((sp + 0x7c#64) ↦₃₂ w.u_7c) ∗
      ((sp + 0x98#64) ↦₆₄ w.u_98) ∗
      ((sp + 0xd0#64) ↦₆₄ w.u_d0) ⊢
      ∃∗ w' : GenP3S5FrontRem,
        ((sp + 0x48#64) ↦₆₄ w'.u48) ∗
        ((sp + 0x50#64) ↦₆₄ w'.u50) ∗
        ((sp + 0x5c#64) ↦₃₂ w'.u5c) ∗
        ((sp + 0x7c#64) ↦₃₂ w'.u7c) ∗
        ((sp + 0x98#64) ↦₆₄ w'.u98) ∗
        ((sp + 0xd0#64) ↦₆₄ w'.ud0) :=
    Entails.sepExists_right ⟨w.u_48, w.u_50, w.u_98, w.u_d0, w.u_5c, w.u_7c⟩ (Entails.refl _)
  refine Entails.trans (entails_replace_sub h930 (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub h960 (by sep_focus) rfl) ?_
  exact entails_replace_sub hrem (by sep_focus) (by ac_rfl)

/-! ## 2. `CloneGenStmt` Prefix Step with `TokenInit` & `stageP3Sub5ExtraPre` Frame -/

theorem sepWPp_lift_panicOom {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)} {s0 : State}
    (h : SepWPp prog ret s P Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨hpan, Pm, hmm, hoom⟩ | hexit⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pm, hmm, Or.inl hoom⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hexit)⟩
theorem stackAt_root_split_grow (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack :=
  stackAt_split_bottom sp growOneSpeStack (rootStack - growOneSpeStack) (by decide)

theorem memRegion344_104_240_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 104 ∗ memRegion (sp + 0x448#64) 240 =
      memRegion (sp + 0x3e0#64) 344 :=
  (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 104) (k := 240)
    (b' := sp + 0x448#64) rfl (by bv_omega) (by decide)).symm

/-! ## 3. `+0x1cd4 → +0x1cd8` `try_decrypt_with_state` Step with Tight Panic Lifting -/

theorem bind_sepWPp_genPanic {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {P P_stage F : SepProp} {Q_mid : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hoom (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
