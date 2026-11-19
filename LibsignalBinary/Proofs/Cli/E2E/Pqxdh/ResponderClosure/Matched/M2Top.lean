/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Bridge
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Ok
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Tail
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Top-Level Stage P2 Matched-Session Contract (`stageP2_matched_ok`)

Composes `+0x0868 → +0x094c` (`stageP2_matched_0868_to_094c`) with both arms of the
`sess.state.remoteIdentity = some pm.identityKey` check:
- Match (`= some pm.identityKey`): advances `+0x094c → +0x1778` with `(coroPtr + 0x298) ↦₃₂ 2#32`,
  `prevSessionsEmptyAt A coroPtr g`, and `TokenInit img ∗ genP3Pre …`.
- Mismatch (`≠ some pm.identityKey`): unwinds both `none` and `some ik` (`ik ≠ pm.identityKey`) via
  `stageP2_matched_mismatch_tail` to `s0.readReg64 .x30` with `InvalidMessage(.preKey)`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

-- Repeat `-arm64_norm` attributes after importing `GenP3.StageP3Stmt` (via `M2Ok`).
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp eq_of_sep_emp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem publicKey_beq_false_of_ne {remIdKey ik : IdentityKey}
    (hne : some ik ≠ some remIdKey) :
    (remIdKey.publicKey == ik.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply hne
  cases remIdKey with | mk pk1 =>
  cases ik with | mk pk2 =>
  dsimp only at heq
  subst heq
  rfl

private theorem coro_2a0_split32 (coroPtr w : BitVec 64) :
    ((coroPtr + 0x2a0#64) ↦₆₄ w) =
      ((coroPtr + 0x2a0#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((coroPtr + 0x2a4#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32 (coroPtr + 0x2a0#64) w]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem panicOomProp_frame {s0 sf : State} {Pf : SepProp} (F : SepProp)
    (h : CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf) :
    CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf (Pf ∗ F) := by
  intro R hmR
  rw [sepConj_assoc Pf F R] at hmR
  have h1 := h (F ∗ R) hmR
  rw [← sepConj_assoc _ F R] at h1
  exact allowPanic_frame id h1

private theorem bind_sepWPp_steps_frame_panicF
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P F P_stage P_stage_post F_inner : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf,
      CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = (P_stage ∗ F) ∗ F_inner)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ (F_inner ∗ F)) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hP_re : P = P_stage ∗ (F_inner ∗ F) := by
    rw [hP]; ac_rfl
  rw [hP_re, sepConj_assoc P_stage (F_inner ∗ F) R] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F_inner ∗ F) ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ (F_inner ∗ F)) ∗ R := by
      rw [sepConj_assoc P_stage_post (F_inner ∗ F) R]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc P_m (F_inner ∗ F) R, ← sepConj_assoc P_m F_inner F] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, (P_m ∗ F_inner) ∗ F, hmm,
      hpan sm (P_m ∗ F_inner) (panicOomProp_frame F_inner hpanm)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
