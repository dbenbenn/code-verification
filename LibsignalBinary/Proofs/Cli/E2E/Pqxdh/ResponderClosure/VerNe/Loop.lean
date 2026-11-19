/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErr
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMoves
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeel
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopSegs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# One-Element `previous_sessions` Loop Composition

Proves `overPrevLoop_cli_of_dec_ext` (`+0x1e78 → +0x2cfc` on `tripleRatchetProgAtExt`) by composing
the loop head (`+0x1e78 → +0x1ee8`), inlined `SessionStructure::decode` (`+0x1ee8 → +0x2620`),
inline `prostSSGQAt` peel, five-step `memcpy` chain (`+0x2620 → +0x1fd4`), and version-mismatch
skip tail (`+0x1fd4 → +0x2cfc`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Framing and scratch repacking helpers -/

private theorem bind_sepWPp_frame_loop {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (P3P4.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stackAt_sub_eq_loop (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

private theorem prevVecAt_open_eq_loop (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
      overPrevElemAt A prevCap prevPtr enc := by
  rw [prevVecAt_one_eq_elemAt A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap, hdrP_coro_eq]
  ac_rfl

private theorem loopScratch_to_decPre (sp : BitVec 64) :
    memRegion (sp + 0x538#64) 1016 ∗
    memRegion (sp + 0x930#64) 48 ∗
    memRegion (sp + 0x960#64) 48 ∗
    memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 344 ∗
    memRegion (sp + 0xbe8#64) 136 =
      memRegion (sp + 0x538#64) 40 ∗
      memRegion (sp + 0x560#64) 320 ∗
      memRegion (sp + 0x6a0#64) 320 ∗
      memRegion (sp + 0x7e0#64) 320 ∗
      overDecScratchPre sp := by
  have h538 :
      memRegion (sp + 0x538#64) 1016 =
        memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
        memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
        memRegion (sp + 0x920#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x538#64) (n := 40) (k := 976) (b' := sp + 0x560#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x560#64) (n := 320) (k := 656) (b' := sp + 0x6a0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x6a0#64) (n := 320) (k := 336) (b' := sp + 0x7e0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x7e0#64) (n := 320) (k := 16) (b' := sp + 0x920#64)
          rfl (by bv_omega) (by decide)]
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48 ∗
        memRegion (sp + 0x990#64) 248 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 48) (k := 296) (b' := sp + 0x960#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 48) (k := 248) (b' := sp + 0x990#64)
          rfl (by bv_omega) (by decide)]
  unfold overDecScratchPre
  rw [h538, h990, h930]
  ac_rfl

private theorem decScratchPost_join_930 (sp : BitVec 64) :
    overDecScratchPost sp ∗ memRegion (sp + 0x930#64) 344 = overDecScratchPre sp := by
  unfold overDecScratchPost overDecScratchPre
  ac_rfl

private theorem mem920_16_split_loop (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 16 =
      ∃∗ u920 : BitVec 64, ((sp + 0x920#64) ↦₆₄ u920) ∗ memRegion (sp + 0x928#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x920#64), sepExists_sepConj_left]

private theorem mem920_16_fold_loop (sp w : BitVec 64) :
    ((sp + 0x920#64) ↦₆₄ w) ∗ memRegion (sp + 0x928#64) 8 ⊢ memRegion (sp + 0x920#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
