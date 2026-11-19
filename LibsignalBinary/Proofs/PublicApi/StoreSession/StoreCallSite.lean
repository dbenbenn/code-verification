/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreSession.StoreShim -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreSession.StorePoll -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prog -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP.ControlTactics
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# `store_session` Call Segment of `session_message_decrypt_signal_with_stores`

Verifies `0x3c830 .. 0x3c8d0` (`+0x2388 .. +0x2428` of `0x3a4a8`): dispatches
`SessionStore::store_session` via `[vtS + 0x20]`, polls the returned `Pin<Box<dyn Future>>` via
`[vtF + 0x18]` into `sp + 0x5f0`, copies the payload to `sp + 0x550`, drops and deallocates the
32-byte future box, and reaches `0x3c8d0: cmn x28, #2` with `x28 = pollTag ans`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `session_message_decrypt_signal` (`0x3a4a8`). -/
abbrev decWithStoresName : String := "session_message_decrypt_signal"

/-- The no-op drop of the `store_session` future (`0x42a44`, `ret`; ICF-shared drop glue). -/
abbrev futDropName : String :=
  "core::ptr::drop_glue::<<libsignal_session_stores::HookSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}>"

/-- The no-op drop: no footprint, trace unchanged. -/
@[expose] def futDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-! ## Calls and frames -/

/-- Call a callee that may panic (state-dependent `Qpan`), continue with a `SepWP` to `target_pc`
(`Keys/CreateChain.lean`'s `SepWPp.call_allowPanic_ret` without the image invariant). -/
private theorem sepWPp_call_panic {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp hcall hpc hrun hsp_align hlr hpre
    (fun sf code _ _ hpost => by rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm => SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm))
    (fun sf _ _ hpost => by rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

private theorem shim_onPanic_entails {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

open Lean Elab Tactic in
/-- `storeSession_call_panic hcall ghost`: call a may-panic callee from a `SepWPp` goal whose panic
postcondition is `⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap` (`wpp_call_ret` of
`Keys/CreateChain.lean` on `sepWPp_call_panic`). -/
elab "storeSession_call_panic " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gs
    | throwError "storeSession_call_panic: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

/-- The segment's stack (`sp` = the caller's): the poll's (the largest callee's). -/
abbrev storeSegStack : Nat := storeSessionPollStack

private theorem stack_seg_shim (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - storeSessionShimStack) ∗
        stackAt sp storeSessionShimStack := by
  have h := stackAt_split_bottom sp storeSessionShimStack
    (storeSegStack - storeSessionShimStack) (by decide)
  rwa [show storeSessionShimStack + (storeSegStack - storeSessionShimStack) = storeSegStack
    by decide] at h

private theorem stack_seg_shim' (sp : BitVec 64) :
    memRegion (sp - 16416#64) (storeSegStack - storeSessionShimStack) ∗
        stackAt sp storeSessionShimStack = stackAt sp storeSegStack :=
  (stack_seg_shim sp).symm

private theorem stack_seg_alloc (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (storeSegStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (storeSegStack - allocHookStack) = storeSegStack by decide] at h

/-- Re-split of the poll's sret after the copy: words at `+8`, `+0xc` (`ldur q0` low), `+0x14`
(high), `+0x1c` (`ldur q1` low), `+0x24` (high), `+0x2c`. -/
private theorem out_repack (o w1 w2 w3 w4 w5 : BitVec 64) :
    ((o + 8#64) ↦₆₄ w1) ∗ ((o + 16#64) ↦₆₄ w2) ∗ ((o + 24#64) ↦₆₄ w3) ∗
        ((o + 32#64) ↦₆₄ w4) ∗ ((o + 40#64) ↦₆₄ w5) =
      ((o + 8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((o + 12#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((o + 20#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((o + 28#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((o + 36#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((o + 44#64) ↦₃₂ w5.extractLsb' 32 32) := by
  have e : ∀ hi lo : BitVec 32, ∀ a : BitVec 64,
      (a ↦₆₄ (hi ++ lo)) = ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) := by
    intro hi lo a
    rw [pointsTo64_split32]
    congr 2 <;> bv_bits
  simp only [e, pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## The segment -/

private theorem out_repack_sp (sp w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 1528#64) ↦₆₄ w1) ∗ ((sp + 1536#64) ↦₆₄ w2) ∗ ((sp + 1544#64) ↦₆₄ w3) ∗
        ((sp + 1552#64) ↦₆₄ w4) ∗ ((sp + 1560#64) ↦₆₄ w5) =
      ((sp + 1528#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((sp + 1532#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((sp + 1540#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp + 1548#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((sp + 1556#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 1564#64) ↦₃₂ w5.extractLsb' 32 32) := by
  have h := out_repack (sp + 1520#64) w1 w2 w3 w4 w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

private theorem box_fold (p u0 u1 u2 : BitVec 64) (b0 : BitVec 8) :
    (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7 ⊢ memRegion p 32 := by
  rw [memRegion_split p 8 24 (by decide), memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))

private theorem stack_seg_alloc' (sp : BitVec 64) :
    stackAt sp storeSessionPollStack =
      memRegion (sp - 16416#64) (storeSegStack - allocHookStack) ∗ stackAt sp allocHookStack :=
  stack_seg_alloc sp

end CryptoVerification.LibsignalPublicApi.StoreSession
