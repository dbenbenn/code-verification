/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen

/-!
# Version-Mismatch Segment of `session_message_decrypt_signal` (`SegMismatch`)

Proves `segMismatch_ok` (`+0x7e4 → +0x850`): constructs `UnrecognizedMessageVersion(x9)`, invokes
the logging closure and `RawVec<SignalProtocolError>::grow_one`, pushes the 48-byte entry onto
`errs`, and reaches `FState`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SegDecryptFacts

theorem stackAt_root_split_closure (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - closureStack) ∗
        stackAt sp closureStack :=
  stackAt_split_bottom sp closureStack (rootStack - closureStack) (by decide)

theorem stackAt_root_split_grow (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack :=
  stackAt_split_bottom sp growOneSpeStack (rootStack - growOneSpeStack) (by decide)

theorem memRegion_5f0_split48 (sp : BitVec 64) :
    memRegion (sp + 0x5f0#64) 0x6b0 =
      memRegion (sp + 0x5f0#64) 48 ∗ memRegion (sp + 0x620#64) 1664 := by
  rw [show (0x6b0 : Nat) = 48 + 1664 from rfl,
    memRegion_split (sp + 0x5f0#64) 48 1664 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_192_split48 (p : BitVec 64) :
    memRegion p 192 =
      memRegion p 48 ∗ memRegion (p + 48#64) 144 := by
  rw [show (192 : Nat) = 48 + 144 from rfl,
    memRegion_split p 48 144 (by decide)]

theorem errsAt_nil_unfold (A : RustAlloc) (sp : BitVec 64) :
    errsAt A (sp + 0x5d8#64) [] =
      ((sp + 0x5d8#64) ↦₆₄ 0#64) ∗ ((sp + 0x5e0#64) ↦₆₄ 8#64) ∗ ((sp + 0x5e8#64) ↦₆₄ 0#64) := by
  simp only [errsAt, BitVec.add_assoc, BitVec.reduceAdd]

theorem errsAt_singleton_intro (A : RustAlloc) (sp p : BitVec 64) (r : RecErr)
    (hp : p ≠ 0) :
    ((sp + 0x5d8#64) ↦₆₄ 4#64) ∗ ((sp + 0x5e0#64) ↦₆₄ p) ∗ ((sp + 0x5e8#64) ↦₆₄ 1#64) ∗
      A.live p 192 8 ∗ recErrAt A p r ∗ memRegion (p + 48#64) 144 ⊢
      ∃∗ r' : RecErr, errsAt A (sp + 0x5d8#64) [r'] := by
  refine Entails.sepExists_right r ?_
  simp only [errsAt, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right p ?_
  exact Entails.pure_right hp (Entails.refl _)

theorem closureStack_to_growStack (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - closureStack) ∗
      stackAt sp closureStack ⊢
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack := by
  rw [← stackAt_root_split_closure sp, stackAt_root_split_grow sp]
  exact Entails.refl _

theorem growStack_to_rootStack (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack ⊢
    stackAt sp rootStack := by
  rw [← stackAt_root_split_grow sp]
  exact Entails.refl _

theorem mismatch_errsAt_entails (A : RustAlloc) (sp p : BitVec 64)
    (w1 w2 w3 w4 w5 : BitVec 64) (v8 : BitVec 8) (hp : p ≠ 0) :
    ((sp + 1496#64) ↦₆₄ 4#64) ∗ ((sp + 1504#64) ↦₆₄ p) ∗ ((sp + 1512#64) ↦₆₄ 1#64) ∗
    A.live p 192 8 ∗
    (p ↦₆₄ 9223372036854775814#64) ∗
    ((p + 8#64) ↦₆₄ (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v8)) ∗
    ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
    ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗
    memRegion (p + 48#64) 144 ⊢
    ∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r] := by
  have h1 : w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 v8 =
      (w1.extractLsb' 32 32) ++ BitVec.setWidth 32 v8 := by bv_bits
  have h2 : speWord 6 = 9223372036854775814#64 := rfl
  have hrec := version_words6At_entails_recErrAt A p
    (BitVec.setWidth 32 v8) (w1.extractLsb' 32 32) w2 w3 w4 w5
  unfold words6At at hrec
  rw [h2, ← h1] at hrec
  refine Entails.trans ?_ (errsAt_singleton_intro A sp p (.version (BitVec.setWidth 32 v8)) hp)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  simpa only [← sepConj_assoc] using sepConj_mono_left hrec

theorem words6_5f0_to_memRegion (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp + 1520#64) ↦₆₄ v0) ∗ ((sp + 1528#64) ↦₆₄ v1) ∗
    ((sp + 1536#64) ↦₆₄ v2) ∗ ((sp + 1544#64) ↦₆₄ v3) ∗
    ((sp + 1552#64) ↦₆₄ v4) ∗ ((sp + 1560#64) ↦₆₄ v5) ∗
    memRegion (sp + 1568#64) 1664 ⊢
    memRegion (sp + 0x5f0#64) 0x6b0 := by
  rw [memRegion_5f0_split48 sp, memRegion48_eq_words6At (sp + 0x5f0#64)]
  simp only [← sepConj_assoc]
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3
      (Entails.sepExists_right v4 (Entails.sepExists_right v5 ?_)))))
  unfold words6At
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
  exact Entails.refl _

theorem sessionStateAt_exists_intro (A : RustAlloc) (p : BitVec 64)
    (G : _) (st : _) :
    sessionStateAt A p G st ⊢ ∃∗ G₂, ∃∗ st₂, sessionStateAt A p G₂ st₂ :=
  Entails.sepExists_right G (Entails.sepExists_right st (Entails.refl _))

theorem noPanic_onPanic_entails {Qpan : SepProp} {F : SepProp} :
    (⌜False⌝ : SepProp) ∗ F ⊢ Qpan := by
  refine Entails.pure_left fun h => False.elim h

theorem grow_onPanic_entails {P1 P2 : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ P2 ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨Or.inr (Or.inr halloc), hpref⟩ (entails_anyHeap _)

theorem segDecrypt_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

theorem segDecrypt_replace_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Q F G : SepProp} {post : State → SepProp → Prop}
    (hPQ : P ⊢ Q) (hG : G = P ∗ F)
    (h : SepWP prog target_pc s (Q ∗ F) post) :
    SepWP prog target_pc s G post := by
  subst hG; exact SepWP.weaken_pre (sepConj_mono_left hPQ) h

macro "segDecrypt_wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 200000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply segDecrypt_exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))

theorem segDecrypt_of_sepWP_placed {prog : Program} {pl : Obj.MultiPlacement} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hF.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem segDecrypt_of_sepWP_ret_placed {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog ret s P (fun sf P_f => LibsignalCodeRoLoaded pl sf.mem → Q sf P_f)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq (hF.of_keepsFrozen hsteps.keepsFrozen)⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem segDecrypt_call_placed {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hF.of_keepsFrozen hsteps.keepsFrozen) R' hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq.1] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · rw [hexit_eq.2] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

open Lean Elab Tactic in
elab "segDecrypt_wpp_call_placed " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (segDecrypt_call_placed $hcall (x := $a) $hF)
    { try wp_norm_goal; try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try wp_norm_goal; try assumption; try rfl }
    { simp only [Reg.lr, wp_norm, arm64_norm]; rfl }
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "segDecrypt_wpp_call_placed: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_loaded := ($hF).1
    have _hF_ro := ($hF).2
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      mkTryDecryptGhost, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec]
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      let id := mkIdent decl.userName
      evalTactic (← `(tactic| try rw [$id:ident] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      mkTryDecryptGhost, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      mkTryDecryptGhost, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec,
    growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
    mkTryDecryptGhost, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec]))
  let mut oldHspIds : Array Ident := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      oldHspIds := oldHspIds.push (mkIdent decl.userName)
  wpNormAndSplitHyp hspId
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        withLsCodeLoaded,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

theorem seg_of_sepWPp_F_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (_htarget : target = recFPCPlaced)
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → FStatePlaced C A ctl uuidTryParse S x R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
      (FStatePlaced C A ctl uuidTryParse S x R s0 s' ∨
        regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hF hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end SegDecryptFacts

open SegDecryptFacts

attribute [local irreducible] Program.fetch Program.externAt?

/-- Relocatable `[LibsignalPlacement]` version of `segMismatch_ok`. -/
theorem segMismatch_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} :
    SegMismatchPlacedSpec C A ctl uuidTryParse S H := by
  intro hgrow hclosure x G₁ R s0 s hM hL
  rcases hM with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_197).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  unfold recFramePlaced at hmem
  rw [hsp0, stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_F_placed rfl hmem hL
  apply segDecrypt_of_sepWP_placed hF0 (mid := lsmpl.base 159)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  segDecrypt_wpp_call_placed hclosure () hF1 noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 42)
  segDecrypt_wp_extract_exists
  rename_i htr_sf
  refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF2
  segDecrypt_wpp_call_placed hgrow (s.sp + 0x5d8#64, 0#64, 8#64, []) hF2
    (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_sf, htr]))
  apply segDecrypt_of_sepWP_ret_placed hF_sf_1
  segDecrypt_wp_extract_exists
  rename_i p' hp'
  rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
  unfold words6At
  segDecrypt_wp_extract_exists
  wp_steps
  rw [hsp_sf]
  refine segDecrypt_replace_pre
    (mismatch_errsAt_entails A s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hp'.2) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (words6_5f0_to_memRegion s.sp 9223372036854775814#64
      (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
      w2 w3 w4 w5) (by sep_focus) ?_
  refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
  refine segDecrypt_replace_pre (sessionStateAt_exists_intro A (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (draws_of_version_ne C x hne ▸ tapeAfter_zero ctl x.cur x.rest) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3 hmf
  refine ⟨by unfold recFPCPlaced; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
  · refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
            by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
            by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
            by simp only [wp_norm, arm64_norm, hp'.1, htr_sf, htr],
            hF3,
            by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
  · unfold recFramePlaced
    rw [hsp0]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

end CryptoVerification.LibsignalTripleRatchet.Record

