/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNegConsumer
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
import ProofLib.SepLogic.HeapIntro

/-!
# Region-Local `<EdwardsPoint as Neg>::neg` Code Verification and Master Spec

Code-level verification of `<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg`
(`edwardsPointNegWords`, 57 words = 228 bytes, 0 B stack):

- `masterEdNegSpec` and `processEdNegSpec`: `masterEdNegSpec` refines
  `edwardsPointNegUnstackedSpec false` (0 stack bytes) using `EdNegStatePreserved` (an `abbrev` of
  `MemsetStatePreserved`), omitting `mem.perm` so `CryptoHooksDehook` can prove
  `SpecStripSInvariant`, while `processEdNegSpec` carries `ProcessFieldsPreserved` so
  `CryptoHooksDehook` can derive `VmPreserved` on real runs.
- Placement-generic `pureWordsProg` `hasWords` and region-local `subroutine_ok`: proves
  `subroutine_ok P_sub entry` for `processEdNegSpec`, `masterEdNegSpec`,
  `edNegSpecK keep masterEdNegSpec`, and `masterEdNegBudgetSpec` on any hook-free `P_sub` with
  `P_sub.hasWords entry edwardsPointNegWords`.
- Fallback soundness (`edNegHook_masterEdNeg_ok`): proves `E2E.edNegHook dalekEdNegVec` satisfies
  `masterEdNegSpec`, `processEdNegSpec`, and `masterEdNegBudgetSpec`.
- `HookOk` lifts and `S2Frame` elimination (`hookOk_edNegUnstacked_elim`): lifts
  `HookOk f masterEdNegSpec` to `edwardsPointNegUnstackedSpec`, `pureByteFunctionSpec`, and
  `E2E.Pqxdh.Shared.cryptoLeafStubSpec` (including `.keepsFs` and `withVmPreserved`), and derives
  `S2Frame s.mem (f s).mem [(dst, 160)]` from `HookOk f (edwardsPointNegUnstackedSpec false)` for
  `Hole3W3VerifySigAux.shadowEdNeg`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.E2E (readVecN u8Vec vecU8)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy (edNegHook)
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhHookStack cryptoLeafStubSpec)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (S2Frame disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap
   read8_eq_of_readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn satisfies_two_blocks isBlock_two_s2frame)
open CryptoVerification.SignalSession.CliExt (inputAfter pureByteFunctionSpec)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred)
open LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg (dalekEdNegBytes dalekEdNegBytes_length
  dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg (edwardsPointNegWords
  edwardsPointNegUnstackedSpec edwardsPointNeg_unstacked_ok
  pureWordsProg_hasInstrs_edNeg pureWordsProg_noSvcMsr_edNeg)
open LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNegConsumer (
  unstacked_simulates_real_cryptoLeafStubSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (agreesOn_readable_of_s2Frame_writeBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved memsetSpecK
  pureWordsProg_externAt_none
  hookOk_frame_pureAbort hookOk_memsetSpecK_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  hookOk_withFsPred_of_keepsFs
)

/-! ## 1. Master `<EdwardsPoint as Neg>::neg` Specification & State Preservation -/

/-- Non-memory process/VM state fields preserved across real `<EdwardsPoint as Neg>::neg`
    (`edwardsPointNegWords`) and fallback `edNegHook dalekEdNegVec`, reusing `MemsetStatePreserved`
    via `abbrev` and omitting `mem.perm` so `SpecStripSInvariant` holds definitionally. -/
abbrev EdNegStatePreserved : State → State → Prop := MemsetStatePreserved

theorem EdNegStatePreserved.refl (s : State) : EdNegStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem EdNegStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : EdNegStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem EdNegStatePreserved.toProcessFieldsPreserved {s0 sf : State}
    (h : EdNegStatePreserved s0 sf) (hvm : VmPreserved s0 sf) :
    ProcessFieldsPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hvm.2.2.1⟩

/-- Permission-free master specification for `<EdwardsPoint as Neg>::neg`: requires `0` stack bytes,
    preserves `(inA ↦ₛ v.toList)`, writes `(dalekEdNegVec v).toList` to `ret`, preserves
    `EdNegStatePreserved`, and never panics, exits, or OOMs. -/
@[expose] def masterEdNegSpec : Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s0 =>
    ⌜s0.readReg64 .x0 = inA ∧ s0.readReg64 .x8 = ret⌝ ∗
      (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ⌜EdNegStatePreserved s0 sf⌝ ∗
      (inA ↦ₛ v.toList) ∗ (ret ↦ₛ (dalekEdNegVec v).toList)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process specification for `<EdwardsPoint as Neg>::neg`: identical `pre` to
    `masterEdNegSpec`, strengthening `post` to full `ProcessFieldsPreserved`. -/
@[expose] def processEdNegSpec : Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s0 =>
    ⌜s0.readReg64 .x0 = inA ∧ s0.readReg64 .x8 = ret⌝ ∗
      (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf⌝ ∗
      (inA ↦ₛ v.toList) ∗ (ret ↦ₛ (dalekEdNegVec v).toList)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem processEdNeg_pre_eq_masterEdNeg_pre :
    processEdNegSpec.pre = masterEdNegSpec.pre := rfl

theorem processEdNeg_pre_of_masterEdNeg_pre
    {x : BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64} {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterEdNegSpec.pre x s0 ∗ R) :
    s0.mem ⊨ processEdNegSpec.pre x s0 ∗ R := hp

abbrev masterEdNegBudgetSpec : Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) :=
  withVmPreserved masterEdNegSpec

/-! ## 2. Placement-Generic `pureWordsProg` & Region-Local `subroutine_ok` -/

theorem pureWordsProg_edNeg_hasWords (base : BitVec 64) :
    (pureWordsProg base edwardsPointNegWords).hasWords base edwardsPointNegWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range edwardsPointNegWords.length).all fun i =>
      (pureWordsProg 0#64 edwardsPointNegWords).readWordOff (4 * i) ==
        edwardsPointNegWords[i]?) = true
    decide +kernel)

private theorem inputAfter_false {n : Nat} (p : BitVec 64) (v : List.Vector (BitVec 8) n) :
    inputAfter false p v = (p ↦ₛ v.toList) := rfl

private theorem inputAfter_true {n : Nat} (p : BitVec 64) (v : List.Vector (BitVec 8) n) :
    inputAfter true p v = memRegion p n := rfl

/-- Full-permission region-local `subroutine_ok` for `processEdNegSpec` on any hook-free `P_sub`
    holding `edwardsPointNegWords` at `entry`. -/
theorem subroutine_ok_processEdNeg_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry edwardsPointNegWords) :
    subroutine_ok P_sub entry processEdNegSpec := by
  have hproc :=
    subroutine_ok_lift_pureWords_process
      (edwardsPointNeg_unstacked_ok false (pureWordsProg_hasInstrs_edNeg entry))
      (pureWordsProg_noSvcMsr_edNeg entry) hwords hsub_no
      (h_pre_mem := by rintro ⟨_, _, _⟩ s _; cases s; rfl)
      (h_post_mem := by rintro ⟨_, _, _⟩ s0 sf _ _; cases s0; cases sf; rfl)
  refine subroutine_ok_mono hproc (fun _ _ _ hp => hp) (fun ⟨inA, v, ret⟩ R s0 sf hq => ?_)
  dsimp only [edwardsPointNegUnstackedSpec, processEdNegSpec] at hq ⊢
  rw [inputAfter_false] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  obtain ⟨hpf, hq⟩ := hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact ⟨hpf, hq.2⟩

/-! ## 3. Fallback `edNegHook dalekEdNegVec` Soundness -/

theorem edNegHook_eq_retHook
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) :
    edNegHook edNeg =
      retHook fun s =>
        s.setMem (s.mem.writeBytes (s.readReg64 .x8)
          (edNeg (readVecN s.mem (s.readReg64 .x0) 160)).toList) := by
  funext s
  unfold edNegHook returnToLinkRegister retHook
  cases s
  rfl

theorem edNegHook_vmPreserved
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) (s : State) :
    VmPreserved s (edNegHook edNeg s) := by
  unfold edNegHook returnToLinkRegister
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun addr => ?_, FdsHiFrame.of_fs_eq rfl⟩
  exact congrFun (Memory.perm_writeBytes s.mem (s.readReg64 .x8) _) addr

theorem edNegHook_preserves_oom_pool
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) (s : State) :
    OomPreserved s (edNegHook edNeg s) ∧ PoolPreserved s (edNegHook edNeg s) := by
  unfold edNegHook returnToLinkRegister
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

private def masterEdNegGenSpec
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s0 =>
    ⌜s0.readReg64 .x0 = inA ∧ s0.readReg64 .x8 = ret⌝ ∗
      (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ⌜EdNegStatePreserved s0 sf⌝ ∗
      (inA ↦ₛ v.toList) ∗ (ret ↦ₛ (edNeg v).toList)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem edNegHook_masterEdNegGen_ok
    (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) :
    HookOk (edNegHook edNeg) (masterEdNegGenSpec edNeg) := by
  rw [edNegHook_eq_retHook]
  refine retHook_ok fun ⟨inA, v, ret⟩ R s0 _ hpre _ => ?_
  dsimp only [masterEdNegGenSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hmem⟩ := hpre
  subst hx0; subst hx8
  have hv_len : v.toList.length = 160 := List.Vector.toList_length v
  have hin_read : s0.mem.readBytes (s0.readReg64 .x0) 160 = v.toList := by
    have hsat_in : s0.mem ⊨ (s0.readReg64 .x0 ↦ₛ v.toList) ∗ (memRegion (s0.readReg64 .x8) 160 ∗ R) :=
      Satisfies.mono (by sep_entail) hmem
    have hr := ((IsBlock.pointsToBytes (s0.readReg64 .x0) v.toList).read hsat_in).2
    rwa [hv_len] at hr
  have hvec : readVecN s0.mem (s0.readReg64 .x0) 160 = v :=
    Subtype.ext hin_read
  let outBs := (edNeg v).toList
  have hout_len : outBs.length = 160 := List.Vector.toList_length (edNeg v)
  have hout_le : outBs.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  have hmem_ret : s0.mem ⊨
      memRegion (s0.readReg64 .x8) outBs.length ∗ ((s0.readReg64 .x0 ↦ₛ v.toList) ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono (by sep_entail) hmem
  rw [hvec]
  refine ⟨keepsFrozen_writeBytes_of_memRegion outBs hout_le hmem_ret,
    rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [masterEdNegGenSpec, retHook]
  change s0.mem.writeBytes (s0.readReg64 .x8) outBs ⊨
    (⌜EdNegStatePreserved s0 s0⌝ ∗
      (s0.readReg64 .x0 ↦ₛ v.toList) ∗ (s0.readReg64 .x8 ↦ₛ outBs)) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨EdNegStatePreserved.refl s0, ?_⟩
  exact Satisfies.mono (by sep_entail) (satisfies_writeBytes outBs hout_le hmem_ret)

theorem edNegHook_masterEdNeg_ok :
    HookOk (edNegHook dalekEdNegVec) masterEdNegSpec :=
  edNegHook_masterEdNegGen_ok dalekEdNegVec

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterEdNegSpec` -/

/-- Lift `SpecSimulates spec1 spec2` from `subroutine_ok` to `HookOk`. -/
private theorem hookOk_of_specSimulates {α β : Type} {f : State → State}
    {spec1 : Spec α} {spec2 : Spec β}
    (hsim : SpecSimulates spec1 spec2)
    (hh : HookOk f spec1) :
    HookOk f spec2 := by
  intro y R s0 hrun hpre hsp
  obtain ⟨x, R', hpre1, houtMap⟩ := hsim y R s0 hpre
  obtain ⟨hkf, hsym, hout1⟩ := hh x R' s0 hrun hpre1 hsp
  exact ⟨hkf, hsym, houtMap (f s0) hout1⟩

private theorem hookOk_drop_keepsFs {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f (keepsFs spec)) :
    HookOk f spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · dsimp only [keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inl ⟨hret, hcc, hpost.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem hookOk_edNegUnstackedFalse_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (keepsFs (edwardsPointNegUnstackedSpec false)) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun ⟨_, _, _⟩ _ => by
      dsimp only [keepsFs, edwardsPointNegUnstackedSpec, masterEdNegSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun ⟨inA, v, _⟩ _ _ => ?_)
  dsimp only [masterEdNegSpec, keepsFs, edwardsPointNegUnstackedSpec]
  rw [inputAfter_false, sepConj_emp]
  exact Entails.pure_left fun hst =>
    Entails.pure_right hst.1 (Entails.pure_right hst.2.1 (Entails.refl _))

theorem hookOk_edNegUnstackedFalse_of_master {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (edwardsPointNegUnstackedSpec false) :=
  hookOk_drop_keepsFs (hookOk_edNegUnstackedFalse_keepsFs_of_master hh)

theorem hookOk_edNegUnstacked_keepsFs_of_master (byVal : Bool) {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (keepsFs (edwardsPointNegUnstackedSpec byVal)) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun ⟨_, _, _⟩ _ => by
      dsimp only [keepsFs, edwardsPointNegUnstackedSpec, masterEdNegSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun ⟨inA, v, _⟩ _ _ => ?_)
  dsimp only [masterEdNegSpec, keepsFs, edwardsPointNegUnstackedSpec]
  rw [sepConj_emp]
  refine Entails.pure_left fun hst => Entails.pure_right hst.1 (Entails.pure_right hst.2.1 ?_)
  cases byVal
  · rw [inputAfter_false]; exact Entails.refl _
  · rw [inputAfter_true]
    have hent : (inA ↦ₛ v.toList) ⊢ memRegion inA 160 := by
      simpa [List.Vector.toList_length v] using pointsToBytes_entails_memRegion inA v.toList
    exact sepConj_mono_left hent

theorem hookOk_edNegUnstacked_of_master (byVal : Bool) {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (edwardsPointNegUnstackedSpec byVal) :=
  hookOk_drop_keepsFs (hookOk_edNegUnstacked_keepsFs_of_master byVal hh)

private theorem hookOk_withStack_keepsFs {α : Type} {f : State → State} {spec : Spec α}
    (hookStack : Nat) (hh : HookOk f (keepsFs spec))
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (keepsFs (withStack spec hookStack)) := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp hookStack) hh
    (fun _ _ => by dsimp only [keepsFs, withStack]; sep_entail)
    (fun _ s0 sf => ?_)
    (fun x s0 sf => hpan x s0 sf)
    (fun x code s0 sf => hex x code s0 sf)
    (fun x s0 sf => hoom x s0 sf)
  dsimp only [keepsFs, withStack]
  rw [sepConj_assoc]
  exact Entails.pure_left fun hfs => Entails.pure_right hfs (by sep_entail)

theorem hookOk_edNegPureByteFunction_keepsFs_of_master (byVal : Bool) {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (keepsFs (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  hookOk_withStack_keepsFs extHookStack (hookOk_edNegUnstacked_keepsFs_of_master byVal hh)

theorem hookOk_edNegPureByteFunction_of_master (byVal : Bool) {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (pureByteFunctionSpec dalekEdNegVec byVal) :=
  hookOk_drop_keepsFs (hookOk_edNegPureByteFunction_keepsFs_of_master byVal hh)

theorem hookOk_edNegCryptoLeafStub_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f
      (keepsFs (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  hookOk_of_specSimulates unstacked_simulates_real_cryptoLeafStubSpec
    (hookOk_withStack_keepsFs pqxdhHookStack (hookOk_edNegUnstackedFalse_keepsFs_of_master hh))

theorem hookOk_edNegCryptoLeafStub_of_master {f : State → State}
    (hh : HookOk f masterEdNegSpec) :
    HookOk f (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160) :=
  hookOk_drop_keepsFs (hookOk_edNegCryptoLeafStub_keepsFs_of_master hh)

/-! ## 5. `S2Frame` Elimination for `edwardsPointNegUnstackedSpec false` (`Hole3W3VerifySigAux`) -/

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode
