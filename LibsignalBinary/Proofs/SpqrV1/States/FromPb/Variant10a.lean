/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Error & Cleanup Paths

Proves stack/OOM (`+11572`) helpers, shared error epilogues at `+2084` and `+2064` (dropping
`sending_ct2`), error-cleanup deallocation paths at `+5844`, `+7236`, `+7212`, and `+5820` for
cloned `Authenticator` buffers, and `ProtoPolynomialEncoder` capacity-exposure helpers.
-/

namespace CryptoVerification.Swarm.IC10.Variant10a

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Alloc

namespace V10Alloc

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

end V10Alloc

end CryptoVerification.Swarm.IC10.Variant10a

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.Swarm.IC10.Variant10a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. General WPp, Stack, & OOM Helpers -/

theorem v10_fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

private theorem v10_add_2080_sub_58308_eq (x : BitVec 64) :
    x + 2080#64 + 0xffffffffffff1c3c#64 = x - 56228#64 := by bv_omega

theorem v10_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v10_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v10_sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v10_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v10_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_encoderFromPbStack_to_dropStack48 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v10_stackAt_dropStack48_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Pure condition on the exposed `cap` word at `d` of `optProtoPolynomialEncoderAt A d m`. -/
@[expose] def v10_optEncoderCapProp (cap : BitVec 64) : Option ProtoPolynomialEncoder → Prop
  | none => cap = noneCap
  | some _ => cap.toNat < 2 ^ 63

/-- Remainder of `optProtoPolynomialEncoderAt A d m` after splitting out `d ↦₆₄ cap`. -/
@[expose] def v10_optProtoPolyEncoderTail (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) : SepProp :=
  match m with
  | none => ⌜cap = noneCap⌝ ∗ memRegion (d + 8#64) 48
  | some pb =>
    ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      protoPolynomialEncoderRestAt A d cap ptr pb

theorem v10_optProtoPolyEncoder_expose_cap (A : RustAlloc) (d : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A d m ⊢
      ∃∗ cap : BitVec 64,
        ⌜v10_optEncoderCapProp cap m⌝ ∗
        (d ↦₆₄ cap) ∗ v10_optProtoPolyEncoderTail A d cap m := by
  cases m with
  | none =>
    rw [optProtoPolynomialEncoderAt_none']
    refine Entails.sepExists_right noneCap ?_
    unfold v10_optEncoderCapProp v10_optProtoPolyEncoderTail
    refine Entails.pure_right rfl ?_
    exact sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some']
    refine Entails.trans (protoPolynomialEncoderAt_expose_cap A d pb) ?_
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro hlt
    refine Entails.sepExists_right cap ?_
    unfold v10_optEncoderCapProp v10_optProtoPolyEncoderTail
    refine Entails.pure_right hlt ?_
    refine Entails.trans ?_
      (sepConj_mono_right (Entails.sepExists_right ptr (Entails.pure_right hlt (Entails.refl _))))
    exact Entails.of_eq (by ac_rfl)

theorem v10_optProtoPolyEncoder_unexpose_cap (A : RustAlloc) (d cap : BitVec 64)
    (m : Option ProtoPolynomialEncoder) :
    (d ↦₆₄ cap) ∗ v10_optProtoPolyEncoderTail A d cap m ⊢
      optProtoPolynomialEncoderAt A d m := by
  cases m with
  | none =>
    unfold v10_optProtoPolyEncoderTail
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro hcap
    subst hcap
    rw [optProtoPolynomialEncoderAt_none']
    exact Entails.refl _
  | some pb =>
    unfold v10_optProtoPolyEncoderTail
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [optProtoPolynomialEncoderAt_some']
    exact protoPolynomialEncoderAt_unexpose_cap A d cap ptr pb

theorem v10_fsp_split_192 (fsp : BitVec 64) :
    memRegion (fsp + 8#64) 2296 ⊢
      memRegion (fsp + 8#64) 184 ∗
      (∃∗ v_sp192 : BitVec 64, (fsp + 192#64) ↦₆₄ v_sp192) ∗
      memRegion (fsp + 200#64) 2104 := by
  rw [ProofLib.memRegion_split' (b := fsp + 8#64) (n := 184) (k := 2112)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 2104)
        (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 192#64)]
  exact Entails.refl _

theorem v10_fsp_unsplit_192 (fsp v0 v192 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗
      memRegion (fsp + 8#64) 184 ∗
      ((fsp + 192#64) ↦₆₄ v192) ∗
      memRegion (fsp + 200#64) 2104 ⊢
      memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 184) (k := 2112)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 2104)
        (b' := fsp + 200#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion fsp v0)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 192#64) v192)))

theorem v10_pb_64_none_entails_160 (pbA : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ none2Cap) ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion (pbA + 64#64) 160 := by
  rw [ProofLib.memRegion_split' (b := pbA + 64#64) (n := 8) (k := 152)
        (b' := pbA + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 72#64) (n := 48) (k := 104)
        (b' := pbA + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (pbA + 64#64) none2Cap)

theorem v10_pb_64_auth_none_entails_160 (pbA epoch : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 72#64) 40 ∗
      ((pbA + 112#64) ↦₆₄ epoch) ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion (pbA + 64#64) 160 := by
  rw [ProofLib.memRegion_split' (b := pbA + 64#64) (n := 8) (k := 152)
        (b' := pbA + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 72#64) (n := 40) (k := 112)
        (b' := pbA + 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := pbA + 112#64) (n := 8) (k := 104)
        (b' := pbA + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (pbA + 64#64) noneCap)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (pbA + 112#64) epoch)))

theorem v10_pb_tag_56_160_entails_224 (pbA tag : BitVec 64) :
    (pbA ↦₆₄ tag) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160 ⊢
      memRegion pbA optProtoInnerStateSize := by
  dsimp only [optProtoInnerStateSize]
  rw [ProofLib.memRegion_split pbA 8 216 (by decide),
      ProofLib.memRegion_split' (b := pbA + 8#64) (n := 56) (k := 160)
        (b' := pbA + 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA tag)

end CryptoVerification.SpqrV1.States.FromPb
