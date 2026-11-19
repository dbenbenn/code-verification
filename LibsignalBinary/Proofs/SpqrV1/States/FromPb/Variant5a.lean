/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 5 (`NoHeaderReceived`, `+1344`) — Part A

OOM cold path (`+11596`), shared `+6500` error exit, inline `ProtoPolynomialDecoder`
deallocation (`+6420..+6500`), and protobuf unpacking helpers for `NoHeaderReceived`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

theorem v5a_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v5a_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v5a_sepWPp_call_ret {α : Type} {prog : Program}
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

theorem v5a_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v5a_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v5a_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v5a_optProtoInnerStateAt_noHeaderReceived (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.NoHeaderReceived) :
    optProtoInnerStateAt A pbA (some (.noHeaderReceived s)) =
      (pbA ↦₆₄ 0x8000000000000005#64) ∗
      optProtoPolynomialDecoderAt A (pbA + 8#64) (s.receivingHdr.map pbToProtoPolyDecoder) ∗
      optProtoUnchunkedNoHeaderReceivedAt A (pbA + 48#64) s.uc ∗
      memRegion (pbA + 104#64) 120 := by
  have h48 : pbA + 8#64 + 40#64 = pbA + 48#64 := by bv_omega
  simp only [optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedNoHeaderReceivedAt, h48, sepConj_assoc]

@[simp]
theorem v5a_spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

theorem v5a_states_from_pb_noHeaderReceived_ptsNeeded_ne (F : ShaCompress)
    (d : PolynomialDecoder) (uc : Option V1State.Unchunked.NoHeaderReceived)
    (hne : (d.ptsNeeded == 48#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := uc, receivingHdr := some d }) } =
      .error (.err .msgDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = true := by
    simpa [bne] using hne
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_uc_none_dec_none (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := none, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_uc_none_dec_some (F : ShaCompress)
    (d : PolynomialDecoder) (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived { uc := none, receivingHdr := some d }) } =
      .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_none_dec_none (F : ShaCompress)
    (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := none, epoch := ep }, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_none_dec_some (F : ShaCompress)
    (ep : BitVec 64) (d : PolynomialDecoder) (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := none, epoch := ep }, receivingHdr := some d }) } =
      .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
    Unchunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_some_dec_none (F : ShaCompress)
    (authPb : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := some authPb, epoch := ep }, receivingHdr := none }) } =
      .error (.err .stateDecode) := rfl

theorem v5a_states_from_pb_noHeaderReceived_auth_some_dec_some (F : ShaCompress)
    (authPb : ProtoAuthenticator) (ep : BitVec 64) (d : PolynomialDecoder)
    (heq : (d.ptsNeeded == 48#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.noHeaderReceived
          { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some d }) } =
      match decoderFromPbResult (pbToProtoPolyDecoder d) with
      | .ok dec =>
        .ok (.noHeaderReceived
          { uc := { auth := Authenticator.fromPb authPb, epoch := ep }
            receiving_hdr := dec })
      | .error _ => .error (.err .stateDecode) := by
  dsimp only [States.from_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
    Unchunked.SendCt.NoHeaderReceived.from_pb]
  have hne' : (d.ptsNeeded != 48#32) = false := by
    simpa [bne] using heq
  erw [hne']
  simp only [Bool.false_eq_true, ↓reduceIte,
    v5a_spqrAuthApi_from_pb, decoderFromPbStateDecode_some,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases decoderFromPbResult (pbToProtoPolyDecoder d) <;> rfl

/-! ## Shared Error Exit at `+6500` & `ProtoPolynomialDecoder` Deallocation Loop (`+6420..+6500`) -/

theorem v5a_memRegion_2304_split_216 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 216 ∗
      (∃∗ w216 : BitVec 64, ((fsp + 216#64) ↦₆₄ w216)) ∗
      memRegion (fsp + 224#64) 2080 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v5a_memRegion_2304_join_216 (fsp w216 : BitVec 64) :
    memRegion fsp 216 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ memRegion (fsp + 224#64) 2080 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

@[expose, reducible]
def v5a_Saved6428Preserved (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x22 = ptsPtr ∧
  s.readReg64 .x23 = ptsCap ∧
  s.readReg64 .x27 = x27_val ∧
  TraceCalleeSaved s s0

theorem v5a_ptsCap_add_one_ne_zero {ptsCap : BitVec 64} (h : ptsCap.toNat * 24 < 2 ^ 63) :
    ¬((ptsCap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h1 : (ptsCap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

@[expose] def v5a_optProtoPolyDecoderWordsAt (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗ ((a + 32#64) ↦₆₄ w32)

theorem v5a_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v5a_byte_pad7_entails_64 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜EncoderFromPb.loByte w = b⌝ ∗ (a ↦₆₄ w) := by
  have hsplit : memRegion (a + 1#64) 7 ⊢
      (∃∗ d1 : BitVec 32, ((a + 1#64) ↦₃₂ d1)) ∗
      (∃∗ h5 : BitVec 16, ((a + 5#64) ↦₁₆ h5)) ∗
      (∃∗ b7 : BitVec 8, ((a + 7#64) ↦₈ b7)) := by
    exact split_top <|
      split_step (mem32_entails _) <|
      split_step (mem16_entails _) <|
      mem8_entails _
  refine Entails.trans (sepConj_mono_right hsplit) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro h5
  apply Entails.sepExists_elim; intro d1
  let w : BitVec 64 := b7 ++ h5 ++ d1 ++ b
  refine Entails.sepExists_right w ?_
  have hw0 : w.extractLsb' 0 8 = b := by dsimp [w]; bv_kernel
  have hw1 : w.extractLsb' 8 32 = d1 := by dsimp [w]; bv_kernel
  have hw5 : w.extractLsb' 40 16 = h5 := by dsimp [w]; bv_kernel
  have hw7 : w.extractLsb' 56 8 = b7 := by dsimp [w]; bv_kernel
  have hlo : EncoderFromPb.loByte w = b := hw0
  refine Entails.pure_right hlo ?_
  rw [v5a_pointsTo64_split_1_4_2_1 a w, hw0, hw1, hw5, hw7]
  exact Entails.refl _

theorem v5a_pointsTo64_entails_byte_pad7 (a w : BitVec 64) (b : BitVec 8)
    (hw : EncoderFromPb.loByte w = b) :
    (a ↦₆₄ w) ⊢ (a ↦₈ b) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_split_1_7 a w, hw]
  exact sepConj_mono_right
    (EncoderFromPb.length_hiBytes7 w ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) (EncoderFromPb.hiBytes7 w))

@[expose] def v5a_optProtoPolyDecoderHeap (A : RustAlloc) :
    Option ProtoPolynomialDecoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 32 → BitVec 32 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, d24, d28, w32 =>
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (if w0 = 0#64 then emp
     else A.live w8 (w0.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
       memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))

theorem v5a_optProtoPolyDecoderWordsAt_entails_40
    (a w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ⊢ memRegion a 40 := by
  unfold v5a_optProtoPolyDecoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion a w0) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 8#64) w8) <|
    collapse_step (Drop.pointsTo64_entails_memRegion (a + 16#64) w16) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 24#64) d24) <|
    collapse_step (pointsTo32_entails_memRegion_4 (a + 28#64) d28) <|
    Drop.pointsTo64_entails_memRegion (a + 32#64) w32

theorem v5a_optProtoPolyDecoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A a optDec ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ d24 : BitVec 32, ∃∗ d28 : BitVec 32, ∃∗ w32 : BitVec 64,
        v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
        v5a_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 := by
  cases optDec with
  | none =>
    dsimp only [optProtoPolynomialDecoderAt, optProtoPolynomialDecoderNoneTailSize,
      v5a_optProtoPolyDecoderHeap]
    have hsplit : memRegion (a + 8#64) 32 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ d24 : BitVec 32, (a + 24#64) ↦₃₂ d24) ∗
        (∃∗ d28 : BitVec 32, (a + 28#64) ↦₃₂ d28) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem32_entails _) <| split_step (mem32_entails _) <|
        mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro d28
    apply Entails.sepExists_elim; intro d24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right d24
        (Entails.sepExists_right d28 (Entails.sepExists_right w32 ?_)))))
    unfold v5a_optProtoPolyDecoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optProtoPolynomialDecoderAt protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
      vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
      protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
      protoPolynomialDecoderPadSize Poly.vecHeaderBytes
    have h33 : a + 0x21#64 = (a + 32#64) + 1#64 := by bv_omega
    rw [h33]
    have h8_64 := v5a_byte_pad7_entails_64 (a + 32#64) (boolByte pb.isComplete)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro c1
    apply Entails.sepExists_elim; intro p1
    refine Entails.trans
      (Entails.of_eq (show _ =
        ⌜pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧ p1 ≠ 0#64⌝ ∗
        ((((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion ((a + 32#64) + 1#64) 7) ∗
         ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
          (if c1 = 0#64 then emp
           else A.live p1 (c1.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 p1 pb.pts ∗
             memRegion (p1 + BitVec.ofNat 64 (pb.pts.length * 24)) ((c1.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨hle, hcap, hp_ne⟩
    refine Entails.trans (sepConj_mono_left h8_64) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w32
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hw32
    refine Entails.sepExists_right c1 (Entails.sepExists_right p1
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right pb.ptsNeeded
          (Entails.sepExists_right pb.polys
            (Entails.sepExists_right w32 ?_)))))
    dsimp only [v5a_optProtoPolyDecoderWordsAt, v5a_optProtoPolyDecoderHeap]
    refine Entails.trans
      (Entails.pure_right
        (φ := BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
          pb.ptsNeeded = pb.ptsNeeded ∧ pb.polys = pb.polys ∧
          pb.pts.length ≤ c1.toNat ∧ c1.toNat * 24 < 2 ^ 63 ∧
          p1 ≠ 0#64 ∧ EncoderFromPb.loByte w32 = boolByte pb.isComplete)
        ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩ (Entails.refl _)) ?_
    exact Entails.of_eq (by ac_rfl)

theorem v5a_protoPolyDecoderAt_pack (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v5a_optProtoPolyDecoderWordsAt a w0 w8 w16 d24 d28 w32 ∗
      v5a_optProtoPolyDecoderHeap A (some pb) w0 w8 w16 d24 d28 w32 ⊢
    protoPolynomialDecoderAt A a pb := by
  dsimp only [v5a_optProtoPolyDecoderWordsAt, v5a_optProtoPolyDecoderHeap]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧
      w8 ≠ 0#64 ∧
      EncoderFromPb.loByte w32 = boolByte pb.isComplete⌝ ∗
    (((a + 32#64) ↦₆₄ w32) ∗
     ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₃₂ d24) ∗ ((a + 28#64) ↦₃₂ d28) ∗
      (if w0 = 0#64 then emp
       else A.live w8 (w0.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
         memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24)))) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  unfold protoPolynomialDecoderAt vecVecU8At vecOf vecAt vecHeader
    vecBuf protoPolynomialDecoderPtsNeededOff protoPolynomialDecoderPolysOff
    protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
    protoPolynomialDecoderPadSize Poly.vecHeaderBytes
  have hcell32 := v5a_pointsTo64_entails_byte_pad7 (a + 32#64) w32 (boolByte pb.isComplete) hw32
  have h33 : (a + 32#64) + 1#64 = a + 0x21#64 := by bv_omega
  rw [h33] at hcell32
  refine Entails.trans (sepConj_mono_left hcell32) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length)) ∗
     (if w0 = 0#64 then emp
      else A.live w8 (w0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 pb.pts ∗
        memRegion (w8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((w0.toNat - pb.pts.length) * 24))) ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (a + 0x21#64) 7 by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)
  exact Entails.trans
    (Entails.pure_right (φ := pb.pts.length ≤ w0.toNat ∧ w0.toNat * 24 < 2 ^ 63 ∧ w8 ≠ 0#64)
      ⟨hle, hcap, hp_ne⟩ (Entails.refl _))
    (Entails.of_eq (by ac_rfl))

/-- The 7 64-bit words of `Option<ProtoUnchunkedNoHeaderReceived>` at `a` (`56` bytes). -/
@[expose] def v5a_optProtoUcWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

theorem v5a_optProtoUcWordsAt_entails_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v5a_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 ⊢ memRegion a 56 := by
  unfold v5a_optProtoUcWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

@[expose] def v5a_vecU8Heap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) : SepProp :=
  ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Payload A cap ptr bs

theorem v5a_vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len)) ∗
        v5a_vecU8Heap A bs cap ptr len := by
  unfold vecU8 v5a_vecU8Heap
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_header_payload A a cap ptr bs]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v5a_vecU8Heap_entails_dealloc (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v5a_vecU8Heap A bs cap ptr len ⊢
      ⌜len = BitVec.ofNat 64 bs.length ∧
        bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecCapPtrDealloc A cap ptr := by
  unfold v5a_vecU8Heap vecU8Payload vecCapPtrDealloc
  apply Entails.pure_left; intro hlen
  apply Entails.pure_left; rintro ⟨hle, hcap, hp⟩
  refine Entails.pure_right ⟨hlen, hle, hcap, hp⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion ptr bs
    have hadd : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        memRegion ptr cap.toNat := by
      rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

/-- Address-independent heap and pure constraints for `Option<ProtoUnchunkedNoHeaderReceived>`. -/
@[expose] def v5a_optProtoUcHeap (A : RustAlloc) :
    Option V1State.Unchunked.NoHeaderReceived →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = none2Cap⌝
  | some { auth := none, epoch := ep }, w0, _, _, _, _, _, w48 =>
    ⌜w0 = noneCap ∧ w48 = ep⌝
  | some { auth := some authPb, epoch := ep }, w0, w8, w16, w24, w32, w40, w48 =>
    ⌜w48 = ep⌝ ∗
    v5a_vecU8Heap A authPb.rootKey w0 w8 w16 ∗
    v5a_vecU8Heap A authPb.macKey w24 w32 w40

theorem v5a_optProtoUcAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optUc : Option V1State.Unchunked.NoHeaderReceived) :
    optProtoUnchunkedNoHeaderReceivedAt A a optUc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        v5a_optProtoUcWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v5a_optProtoUcHeap A optUc w0 w8 w16 w24 w32 w40 w48 := by
  cases optUc with
  | none =>
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt, v5a_optProtoUcHeap]
    have hsplit : memRegion (a + 8#64) 48 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right none2Cap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 ?_))))))
    unfold v5a_optProtoUcWordsAt
    exact Entails.trans (Entails.pure_right (rfl : none2Cap = none2Cap) (Entails.refl _))
      (Entails.of_eq (by ac_rfl))
  | some uc =>
    rcases uc with ⟨ep, optAuth⟩
    cases optAuth with
    | none =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt,
        optProtoAuthenticatorAt, v5a_optProtoUcHeap]
      have hsplit : memRegion (a + 8#64) 40 ⊢
          (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
          (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
          (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
          (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
          (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) := by
        exact split_top <|
          split_step (mem64_entails _) <| split_step (mem64_entails _) <|
          split_step (mem64_entails _) <| split_step (mem64_entails _) <|
          mem64_entails _
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right hsplit)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply Entails.sepExists_elim; intro w40
      apply Entails.sepExists_elim; intro w32
      apply Entails.sepExists_elim; intro w24
      apply Entails.sepExists_elim; intro w16
      apply Entails.sepExists_elim; intro w8
      refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
        (Entails.sepExists_right w16 (Entails.sepExists_right w24
          (Entails.sepExists_right w32 (Entails.sepExists_right w40
            (Entails.sepExists_right ep ?_))))))
      unfold v5a_optProtoUcWordsAt
      exact Entails.trans
        (Entails.pure_right (⟨rfl, rfl⟩ : noneCap = noneCap ∧ ep = ep) (Entails.refl _))
        (Entails.of_eq (by ac_rfl))
    | some authPb =>
      dsimp only [optProtoUnchunkedNoHeaderReceivedAt, protoUnchunkedNoHeaderReceivedAt,
        optProtoAuthenticatorAt, protoAuthenticatorAt, v5a_optProtoUcHeap]
      refine Entails.trans
        (sepConj_mono_left
          (sepConj_mono (v5a_vecU8_unpack A a authPb.rootKey)
            (v5a_vecU8_unpack A (a + 24#64) authPb.macKey))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        BitVec.add_assoc, BitVec.reduceAdd]
      apply Entails.sepExists_elim; intro w24
      apply Entails.sepExists_elim; intro w32
      apply Entails.sepExists_elim; intro w40
      apply Entails.sepExists_elim; intro w0
      apply Entails.sepExists_elim; intro w8
      apply Entails.sepExists_elim; intro w16
      refine Entails.sepExists_right w0 (Entails.sepExists_right w8
        (Entails.sepExists_right w16 (Entails.sepExists_right w24
          (Entails.sepExists_right w32 (Entails.sepExists_right w40
            (Entails.sepExists_right ep ?_))))))
      unfold v5a_optProtoUcWordsAt
      exact Entails.trans
        (Entails.pure_right (rfl : ep = ep) (Entails.refl _))
        (Entails.of_eq (by ac_rfl))

/-- All 224 bytes of `pbA` when `pbA + 8..48` and `pbA + 48..104` are unpacked into words. -/
@[expose] def v5a_pbAHeadersAt (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) : SepProp :=
  (pbA ↦₆₄ 0x8000000000000005#64) ∗
  v5a_optProtoPolyDecoderWordsAt (pbA + 8#64) w8 w16 w24 d32 d36 w40 ∗
  v5a_optProtoUcWordsAt (pbA + 48#64) w48 w56 w64 w72 w80 w88 w96 ∗
  memRegion (pbA + 104#64) 120

theorem v5a_pbAHeadersAt_eq (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 =
      (pbA ↦₆₄ 0x8000000000000005#64) ∗
      ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗ ((pbA + 24#64) ↦₆₄ w24) ∗
      ((pbA + 32#64) ↦₃₂ d32) ∗ ((pbA + 36#64) ↦₃₂ d36) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
      ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
      ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗ ((pbA + 88#64) ↦₆₄ w88) ∗
      ((pbA + 96#64) ↦₆₄ w96) ∗
      memRegion (pbA + 104#64) 120 := by
  unfold v5a_pbAHeadersAt v5a_optProtoPolyDecoderWordsAt v5a_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem v5a_pbAHeadersAt_entails_224 (pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ⊢
      memRegion pbA optProtoInnerStateSize := by
  unfold v5a_pbAHeadersAt
  dsimp only [optProtoInnerStateSize]
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (v5a_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    collapse_step (v5a_optProtoUcWordsAt_entails_56 _ _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v5a_optProtoInnerStateAt_unpack (A : RustAlloc) (pbA : BitVec 64)
    (s : V1State.Chunked.NoHeaderReceived) :
    optProtoInnerStateAt A pbA (some (.noHeaderReceived s)) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ d32 : BitVec 32, ∃∗ d36 : BitVec 32, ∃∗ w40 : BitVec 64,
      ∃∗ w48 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64,
        v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A (s.receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
        v5a_optProtoUcHeap A s.uc w48 w56 w64 w72 w80 w88 w96 := by
  rw [v5a_optProtoInnerStateAt_noHeaderReceived A pbA s]
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono_left (v5a_optProtoPolyDecoderAt_unpack A (pbA + 8#64) (s.receivingHdr.map pbToProtoPolyDecoder)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro d32
  apply Entails.sepExists_elim; intro d36
  apply Entails.sepExists_elim; intro w40
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v5a_optProtoUcAt_unpack A (pbA + 48#64) s.uc))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w48
  apply Entails.sepExists_elim; intro w56
  apply Entails.sepExists_elim; intro w64
  apply Entails.sepExists_elim; intro w72
  apply Entails.sepExists_elim; intro w80
  apply Entails.sepExists_elim; intro w88
  apply Entails.sepExists_elim; intro w96
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right d32
      (Entails.sepExists_right d36 (Entails.sepExists_right w40
        (Entails.sepExists_right w48 (Entails.sepExists_right w56
          (Entails.sepExists_right w64 (Entails.sepExists_right w72
            (Entails.sepExists_right w80 (Entails.sepExists_right w88
              (Entails.sepExists_right w96 ?_))))))))))))
  unfold v5a_pbAHeadersAt
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
