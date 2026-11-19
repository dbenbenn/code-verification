/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainResolve
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.States CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.States.Leaves

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff /-! ## 1. Callee Relative Addresses -/
private theorem stackAt_callee_split (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide) :
    stackAt sp spqrSendCalleeStack = memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

private theorem panic_frame_anyHeap {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) : m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) := Entails.of_eq (by ac_rfl)
  have hm' := Satisfies.mono h1 hm; rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

private theorem panic_not_exited {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False := ((satisfies_pure_sepConj _ _ _).mp h).1

theorem pure_elim_focus_b1 {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P' Q Qp)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp := by
  rw [hf]
  exact SepWPp.pure_left h

theorem sepWPp_at_panic_stub {prog : Program} {ret : BitVec 64}
    {s : State} {P Fr : SepProp} {Q : State → SepProp → Prop} {φ_out : State → Prop}
    (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked) (hφ : φ_out (Rust.panicked s)) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  intro R' hm hL
  have hstep : Step prog s (Rust.panicked s) := Step.extern hrun hext (Memory.KeepsFrozen.refl s.mem) rfl
  have hmem : (Rust.panicked s).mem ⊨ (⌜φ_out (Rust.panicked s)⌝ ∗ anyHeap) ∗ R' :=
    Satisfies.mono (sepConj_mono_left (Entails.pure_right hφ (entails_anyHeap P))) hm
  exact ⟨Rust.panicked s, Steps.step hstep (Steps.refl _), Or.inr (Or.inl ⟨rfl, ⌜φ_out (Rust.panicked s)⌝ ∗ anyHeap, hmem, id⟩)⟩

@[expose] def sendResolveChain (hkdf : HkdfFn) (chain : Option ChainPB) (vn : Option VersionNegotiationPB) : SpqrApiResult (Option Chain) :=
  match chain with
  | none => match vn with
    | some v => if BitVec.slt Version.v0.toI32 v.minVersion then do
        let c ← SpqrApiResult.ofError (chainFromVersionNegotiation hkdf v); pure (some c)
      else pure none
    | none => .error (.err .chainNotAvailable)
  | some pb => do let c ← SpqrApiResult.ofError (Chain.fromPb pb); pure (some c)

@[expose] def sendStepChain (hkdf : HkdfFn) (chain : Option Chain) (key : Option EpochSecret) (epoch : BitVec 64) :
    SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) :=
  match chain with
  | none => if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB)) else .error (.panic .sendKeySomeWithoutChain)
  | some chain0 => do
    let chain1 ← match key with | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret) | none => pure chain0
    if epoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
      let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64)); pure (idx, mk, some chain2.intoPb)

@[expose] def sendChainPhase (hkdf : HkdfFn) (chain : Option ChainPB) (vn : Option VersionNegotiationPB)
    (key : Option EpochSecret) (epoch : BitVec 64) : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) := do
  let ch ← sendResolveChain hkdf chain vn; sendStepChain hkdf ch key epoch

theorem sendAfterStates_eq_bind_sendChainPhase (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB) (msg : D.MessageV1) (key : Option EpochSecret) (state : D.States) :
    sendAfterStates D hkdf statePb msg key state =
      match sendChainPhase hkdf statePb.chain statePb.versionNegotiation key (D.msgEpoch msg) with
      | .error e => .error e
      | .ok (index, msgKey, chainPb) =>
        let msgBytes := D.msgSerialize msg index
        match msgBytes with
        | [] => .error (.panic .sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then .error (.panic .sendMsgBadVersion)
          else .ok { state := D.encodeState { inner := some (D.statesIntoPb state), versionNegotiation := statePb.versionNegotiation, chain := chainPb },
                     msg := msgBytes, key := if msgKey.isEmpty then none else some msgKey } := by
  unfold sendAfterStates sendChainPhase sendResolveChain sendStepChain
  cases statePb.chain with
  | none =>
    cases statePb.versionNegotiation with
    | none => rfl
    | some v =>
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]; split
      · rcases SpqrApiResult.ofError (chainFromVersionNegotiation hkdf v) with _ | c
        · rfl
        · dsimp only; rcases key with _ | es <;> dsimp only
          · split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
          · rcases SpqrApiResult.ofChainPanic (c.addEpoch hkdf es) with _ | c1
            · rfl
            · dsimp only; split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
      · dsimp only; split <;> rfl
  | some pb =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rcases SpqrApiResult.ofError (Chain.fromPb pb) with _ | c
    · rfl
    · dsimp only; rcases key with _ | es <;> dsimp only
      · split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]
      · rcases SpqrApiResult.ofChainPanic (c.addEpoch hkdf es) with _ | c1
        · rfl
        · dsimp only; split <;> [rfl; (rcases SpqrApiResult.ofChainResult _ with _ | ⟨_, _, _⟩ <;> rfl)]

theorem sendResolveChain_raw_le (hkdf : HkdfFn) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) {c : Chain} (h : sendResolveChain hkdf chain vn = .ok (some c)) :
    Top.StateSize.rawChain c.intoPb ≤ Top.StateSize.optRaw Top.StateSize.rawChain chain + 296 := by
  unfold sendResolveChain at h; cases chain with
  | none =>
    cases vn with
    | none => contradiction
    | some v =>
      dsimp only at h; split at h
      · rcases Top.StateSize.except_bind_eq_ok h with ⟨c', hc', heq⟩
        rw [SpqrApiResult.ofError_eq_ok] at hc'; have hc_eq := Option.some.inj (Except.ok.inj heq); subst hc_eq
        have hle := Top.StateSize.chainFromVersionNegotiation_raw_le hkdf v hc'; simp only [Top.StateSize.optRaw_none]; omega
      · nomatch h
  | some pb =>
    dsimp only at h; rcases Top.StateSize.except_bind_eq_ok h with ⟨c', hc', heq⟩
    rw [SpqrApiResult.ofError_eq_ok] at hc'; have hc_eq := Option.some.inj (Except.ok.inj heq); subst hc_eq
    have heq_raw := Top.StateSize.Chain.fromPb_raw_eq hc'; simp only [Top.StateSize.optRaw_some]; omega

private theorem vecDequeRingBuf_expose_len_le {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr head : BitVec 64) (xs : List α) :
    vecDequeRingBuf A stride align elem cap ptr head xs ⊢ ⌜xs.length ≤ cap.toNat⌝ ∗ vecDequeRingBuf A stride align elem cap ptr head xs := by
  unfold vecDequeRingBuf; apply Entails.pure_left; intro hpure; exact Entails.pure_right hpure.1 (Entails.pure_right hpure (Entails.refl _))

private theorem vecDequeAt_expose_len_le {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (v cap ptr head : BitVec 64) (xs : List α) :
    vecDequeAt A stride align elem v cap ptr head xs ⊢ ⌜xs.length ≤ cap.toNat⌝ ∗ vecDequeAt A stride align elem v cap ptr head xs := by
  unfold vecDequeAt; refine Entails.trans (sepConj_mono_right (vecDequeRingBuf_expose_len_le A stride align elem cap ptr head xs)) ?_
  rw [← sepConj_assoc, sepConj_comm (vecDequeHeader v cap ptr head (BitVec.ofNat 64 xs.length)), sepConj_assoc]; exact Entails.refl _

theorem chainAt_entails_links_grow_ok (A : RustAlloc) (a : BitVec 64) (G : ChainGhost) (c : Chain) (hbnd : c.links.length ≤ 2 ^ 54) :
    chainAt A a G c ⊢ ⌜c.links.length < G.linksCap.toNat ∨ max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63⌝ ∗ chainAt A a G c := by
  unfold chainAt; apply Entails.pure_left; intro hlen_eq
  refine Entails.trans (sepConj_mono_left (vecDequeAt_expose_len_le A chainEpochSize chainEpochAlign
    (chainEpochAt A) a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links))) ?_
  rw [sepConj_assoc]; apply Entails.pure_left; intro hle_zip
  have hzip_len : (G.epochs.zip c.links).length = c.links.length := by rw [List.length_zip, hlen_eq, Nat.min_self]
  have hle : c.links.length ≤ G.linksCap.toNat := by rwa [hzip_len] at hle_zip
  exact Entails.pure_right (links_len_or_grow_ok hle hbnd) (Entails.pure_right hlen_eq (Entails.refl _))

@[expose] def sendKeyIntoPbChain (hkdf : HkdfFn) (c1 : Chain) (msgEpoch : Epoch) :
    SpqrApiResult (BitVec 32 × Bytes × Option ChainPB) :=
  if msgEpoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
    let (c2, (idx, msgKey)) ← SpqrApiResult.ofChainResult (c1.sendKey hkdf (msgEpoch - 1#64)); pure (idx, msgKey, some c2.intoPb)

private theorem readReg32_of_readReg64_eq {s1 s2 : State} {r : Reg} (h : s1.readReg64 r = s2.readReg64 r) :
    s1.readReg32 r = s2.readReg32 r := by unfold State.readReg32; rw [h]
private theorem flag_preserve {s1 s2 : State}
    (h : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x20 = 0#32)
    (hx20 : s2.readReg64 .x20 = s1.readReg64 .x20) (hx21 : s2.readReg64 .x21 = s1.readReg64 .x21) :
    s2.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s2.readReg32 .x20 = 0#32 :=
  h.imp (hx21.trans ·) ((readReg32_of_readReg64_eq hx20).trans ·)
private theorem flag_of_csinc_315b8 {s : State} {x21 : BitVec 64} (hx21 : s.readReg64 .x21 = x21)
    (hx20 : s.readReg32 .x20 = (if (x21 + 1#64 != 0#64) = true then 0#32 else 1#32)) :
    s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32 := by
  by_cases h : x21 = LibsignalTripleRatchetRepr.noneCap
  · exact Or.inl (hx21.trans h)
  · refine Or.inr (hx20.trans ?_)
    have hne : (x21 + 1#64 != 0#64) = true := by unfold LibsignalTripleRatchetRepr.noneCap at h; simp only [bne_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [hne]
private theorem memRegion_1260_88_eq_32_56 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 32 ∗ memRegion (sp + 0x1280#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 32) (k := 56) (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1260_88_eq_40_48 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 40 ∗ memRegion (sp + 0x1288#64) 48 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 40) (k := 48) (b' := sp + 0x1288#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_80_8 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 80 ∗ memRegion (sp + 0x5e0#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 80) (k := 8) (b' := sp + 0x5e0#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_24_64 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 24 ∗ memRegion (sp + 0x5a8#64) 64 :=
  ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 64) (b' := sp + 0x5a8#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1060_80_eq_24_56 (sp : BitVec 64) :
    memRegion (sp + 0x1060#64) 80 = memRegion (sp + 0x1060#64) 24 ∗ memRegion (sp + 0x1078#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 24) (k := 56) (b' := sp + 0x1078#64) rfl (by bv_omega) (by decide)

private theorem addsPState64_noneCap_z : (addsPState64 LibsignalTripleRatchetRepr.noneCap 1#64).z = true := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap; decide

private theorem addsPState64_z_false_of_ne_noneCap {x21 : BitVec 64} (hne : x21 ≠ LibsignalTripleRatchetRepr.noneCap) :
    (addsPState64 x21 1#64).z = false := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap at *
  simp only [Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne]; intro h; apply hne; bv_omega

private theorem setPC_preserves {s1 s : State} {pc : BitVec 64} (h : s1 = s.setPC pc) :
    s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧ (∀ r, s1.readReg64 r = s.readReg64 r) := by
  subst h; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem vn_some_pack (A : RustAlloc) (pin : VecPin) (a : BitVec 64) (v : VersionNegotiationPB) :
    ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v ⊢ ProtoRepr.optVersionNegotiationPBAt A a (some v) := by
  dsimp only [ProtoRepr.optVersionNegotiationPBAt]; rw [versionNegotiationPBAt_eq_exists_pin A a v]
  exact Entails.sepExists_right pin (Entails.refl _)

private theorem optEpochSecretRegSlotAt_some_ne (A : RustAlloc) (sp x21 x27 : BitVec 64) (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢
      ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ optEpochSecretRegSlotAt A sp x21 x27 (some es) := by
  dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne
  exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))

end CryptoVerification.SpqrV1.Top.Send
