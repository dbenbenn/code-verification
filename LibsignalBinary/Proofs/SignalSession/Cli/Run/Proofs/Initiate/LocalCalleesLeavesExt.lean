/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.Leaves -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesDecode
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extern-Parameterized Leaf Callee Contracts for `initiate`

Proves `CliExternsOk P A ext`-parameterized placed `subroutine_ok` theorems for the leaf callees of
`initiate`:
`spqr_chain_params`, `<SessionState>::set_unacknowledged_kyber_pre_key_id`,
`<SessionState>::set_kyber_ciphertext`, `<curve25519::PrivateKey>::derive_public_key_bytes`,
`<SessionState>::{new, with_receiver_chain, with_sender_chain}`, `<kem::Ciphertext>::serialize`,
and `<SessionRecord>::promote_state`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## Shared specification definitions -/

/-- `CliExternsOk`-compatible `<kem::Ciphertext>::serialize` contract. -/
@[expose] def kemCiphertextSerializeExtSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrPtr, boxPtr, ctBytes) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568⌝ ∗
    (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
    (boxPtr ↦ₛ ctBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun (hdrPtr, boxPtr, ctBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧ tempPtr ≠ 0#64⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗ (boxPtr ↦ₛ ctBytes) ∗
      (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cond_eq_adds_1_false_ext {cap : BitVec 64} (hne : cap + 1#64 ≠ 0#64) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [ProofLib.conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

@[simp, arm64_norm]
abbrev leafSetUnackKyberPreKeyIdName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id"

/-- Specification of `<SessionState>::set_unacknowledged_kyber_pre_key_id`. -/
@[expose] def leafSetUnackKyberPreKeyIdSpec : Spec (BitVec 64 × BitVec 64 × BitVec 32) where
  pre := fun (statePtr, cap, kyberPreKeyId) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ (s.readReg64 .x1).setWidth 32 = kyberPreKeyId ∧
      cap + 1#64 ≠ 0#64⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      (∃∗ w : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w)
  post := fun (statePtr, cap, kyberPreKeyId) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      ((statePtr + 0x140#64) ↦₃₂ kyberPreKeyId)

@[simp, arm64_norm]
abbrev leafSetKyberCiphertextName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"

/-- Specification of `<SessionState>::set_kyber_ciphertext` on an empty slot (`0xffffffffffffffff`). -/
@[expose] def leafSetKyberCiphertextNoneSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (statePtr, ctPtr, ctLen) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x1 = ctPtr ∧ s.readReg64 .x2 = ctLen⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w1 : BitVec 64, (statePtr + 0x130#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (statePtr + 0x138#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w3) ∗
      cells (s.sp - 48#64) 6
  post := fun (statePtr, ctPtr, ctLen) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x130#64) ↦₆₄ ctPtr) ∗
      ((statePtr + 0x138#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x140#64) ↦₃₂ 0xffffffff#32) ∗
      cells (s0.sp - 48#64) 6

private theorem stackAt_kemSerialize48_ext (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, tryCloneFromRefStackX, extHookStack]
  have hsub : sp - 48#64 - BitVec.ofNat 64 (2 ^ 14) = sp - BitVec.ofNat 64 (2 ^ 14 + 48) := by
    bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 48))
        (n := 2 ^ 14) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (ProofLib.memRegion_cells (sp - 48#64) 6 (by decide) :
        memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

private theorem memRegion_1569_split_ext (p : BitVec 64) :
    memRegion p 1569 = (∃∗ b0 : BitVec 8, p ↦₈ b0) ∗ memRegion (p + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
      memRegion_split p 1 1568 (by decide),
      memRegion_one p]

private theorem sepWPp_pure_mid_ext {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post postP : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) post postP) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post postP := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem hookOk_map_local {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hpreY hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hpreY) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 (f s0) (hI s0) hpreY hq⟩
  · exact Or.inr (Or.inl ⟨hp1, hpanic y R s0 (f s0) hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, hexit y c R s0 (f s0) he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, hoom y R s0 (f s0) ho2⟩))

private theorem hookSat_map_local {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_withStack_local {α : Type} {f : State → State} {base : Spec α}
    (hh : HookOk f base) (stk : Nat)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (LibsignalTripleRatchet.withStack base stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ base.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [LibsignalTripleRatchet.withStack] at hpre
    rwa [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withStack]
    rwa [← sepConj_assoc] at hpost
  · rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem hookOk_stack_mono_local {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (LibsignalTripleRatchet.withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (LibsignalTripleRatchet.withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (LibsignalTripleRatchet.withStack base s1).pre x s0 ∗ R' := by
    dsimp only [LibsignalTripleRatchet.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [LibsignalTripleRatchet.withStack] at hp
    rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [LibsignalTripleRatchet.withStack] at he
    rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [LibsignalTripleRatchet.withStack] at ho
    rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem hookOk_sessionMemcpy_of_cliExt_local {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpySpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  have h1 : HookOk f (LibsignalTripleRatchet.withStack sessionMemcpyRegionSpec CliExt.memHookStack) :=
    hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memcpySpec, libcMemcpySpec,
        LibsignalTripleRatchet.withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memcpySpec, LibsignalTripleRatchet.withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono_local h1 hle hmax
  exact hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec,
      LibsignalTripleRatchet.withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, LibsignalTripleRatchet.withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

section PromoteStateExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_promoteState_ext_split (sp : BitVec 64) :
    stackAt sp (extHookStack + 32) =
      memRegion (sp - 16416#64) 16320 ∗
      cells (sp - 96#64) 8 ∗
      cells (sp - 32#64) 4 := by
  simp only [stackAt, extHookStack]
  rw [show (2 ^ 14 + 32 : Nat) = 16416 from rfl,
      show BitVec.ofNat 64 16416 = 16416#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 16416#64) (n := 16320) (k := 96)
        (b' := sp - 96#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 64) (k := 32)
        (b' := sp - 32#64) (by decide) (by bv_omega) (by decide),
      (ProofLib.memRegion_cells (sp - 96#64) 8 (by decide) :
        memRegion (sp - 96#64) 64 = cells (sp - 96#64) 8),
      (ProofLib.memRegion_cells (sp - 32#64) 4 (by decide) :
        memRegion (sp - 32#64) 32 = cells (sp - 32#64) 4)]

private theorem stackAt_promoteState_tail_merge (sp : BitVec 64) :
    memRegion (sp - 16416#64) 16320 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 =
      memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [← stackAt_promoteState_ext_split sp]
  simp only [stackAt, extHookStack]
  rw [show (2 ^ 14 + 32 : Nat) = 16416 from rfl,
      show (2 ^ 14 : Nat) = 16384 from rfl,
      show BitVec.ofNat 64 16416 = 16416#64 from rfl,
      show BitVec.ofNat 64 16384 = 16384#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16416#64) (n := 32) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

private theorem cells_sub32_4_merge_ext (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

end PromoteStateExt

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
