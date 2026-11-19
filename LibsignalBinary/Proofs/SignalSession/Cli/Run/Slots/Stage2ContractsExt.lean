/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorPush
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.VarintSlow
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# Contract-Backed `Stage2ContractsExt` and `Stage2ContractsWeak` from `CliExternsOk`

Derives `AllocContractsX`, `Stage2ContractsWeak`, and the extended `Stage2ContractsExt` bundle
directly from `CliExternsOk P A ext` for any hook table `ext'` agreeing with `ext` on `cliHookNames`
(`AgreeOnCliHooks`).
-/

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `HookOk`/`HookSat` transport, stack monotonicity, and `AgreeOnCliHooks` -/

private theorem hookOk_map {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
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

private theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_withStack {α : Type} {f : State → State} {base : Spec α}
    (hh : HookOk f base) (stk : Nat)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ base.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [withStack] at hpre
    rwa [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack]
    rwa [← sepConj_assoc] at hpost
  · rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (withStack base s1).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem hookOk_sessionMemcpy_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpySpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  have h1 : HookOk f (withStack sessionMemcpyRegionSpec CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memcpySpec, libcMemcpySpec, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memcpySpec, withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
       sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemcpy_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) : HookOk f (libcMemcpySpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemcpyRegion_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemcpySpec stk)) :
    HookOk f (withStack sessionMemcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_memcpyRegion_of_libc {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemcpySpec stk)) : HookOk f (withStack memcpyRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

/-- Stack-equipped read-only `memcpy` specification at `hookStack`. -/
@[expose] def memcpyROSpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  CliExt.withStack
    { pre := fun (dst, src, bs) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
          bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
      post := fun (dst, src, bs) s0 sf =>
        ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    hookStack

private theorem hookOk_memcpyRO_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpyROSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (memcpyROSpecWithStack stk) :=
  hookOk_stack_mono hh hle hmax

private theorem hookOk_sessionMemmove_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memmoveSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemmoveSpec stk) := by
  let base : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
    { pre := fun (b, buf, dst, src, len) s0 =>
        ⌜s0.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧
         s0.readReg64 .x1 = b + BitVec.ofNat 64 src ∧
         (s0.readReg64 .x2).toNat = len ∧
         dst + len ≤ buf.length ∧ src + len ≤ buf.length⌝ ∗ (b ↦ₛ buf)
      post := fun (b, buf, dst, src, len) s0 sf =>
        ⌜sf.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
          (b ↦ₛ listMove buf dst src len) }
  have h1 : HookOk f (withStack base CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memmoveSpec, libcMemmoveSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memmoveSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemmove_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemmoveSpec stk)) : HookOk f (libcMemmoveSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemset_of_cliExt {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memsetSpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemsetSpec stk) := by
  let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
    { pre := fun (ptr, c, len) s0 =>
        ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg32 .x1).truncate 8 = c ∧
         (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
      post := fun (ptr, c, len) s0 sf =>
        ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
  have h1 : HookOk f (withStack base CliExt.memHookStack) :=
    hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memsetSpec, libcMemsetSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memsetSpec, withStack, base,
        sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono h1 hle hmax
  exact hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_libcMemset_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) : HookOk f (libcMemsetSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_sessionMemsetRegion_of_session {f : State → State} {stk : Nat}
    (hh : HookOk f (sessionMemsetSpec stk)) :
    HookOk f (withStack sessionMemsetRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by
      simp only [sessionMemsetSpec, libcMemsetSpec, withStack, sessionMemsetRegionSpec,
        memsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack,
      sessionMemsetRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_memsetRegion_of_libc {f : State → State} {stk : Nat}
    (hh : HookOk f (libcMemsetSpec stk)) :
    HookOk f (withStack memsetRegionSpec stk) :=
  hookOk_map (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => by
      simp only [libcMemsetSpec, withStack, memsetRegionSpec, sepConj_assoc,
        satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
    (fun _ _ _ _ _ _ hq => by simpa only [libcMemsetSpec, withStack, memsetRegionSpec,
      sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

private theorem hookOk_blackBoxU8_of_cliExt {f : State → State}
    (hh : HookOk f CliExt.blackBoxSpec) :
    HookOk f (withStack blackBoxU8Spec extHookStack) := by
  refine hookOk_map (fun v => v) (fun _ _ => True) (fun _ => trivial) hh
    (fun _ _ _ hp => hp) (fun v _ s0 sf _ _ hq => ?_)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  simp only [CliExt.blackBoxSpec, CliExt.withStack, withStack, blackBoxU8Spec,
    sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨⟨hx0, htr⟩, hstk⟩
  have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
    have h1 := congrArg (fun w : BitVec 32 => w.setWidth 8) hx0
    have hlhs : ((sf.readReg64 .x0).setWidth 32).setWidth 8 = (sf.readReg64 .x0).setWidth 8 :=
      BitVec.setWidth_setWidth_of_le (sf.readReg64 .x0) (by decide : 8 ≤ 32)
    have hrhs : ((v.setWidth 8).zeroExtend 32).setWidth 8 = v.setWidth 8 := by
      change ((v.setWidth 8).setWidth 32).setWidth 8 = v.setWidth 8
      rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    exact hlhs.symm.trans (h1.trans hrhs)
  exact ⟨⟨h8, htr⟩, hstk⟩

private theorem memHookStack_le_of_ext {stk : Nat} (hle : extHookStack ≤ stk) :
    CliExt.memHookStack ≤ stk :=
  Nat.le_trans (by decide : CliExt.memHookStack ≤ extHookStack) hle

/-- Agreement of `ext'` with `ext` on all `cliHookNames`. -/
structure AgreeOnCliHooks (ext ext' : String → Option (State → State)) : Prop where
  hook_eq : ∀ n, n ∈ cliHookNames → ext' n = ext n

theorem AgreeOnCliHooks.hookSat {α : Type} {ext ext' : String → Option (State → State)}
    (hAg : AgreeOnCliHooks ext ext') {n : String} {spec : Spec α}
    (hmem : n ∈ cliHookNames) (hs : HookSat ext n spec) :
    HookSat ext' n spec := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, (hAg.hook_eq n hmem).trans hf, hok⟩

/-! ## 2. Unconditional `spqrRecvEmptyAny` from `AllocContractsX` -/

private theorem spqrRecvEmpty_res_shape' (msg : List (BitVec 8)) :
    LibsignalSpqr.spqrRecvEmpty msg = .ok ([], none) ∨
      (msg ≠ [] ∧ ∃ sd, LibsignalSpqr.spqrRecvEmpty msg = .error sd) := by
  unfold LibsignalSpqr.spqrRecvEmpty
  cases hok : LibsignalSpqr.msgPreambleOk msg with
  | true => exact Or.inl rfl
  | false =>
    refine Or.inr ⟨?_, false, rfl⟩
    intro hnil
    subst hnil
    simp [LibsignalSpqr.msgPreambleOk, LibsignalSpqr.msgPreamble?] at hok

namespace Stage2ContractsExt

end Stage2ContractsExt

end CryptoVerification.SignalSession.Cli.Slots
