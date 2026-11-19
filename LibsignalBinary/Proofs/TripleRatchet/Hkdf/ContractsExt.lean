/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed HKDF Specifications and Hook Bridges

Defines `extHookStack`-sized contracts for `finalize_fixed`, `new_from_slice`, `extract`,
and `expand_multi_info` on `tripleRatchetProgAtExt`, together with the `HkdfContractsExt`
extern-contract bundle and `subroutine_ok`-to-`RunsToE` step bridges.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

/-! ## `extHookStack`-Sized Specifications -/

/-- Stack budget of `Hmac<Sha256>::finalize_fixed` under `extHookStack`
(`finalizeFixedStack + extHookStack = 144 + 16384 = 16528` B). -/
abbrev finalizeFixedStackExt : Nat := finalizeFixedStack + extHookStack

/-- Contract of `Hmac<Sha256>::finalize_fixed` with `finalizeFixedStackExt` (`16528` B). -/
@[expose] def finalizeFixedSpecExt (F : ShaCompress) : Spec FinalizeFixedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.hm ∧
      x.key.length ≤ 64 ∧ x.msg.length < 56⌝ ∗
    memRegion x.out 32 ∗ hmacCoreAt F x.hm x.key x.msg ∗ stackAt s.sp finalizeFixedStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (x.out ↦ₛ hmacWith F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ stackAt s0.sp finalizeFixedStackExt

/-- Stack budget of `Hmac<Sha256>::new_from_slice` under `extHookStack`
(`newFromSliceStack + extHookStack = 544 + 16384 = 16928` B). -/
abbrev newFromSliceStackExt : Nat := newFromSliceStack + extHookStack

/-- Contract of `Hmac<Sha256>::new_from_slice` with `newFromSliceStackExt` (`16928` B). -/
@[expose] def newFromSliceSpecExt (F : ShaCompress) : Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
    memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗ stackAt s.sp newFromSliceStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
    (x.keyA ↦ₛ x.key) ∗ stackAt s0.sp newFromSliceStackExt

/-- Stack budget of `GenericHkdf<Hmac<Sha256>>::extract` under `extHookStack`
(`extractStack + extHookStack = 976 + 16384 = 17360` B). -/
abbrev extractStackExt : Nat := extractStack + extHookStack

/-- Contract of `GenericHkdf<Hmac<Sha256>>::extract` with `extractStackExt` (`17360` B). -/
@[expose] def extractSpecExt (F : ShaCompress) : Spec ExtractGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.saltA ∧
      (x.salt.isSome → s.readReg64 .x2 = 32#64) ∧
      (x.salt = none → x.saltA = 0#64 ∨ s.readReg64 .x2 = 0#64) ∧
      s.readReg64 .x3 = x.ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      x.ikm.length = 32⌝ ∗
      memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s.sp extractStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦ₛ x.prk F) ∗ hmacCoreAt F (x.ret + 0x20#64) (x.prk F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      stackAt s0.sp extractStackExt

/-- Stack budget of `GenericHkdf<Hmac<Sha256>>::expand_multi_info` under `extHookStack`
(`expandMultiInfoStack + extHookStack = 640 + 16384 = 17024` B). -/
abbrev expandMultiInfoStackExt : Nat := expandMultiInfoStack + extHookStack

/-- Contract of `GenericHkdf<Hmac<Sha256>>::expand_multi_info` with `expandMultiInfoStackExt`
(`17024` B). -/
@[expose] def expandMultiInfoSpecExt (F : ShaCompress) : Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧ s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.okmLen ∧
      x.prk.length ≤ 64 ∧ x.info.length < 23 ∧ (x.okmLen = 64 ∨ x.okmLen = 80)⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      stackAt s.sp expandMultiInfoStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand F x.prk x.info x.okmLen) ∗
      stackAt s0.sp expandMultiInfoStackExt

/-- Stack-equipped read-only `memcpy` spec at configurable `hookStack`. -/
abbrev memcpyROExtSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

namespace HkdfExt

open Extract

/-- `ShaState`-indexed `compress256` contract with stack slack `hookStack`. -/
@[expose] def compress256ExternShaSpec (F : ShaCompress) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × ShaState × List (BitVec 8)) where
  pre := fun (stA, blkA, st, bs) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧
      64 * (s.readReg64 .x2).toNat = bs.length⌝ ∗
      (blkA ↦ₛ bs) ∗ (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ stackAt s.sp hookStack
  post := fun (stA, blkA, st, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (blkA ↦ₛ bs) ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes ((HMAC.chunks64 bs).foldl F st)) ∗
      stackAt s0.sp hookStack

/-- `memset` contract with 64-bit `.x1` low-byte truncation and stack slack `hookStack`. -/
@[expose] def session2MemsetExternSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, val, n) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 8 = val ∧
      (s0.readReg64 .x2).toNat = n⌝ ∗
      memRegion dst n ∗ stackAt s0.sp hookStack
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ List.replicate n val) ∗ stackAt s0.sp hookStack

end HkdfExt

/-! ## `HkdfContractsExt` Bundle -/

namespace HkdfContractsExt

private theorem hookOk_map_pure {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0, (f s0).mem ⊨ s₁.post (g y) s0 (f s0) ∗ R →
      (f s0).mem ⊨ s₂.post y s0 (f s0) ∗ R)
    (hpan : ∀ x s0 sf, s₁.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, s₁.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, s₁.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hp) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp'⟩ | ⟨code, _, he'⟩ | ⟨_, ho'⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 hq⟩
  · rw [hpan (g y) s0 (f s0), satisfies_pure_sepConj] at hp'; exact False.elim hp'.1
  · rw [hex (g y) code s0 (f s0), satisfies_pure_sepConj] at he'; exact False.elim he'.1
  · rw [hoom (g y) s0 (f s0), satisfies_pure_sepConj] at ho'; exact False.elim ho'.1

private theorem hookSat_map {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_stack_mono {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (SignalSession.CliExt.withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (SignalSession.CliExt.withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (SignalSession.CliExt.withStack base s1).pre x s0 ∗ R' := by
    dsimp only [SignalSession.CliExt.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SignalSession.CliExt.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [SignalSession.CliExt.withStack] at hp
    rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [SignalSession.CliExt.withStack] at he
    rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [SignalSession.CliExt.withStack] at ho
    rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem readReg32_truncate8_eq (s : State) (r : Reg) :
    (s.readReg32 r).truncate 8 = (s.readReg64 r).truncate 8 := by
  change ((s.readReg64 r).setWidth 32).setWidth 8 = (s.readReg64 r).setWidth 8
  exact BitVec.setWidth_setWidth_of_le (s.readReg64 r) (by decide : 8 ≤ 32)

private theorem isPanic_compress256 :
    Rust.isPanicSymbol "sha2::sha256::compress256" = false := by
  simp [Rust.isPanicSymbol]

private theorem isPanic_memcpy : Rust.isPanicSymbol "memcpy" = false := by
  simp [Rust.isPanicSymbol]

private theorem isPanic_memset : Rust.isPanicSymbol "memset" = false := by
  simp [Rust.isPanicSymbol]

private theorem isPanicE_compress256 :
    E2E.isImagePanicSymbol "sha2::sha256::compress256" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_compress256, E2E.extraImagePanicNames]

private theorem isPanicE_memcpy :
    E2E.isImagePanicSymbol "memcpy" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memcpy, E2E.extraImagePanicNames]

private theorem isPanicE_memset :
    E2E.isImagePanicSymbol "memset" = false := by
  simp [E2E.isImagePanicSymbol, isPanic_memset, E2E.extraImagePanicNames]

end HkdfContractsExt

/-! ## `subroutine_ok`-to-`RunsToE` Bridges and Cut Invariants -/

namespace HkdfExt

open Extract

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

theorem satisfies_two_blocks {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hn2 : n2 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hdisj12 : h1.Disjoint h2 := regionHeap_disjoint m hd12 hn2
  exact Satisfies.sepConj_intro hdisj12 hp1 hp2 (Heap.Matches.union hm1 hm2)

theorem isBlock_two_none_outside {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) {a : BitVec 64}
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) :
    h a = none := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  have hn1 : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have hn2 : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  simp [Heap.union, regionHeap, hn1, hn2]

theorem isBlock_two_mapped_false {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  simp [Heap.union, regionHeap]

theorem isBlock_two_s2frame_aux {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hp : (P1 ∗ P2) h) (hm : h.Matches m)
    (hmc : ∀ a c, (fullComplementHeap h m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap h m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    (∀ a, (m.perm a).mapped = true ∧ m.isAnon a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) ∧
    (∀ a, m.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m'.perm a = some Perm.protNone ∧
      (m.isLazyFree a = false → m'.read8 a = m.read8 a ∧ m'.isLazyFree a = false)) := by
  refine ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩
  · have hm0 : h.mapped a = false := isBlock_two_mapped_false hb1 hb2 hp a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      unfold Heap.Matches at hm
      obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeap b2 n2 m2)) a with
      | none => rfl
      | some c =>
        have hperm := hm.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

theorem isBlock_two_s2frame {P1 P1' P2 R1 R2 : SepProp}
    {dst b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ1' Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 dst n1 Φ1) (hb1' : IsBlock P1' dst n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2)
    (hmc : ∀ a c, (fullComplementHeap hP m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap hP m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    S2Frame m m' [(dst, n1), (b2, n2)] := by
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     isBlock_two_s2frame_aux hb1 hb2 hpP hmP hmc hmc_map⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion dst n1 a := ha (dst, n1) (by simp)
    have ha2 : OutsideRegion b2 n2 a := ha (b2, n2) (by simp)
    have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc a _ hca).1
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.permNoLazy_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.perm_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hlf_a : m.isLazyFree a = true
        · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact hmc a .lazy hca
        · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_f]
          exact (hmc a _ hca).2.1
  · by_cases hin1 : InRegion dst n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨by rw [hb2.perm_rw hpost_2 hin2]; rfl, hb2.isLazyFree_false hpost_2 hin2⟩
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hrw_a : m.perm a = some Perm.rw
        · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact ⟨by rw [hp']; rfl, hlf'⟩
        · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
          obtain ⟨-, hr', hlf'⟩ := hmc a _ hca
          exact ⟨hr', hlf'⟩

theorem shaStateBytes_length (st : ShaState) :
    (LibsignalHmac.shaStateBytes st).length = 32 := by
  rcases st with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

theorem regionHeap_disjoint_opt {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} (m : Memory)
    (hd : n₁ = 0 ∨ n₂ = 0 ∨ DisjointRegions b₁ n₁ b₂ n₂) (hn₂ : n₂ ≤ 2 ^ 64) :
    (regionHeap b₁ n₁ m).Disjoint (regionHeap b₂ n₂ m) := by
  rcases hd with rfl | rfl | hd
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inl (by simp [regionHeap, InRegion])
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inr (Or.inl (by simp [regionHeap, InRegion]))
  · exact regionHeap_disjoint m hd hn₂

theorem satisfies_three_blocks_opt {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : n1 = 0 ∨ n2 = 0 ∨ DisjointRegions b1 n1 b2 n2)
    (hd13 : n1 = 0 ∨ n3 = 0 ∨ DisjointRegions b1 n1 b3 n3)
    (hd23 : n2 = 0 ∨ n3 = 0 ∨ DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  let h3 := regionHeap b3 n3 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hp3 : P3 h3 := (hb3.iff h3).mpr ⟨m, hΦ3, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hm3 : h3.Matches m := IsBlock.regionHeap_matches b3 n3 m hrw3
  have hdisj23 : h2.Disjoint h3 := regionHeap_disjoint_opt m hd23 hn3
  have hm23 : (h2.union h3).Matches m := Heap.Matches.union hm2 hm3
  have hdisj1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hdisj23).mpr
      ⟨regionHeap_disjoint_opt m hd12 hn2, regionHeap_disjoint_opt m hd13 hn3⟩
  exact Satisfies.sepConj_intro hdisj1_23 hp1 (SepProp.holds_sepConj_intro hdisj23 hp2 hp3)
    (Heap.Matches.union hm1 hm23)

private theorem chunks64_single_of_len_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    HMAC.chunks64 bs = [bs] := by
  simp [HMAC.chunks64, h]

end HkdfExt

end CryptoVerification.LibsignalTripleRatchet
