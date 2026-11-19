/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs -- shake: keep

/-!
# Contract-Backed Hook and Key-Agreement Bridges (`tripleRatchetProgAtExt`)

Bridges `CliExternsOk` / `HookSat` contracts at `pqxdhHookStackExt` (`16384` B) to the by-value
`kyber::encapsulate` ABI (`kyberEncapsByValSpec`), allocator/memcpy helpers, and the
`FrozenLoaded`-only `<PrivateKey>::calculate_agreement` contract
(`calculateAgreement_frozen_ok_ext`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem fitBv8_kyberEncapsOutBytes_eq_extA_of_len {P : Primitives}
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (pk r : Bytes) (hpk : pk.length = 1568) :
    let o := encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
    fitBv8 1600 (kyberEncapsOutBytes P pk r) = o.1.toList ++ o.2.toList := by
  intro o; unfold kyberEncapsOutBytes; rw [hEncapsEq pk r hpk]; dsimp only; unfold fitBv8
  rw [bytesToBv8_append, e2e_bytesToBv8_vecU8, e2e_bytesToBv8_vecU8]
  have hlen : (o.1.toList ++ o.2.toList).length = 1600 := by
    rw [List.length_append, o.1.toList_length, o.2.toList_length]
  rw [hlen, List.take_of_length_le (by rw [hlen]), Nat.sub_self, List.replicate_zero,
    List.append_nil]

@[simp, arm64_norm] abbrev initAliceCalcSubStackExt : Nat := 64 + pqxdhHookStackExt
@[simp, arm64_norm] abbrev initAliceCalcStackExt : Nat := 160 + initAliceCalcSubStackExt

theorem initAlice_stackAt_split (sp : BitVec 64) (extra inner : Nat)
    (hbound : extra + inner ≤ 2 ^ 64) :
    stackAt sp (extra + inner) =
      memRegion (sp - BitVec.ofNat 64 (extra + inner)) extra ∗ stackAt sp inner := by
  have hb' : sp - BitVec.ofNat 64 inner =
      sp - BitVec.ofNat 64 (extra + inner) + BitVec.ofNat 64 extra := by
    rw [Nat.add_comm extra inner, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (extra + inner))
    (n := extra) (k := inner) (b' := sp - BitVec.ofNat 64 inner) rfl hb' hbound

theorem initAlice_hookOk_map {α β : Type} {fn : State → State}
    {specA : Spec α} {specB : Spec β} (f : β → α)
    (hok : HookOk fn specA)
    (hpre : ∀ b R s0, (s0.mem ⊨ specB.pre b s0 ∗ R) → (s0.mem ⊨ specA.pre (f b) s0 ∗ R))
    (hpost : ∀ b R s0 sf, (s0.mem ⊨ specB.pre b s0 ∗ R) →
      (sf.mem ⊨ specA.post (f b) s0 sf ∗ R) → (sf.mem ⊨ specB.post b s0 sf ∗ R))
    (hpan : ∀ a s0 sf, specA.onPanic a s0 sf = ⌜False⌝ := by intro _ _ _; rfl)
    (hexit : ∀ a c s0 sf, specA.onExit a c s0 sf = ⌜False⌝ := by intro _ _ _ _; rfl)
    (hoom : ∀ a s0 sf, specA.onOom a s0 sf = ⌜False⌝ := by intro _ _ _; rfl) :
    HookOk fn specB := by
  intro b R s0 hrun hb hsp
  obtain ⟨hkf, hsym, hout⟩ := hok (f b) R s0 hrun (hpre b R s0 hb) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hf⟩ | ⟨c, _, hf⟩ | ⟨_, hf⟩
  · exact Or.inl ⟨hret, hcc, hpost b R s0 (fn s0) hb hq⟩
  · rw [hpan] at hf; exact (not_satisfies_false_sepConj hf).elim
  · rw [hexit] at hf; exact (not_satisfies_false_sepConj hf).elim
  · rw [hoom] at hf; exact (not_satisfies_false_sepConj hf).elim

/-- `kyber::encapsulate(&pk, randomness)` (`sret x8`) with by-value 32-byte `coins`
(`memRegion g.coinsPtr 32` after call) and `pqxdhHookStackExt` (`16384` B) stack budget. -/
@[expose] def kyberEncapsByValSpec (P : Primitives) : Spec KyberEncapsCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.pkPtr ∧ s.readReg64 .x1 = g.coinsPtr ∧ s.readReg64 .x8 = g.outPtr ∧
      g.pk1568.length = 1568 ∧ g.coins32.length = 32 ∧
      (P.kemEncaps g.pk1568 g.coins32).isSome⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
      (g.coinsPtr ↦ₛ bytesToBv8 g.coins32) ∗
      memRegion g.outPtr 1600 ∗ stackAt s.sp pqxdhHookStackExt
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ bytesToBv8 g.pk1568) ∗
      memRegion g.coinsPtr 32 ∗
      (g.outPtr ↦ₛ fitBv8 1600 (kyberEncapsOutBytes P g.pk1568 g.coins32)) ∗
      stackAt s0.sp pqxdhHookStackExt

theorem hookSat_kyberEncapsByVal_of_kemEncaps_of_len {P : Primitives}
    {Q : CryptoVerification.E2E.PqxdhPrims}
    {ext : String → Option (State → State)}
    (hEncapsEq : ∀ pk r : Bytes, pk.length = 1568 → P.kemEncaps pk r =
      let (ct, ss) :=
        Q.encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (hKem : HookSat ext
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemEncapsName
      (SignalSession.CliExt.kemEncapsSpec Q)) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec P) := by
  rcases hKem with ⟨fn, hfn, hok⟩
  have hname : kyberEncapsStub =
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemEncapsName := rfl
  refine ⟨fn, hname ▸ hfn, initAlice_hookOk_map
    (fun (g : KyberEncapsCall) =>
      (g.pkPtr, CryptoVerification.E2E.u8Vec 1568 g.pk1568,
       g.coinsPtr, CryptoVerification.E2E.u8Vec 32 g.coins32, g.outPtr))
    hok ?_ ?_⟩
  · intro g R s0 hpre
    simp only [kyberEncapsByValSpec, pqxdhHookStackExt,
      SignalSession.CliExt.kemEncapsSpec, SignalSession.CliExt.withStack,
      extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx8, hpk, hcoins, _⟩, hmem⟩
    rw [ResponderCore.u8Vec_toList_of_length hpk, ResponderCore.u8Vec_toList_of_length hcoins]
    exact ⟨⟨hx0, hx1, hx8⟩, by ac_nf at hmem ⊢⟩
  · intro g R s0 sf hpre hpost
    simp only [kyberEncapsByValSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, _, hpk, _hcoins, _⟩, _⟩
    simp only [kyberEncapsByValSpec, pqxdhHookStackExt,
      SignalSession.CliExt.kemEncapsSpec, SignalSession.CliExt.withStack,
      extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem⟩
    rw [ResponderCore.u8Vec_toList_of_length hpk] at hmem
    let o := Q.encaps (CryptoVerification.E2E.u8Vec 1568 g.pk1568)
      (CryptoVerification.E2E.u8Vec 32 g.coins32)
    have hout : fitBv8 1600 (kyberEncapsOutBytes P g.pk1568 g.coins32) =
        o.1.toList ++ o.2.toList :=
      fitBv8_kyberEncapsOutBytes_eq_extA_of_len Q.encaps hEncapsEq g.pk1568 g.coins32 hpk
    have hmerge : (g.outPtr ↦ₛ (o.1.toList ++ o.2.toList)) =
        (g.outPtr ↦ₛ o.1.toList) ∗ ((g.outPtr + 0x620#64) ↦ₛ o.2.toList) := by
      rw [pointsToBytes_append, o.1.toList_length]
    rw [hout, hmerge]
    exact ⟨htr, by ac_nf at hmem ⊢⟩

theorem hookSat_kyberEncapsByVal_of_kemEncaps {P : Primitives}
    {Q : CryptoVerification.E2E.PqxdhPrims}
    {ext : String → Option (State → State)}
    (hEncapsEq : ∀ pk r : Bytes, P.kemEncaps pk r =
      let (ct, ss) :=
        Q.encaps (CryptoVerification.E2E.u8Vec 1568 pk) (CryptoVerification.E2E.u8Vec 32 r)
      some (CryptoVerification.E2E.vecU8 ss, CryptoVerification.E2E.vecU8 ct))
    (hKem : HookSat ext
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.kemEncapsName
      (SignalSession.CliExt.kemEncapsSpec Q)) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec P) :=
  hookSat_kyberEncapsByVal_of_kemEncaps_of_len (fun pk r _ => hEncapsEq pk r) hKem

theorem hookSat_kyberEncapsByVal_of_externsOk
    (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives) {P0 : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    HookSat ext kyberEncapsStub (kyberEncapsByValSpec (initiatorModelPrims X P0)) :=
  hookSat_kyberEncapsByVal_of_kemEncaps_of_len
    (fun pk r hpk => by
      simp only [initiatorModelPrims, ResponderCore.ofSignalPqxdhPrimitives,
        CryptoVerification.E2E.modelPrims, CryptoVerification.E2E.blockLevelPrims,
        SignalPqxdh.kyberPkLen, hpk, beq_self_eq_true, ↓reduceIte])
    hOk.kemEncaps

/-- Hook hypotheses needed by `<PrivateKey>::calculate_agreement` and `initialize_alice_session`
Stage 1 DH steps on `tripleRatchetProgAtExt`. -/
structure InitAliceAgreeHooks (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocHooks A ext
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" SignalSession.CliExt.shimSpec
  memcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec
  blackBox : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec
  dh : HookSat ext dhName (SignalSession.CliExt.dhSpec C)
  staticDrop : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec
  sharedDrop : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec

theorem InitAliceAgreeHooks.of_externsOk
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    InitAliceAgreeHooks P0.C A ext where
  alloc := hOk.alloc
  shim := hOk.shim
  memcpy := hOk.memcpy
  blackBox := hOk.blackBox
  dh := hOk.dh
  staticDrop := hOk.staticDrop
  sharedDrop := hOk.sharedDrop

@[expose] def initAliceMemcpyRegionExtSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack

private theorem initAlice_hookSat_shim {ext : String → Option (State → State)}
    (h : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" SignalSession.CliExt.shimSpec) :
    HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" pqxdhShimSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, hfn, initAlice_hookOk_map id hok (fun _ _ _ hp => hp) (fun _ _ _ _ _ hq => hq)⟩

private theorem initAlice_hookSat_memcpy {ext : String → Option (State → State)}
    (h : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec) :
    HookSat ext "memcpy" initAliceMemcpyRegionExtSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, initAlice_hookOk_map (fun x => x) hok ?_ ?_⟩
  · rintro ⟨dst, src, bs⟩ R s0 hpre
    simp only [initAliceMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
    have hx2_nat : (s0.readReg64 .x2).toNat = bs.length := by
      rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact ⟨⟨hx0, hx1, hx2_nat⟩, by ac_nf at hmem ⊢⟩
  · rintro ⟨dst, src, bs⟩ R s0 sf _ hpost
    simp only [initAliceMemcpyRegionExtSpec, SignalSession.CliExt.memcpySpec, libcMemcpySpec,
      SignalSession.CliExt.memHookStack, allocHookStack, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem⟩
    exact ⟨hp, by ac_nf at hmem ⊢⟩

theorem stackAt_calc_split_alloc_ext (fsp : BitVec 64) :
    stackAt fsp initAliceCalcStackExt =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 16608#64) 12512 := by
  have h1 := initAlice_stackAt_split fsp 12512 allocHookStack (by decide)
  have h2 : (12512 + allocHookStack : Nat) = initAliceCalcStackExt := by decide
  have h3 : BitVec.ofNat 64 (12512 + allocHookStack) = 16608#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

theorem stackAt_calculateAgreement_eq_pqxdh_ext (fsp : BitVec 64) :
    stackAt fsp initAliceCalcStackExt =
      memRegion (fsp - 16608#64) 224 ∗ stackAt fsp pqxdhHookStackExt := by
  have h1 := initAlice_stackAt_split fsp 224 pqxdhHookStackExt (by decide)
  have h2 : (224 + pqxdhHookStackExt : Nat) = initAliceCalcStackExt := by decide
  have h3 : BitVec.ofNat 64 (224 + pqxdhHookStackExt) = 16608#64 := rfl
  rw [h3] at h1
  rw [← h2, h1]

theorem stackAt_pqxdh_split_alloc_ext (fsp : BitVec 64) :
    stackAt fsp pqxdhHookStackExt =
      stackAt fsp allocHookStack ∗ memRegion (fsp - 16384#64) 12288 := by
  have h1 := initAlice_stackAt_split fsp 12288 allocHookStack (by decide)
  have h2 : (12288 + allocHookStack : Nat) = pqxdhHookStackExt := by decide
  have h3 : BitVec.ofNat 64 (12288 + allocHookStack) = 16384#64 := rfl
  rw [h3] at h1
  rw [← h2, h1, sepConj_comm]

end CryptoVerification.E2E.Pqxdh.Initiator
