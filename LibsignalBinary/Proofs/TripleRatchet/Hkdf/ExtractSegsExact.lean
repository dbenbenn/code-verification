/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSatExactMemcpy` sibling of `TripleRatchet.Hkdf.Extract` (Block `54`)

Replaces `[HkdfPlacedHooks C.F H]` (`H lsMemcpySym = some memcpyHook`) on Block `54`'s raw
`memcpy` segment `Extract.seg1b_placed_runsTo` (`ExtractSegs.lean:1001`) with
`h_mc : HookSatExactMemcpy H lsMemcpySym` in the `∀ c : MemcpyClobber` shape
(`s2_memcpy_step_placed_of_exact`):
- Keeps `EMemcpyPlaced` and `EC88` unchanged (preserving exact `s.mem.writeBytes sp0 x.ikm`
  across the 3 post-call instructions without `Frame → S2Frame` cut-predicate rewrites);
- Reuses the other 8 segments (`seg0`, `nfs1`, `seg1a`, `seg1c`, `fin`, `seg2`, `nfs2`, `seg3`)
  directly from `ExtractSegs`;
- Assembles `extract_placed_ok_of_inv_exact`, `extract_placed_ok_exact`, and
  `extract_placed_ok_of_plain_exact` parameterized by `h_mc : HookSatExactMemcpy H lsMemcpySym`
  and `FinPostS2` (accepting both `FinalizeFixedProof.FinPost` via `FinPostS2.of_finPost` and
  the `S2Frame`-backed `FinalizeFixedSat.FinPostSat`).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (hkdfExtract)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsρ lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost HmacSt NewFromSliceGhost RW
  RunsTo blkPC_54 blkPl_54 blkPl_123 effectiveSalt extPlacedFakeB extPlacedFakeB_off_80
  extPlacedFakeB_off_328 extPlacedFakeB_off_380 extPlacedFakeB_off_396 finPlacedFakeB
  finPlacedFakeB_off_0 hmacCoreAt isBlock_hmacCoreAt length_hmacWith lsMemcpySym optSaltAt
  rw_of_perm_eq
)
open CryptoVerification.LibsignalTripleRatchet.Extract (
  CallingConventionPreserved.x19
  CallingConventionPreserved.x20 CallingConventionPreserved.x21 CallingConventionPreserved.x22
  CallingConventionPreserved.x27 CallingConventionPreserved.x29 EC88 ERet1 ERet2 ERetFin ExtFrame
  ExtSaved HmacSt.of_writeBytes_32_write8_pos RunsTo.toE RunsToE S2Frame
  agreesOutside_sp0_write8 disjoint_fullComplementHeap disj_sp0_off disj_sp0_sub_off
  effectiveSalt_length frame_of_agreesOutside fullComplementHeap hmacSt_saltSliceOf
  isBlock_three_s2frame matches_fullComplementHeap pointsToBytes_saltRegOf_eq saltPtrOf saltRegOf
  saltSliceOf saltSliceOf_length_le satisfies_three_blocks seg0_placed_runsTo seg1a_placed_runsTo
  seg1c_placed_runsTo seg2_placed_runsTo seg3_placed_runsTo sp0_aligned sp0_aligned_0b1111
)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPost)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExtractX (ExtSaved.changeSetMem)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy s2_memcpy_step_placed_of_exact
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  extractSpecSat extractStackSat newFromSliceSpecSat newFromSliceStackSat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (
  FinPreSat FinPreSat.of_320
)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

public abbrev ExtFrameSat (s0 : State) (sp0 : BitVec 64) (m : Memory) : Prop :=
  S2Frame s0.mem m [(s0.readReg64 .x0, 0xb0), (sp0 - 720#64, 1152)]

public theorem rw_stkSat_sub {m : Memory} {sp0 : BitVec 64}
    (hrw : RW m (sp0 - 720#64) 1152) (addr : BitVec 64) (sz : Nat)
    (hsub : (addr - (sp0 - 720#64)).toNat + sz ≤ 1152) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

public theorem disj_stkSat_sub_right {a : BitVec 64} {n : Nat} {sp0 : BitVec 64}
    (hd : DisjointRegions a n (sp0 - 720#64) 1152) (addr : BitVec 64) (sz : Nat)
    (hsub : 0 < sz ∧ (addr - (sp0 - 720#64)).toNat + sz ≤ 1152) :
    DisjointRegions a n addr sz := by
  unfold DisjointRegions at hd ⊢
  bv_omega

public theorem ExtFrameSat.of_extFrame {s0 : State} {sp0 : BitVec 64} {m1 m2 : Memory}
    (hf1 : ExtFrameSat s0 sp0 m1) (hf2 : ExtFrame (s0.setMem m1) sp0 m2) :
    ExtFrameSat s0 sp0 m2 := by
  refine hf1.trans (hf2.mono fun a ha => ?_)
  have hout : OutsideRegion (s0.readReg64 .x0) 0xb0 a :=
    ha (s0.readReg64 .x0, 0xb0) (by simp)
  have hstk : OutsideRegion (sp0 - 720#64) 1152 a :=
    ha (sp0 - 720#64, 1152) (by simp)
  intro r hr
  simp only [State.readReg64_setMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · simp only [OutsideRegion] at hstk ⊢
    bv_omega

public theorem ExtFrameSat.of_agreesOutside_sp0 {s0 : State} {sp0 : BitVec 64} {m m' : Memory} {n : Nat}
    (hf : ExtFrameSat s0 sp0 m) (hn : n ≤ 432) (hag : AgreesOutside m m' sp0 n) :
    ExtFrameSat s0 sp0 m' := by
  refine hf.trans ((S2Frame.of_frame (frame_of_agreesOutside hag)).mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 720#64) 1152 a :=
    ha (sp0 - 720#64, 1152) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

public theorem ExtFrameSat.trans_pair {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : Nat} {a₂ : BitVec 64} {n₂ : Nat}
    (hf₁ : ExtFrameSat s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp0 - 720#64)).toNat + n₁ ≤ 1152)
    (hsub₂ : (a₂ - (sp0 - 720#64)).toNat + n₂ ≤ 1152) :
    ExtFrameSat s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 720#64) 1152 a :=
    ha (sp0 - 720#64, 1152) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega⟩

public theorem ExtFrameSat.trans_triple {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : Nat} {a₂ : BitVec 64} {n₂ : Nat} {a₃ : BitVec 64} {n₃ : Nat}
    (hf₁ : ExtFrameSat s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 720#64)).toNat + n₁ ≤ 1152)
    (hsub₂ : (a₂ - (sp0 - 720#64)).toNat + n₂ ≤ 1152)
    (hsub₃ : (a₃ - (sp0 - 720#64)).toNat + n₃ ≤ 1152) :
    ExtFrameSat s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 720#64) 1152 a :=
    ha (sp0 - 720#64, 1152) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

public abbrev ExtCommonSat (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  s.status = .Running ∧
  s.sp = sp0 ∧
  s.readReg64 .x19 = s0.readReg64 .x0 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x29 = sp0 + 336#64 ∧
  ExtSaved s0 sp0 s.mem ∧
  ExtFrameSat s0 sp0 s.mem

@[expose] public def ENfs1PlacedSat [LibsignalPlacement] (x : ExtractGhost) (s0 : State)
    (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = lsmpl.base 114 ∧
  s.readReg64 .lr = (blkPl_54).base + 80#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = saltRegOf sp0 x ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (saltSliceOf x).length ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  (∀ sv, x.salt = some sv → x.saltA ≠ 0#64) ∧
  s.mem.readBytes (saltPtrOf sp0 x) (saltSliceOf x).length = saltSliceOf x

@[expose] public def ERet1Sat (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = b + bv% (offExtract + 80) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

@[expose] public def EMemcpyPlacedSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = lsρ lsMemcpySym ∧
  s.readReg64 .lr = (blkPl_54).base + 192#64 ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x21 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x25 = 0#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) []

@[expose] public def EC88Sat (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = b + bv% (offExtract + 328) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) x.ikm

@[expose] public def EFinPlacedSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = (blkPl_123).base ∧
  s.readReg64 .lr = (blkPl_54).base + 380#64 ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem (sp0 + 176#64) F (effectiveSalt x.salt) x.ikm

@[expose] public def ERetFinSat (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = b + bv% (offExtract + 380) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

@[expose] public def ENfs2PlacedSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = lsmpl.base 114 ∧
  s.readReg64 .lr = (blkPl_54).base + 396#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = sp0 + 144#64 ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

@[expose] public def ERet2Sat (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonSat s0 sp0 s ∧
  s.pc = b + bv% (offExtract + 396) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F ∧
  HmacSt s.mem (sp0 + 184#64) F (x.prk F) []

@[expose] public def EPostSat (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = x.prk F ∧
  HmacSt s'.mem (s0.readReg64 .x0 + 0x20#64) F (x.prk F) [] ∧
  ExtFrameSat s0 sp0 s'.mem

private theorem extract_salt_props {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64} {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 720#64) 1152) (sp0 - 720#64) 1152 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 720#64) 1152) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 720#64) 1152 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 720#64) 1152 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 720#64) 1152 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 720#64) 1152 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

/-- `S2Frame`-relaxed `320`-byte-stack postcondition of `finalize_fixed` (definitionally identical
to `FinalizeFixedSat.FinPostSat`). -/
@[expose] public def FinPostS2 (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  S2Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)]

theorem FinPostS2.of_finPost {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} {s0 s' : State}
    (h : FinPost F key msg s0 s') : FinPostS2 F key msg s0 s' := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, (S2Frame.of_frame h.2.2.2.2).mono fun a ha r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha (s0.readReg64 .x0, 32) (by simp)
  · exact ha (s0.readReg64 .x1, 0x90) (by simp)
  · have ha320 := ha (s0.sp - 320#64, 320) (by simp)
    unfold OutsideRegion at ha320 ⊢; bv_omega

public theorem nfs_runsTo_placed_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {s : State} {ret keyRegA keyA : BitVec 64} {key : List (BitVec 8)}
    (hInv : Inv s.mem)
    (hpc : s.pc = lsmpl.base 114)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyRegA)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 key.length)
    (hkey_len : key.length ≤ 32)
    (hkey_pts : (keyRegA ↦ₛ key) = (keyA ↦ₛ key))
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 720#64) 720)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 720#64) 720)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 720#64) 720)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 720#64, 720)]) := by
  intro hL
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyRegA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStackSat
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 ret 0x98 (fun _ => True) := IsBlock.memRegion ret 0x98
  have hb2 : IsBlock P2 keyA key.length
      (fun m => key.length ≤ 2 ^ 64 ∧ m.readBytes keyA key.length = key) :=
    IsBlock.pointsToBytes keyA key
  have hb3 : IsBlock P3 (s.sp - 720#64) 720 (fun _ => True) := IsBlock.memRegion (s.sp - 720#64) 720
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : RW s.mem keyA key.length :=
    fun a ha => hrw_key a (by simp only [InRegion] at ha ⊢; omega)
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length :=
    ⟨hd_ret_key.1, Nat.le_trans hkey_len hd_ret_key.2⟩
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 720#64) 720 :=
    ⟨Nat.le_trans hkey_len hd_key_stk.1, hd_key_stk.2⟩
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, hkey_mem⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre_sat : s.mem ⊨
      ({ newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }).pre xg s ∗ R := by
    dsimp only []
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hInv, ?_⟩
    rw [newFromSliceSpecSat]
    dsimp only [xg]
    rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hkey_le64⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full hNfs xg R hpc hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [newFromSliceSpecSat] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [newFromSliceSpecSat] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [newFromSliceSpecSat] at ho; rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, ⟨⟩⟩⟩
  dsimp only [newFromSliceSpecSat, xg] at hpost_sat
  rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1_tag : IsBlock (ret ↦₆₄ 0#64) ret 8 (fun m => m.read64 ret = 0#64) :=
    IsBlock.pointsTo64 ret 0#64
  have hb1_hm : IsBlock (hmacCoreAt C.F (ret + 8#64) key []) (ret + 8#64) 0x90
      (fun m => HmacSt m (ret + 8#64) C.F key []) :=
    isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide)
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    hb1_tag.sepConj hb1_hm rfl (by decide)
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by
    dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by
    ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hmc_map := hmc.2.2
  replace hmc := hmc.1
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 720#64, 720)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans hkey_mem.symm) hmc hmc_map
  exact ⟨s', hsteps, ⟨htr, CallingConventionPreserved.vregs hcc⟩, ⟨hpc', hstat', hcc, hok, hhm, hframe⟩,
    hsteps.codeLoaded hL⟩

public theorem nfs32_runsTo_placed_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hInv : Inv s.mem)
    (hpc : s.pc = lsmpl.base 114)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 720#64) 720)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 720#64) 720)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 720#64) 720)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 720#64, 720)]) :=
  nfs_runsTo_placed_sat hNfs hInv hpc hstat hx0 hx1 (by rw [hx2, hkey_len])
    (by omega) rfl (by rwa [hkey_len]) hrw_ret hrw_key hrw_stk hd_ret_key hd_ret_stk hd_key_stk hsp_al

section SegmentsPlacedExact

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

public theorem seg0_placed_runsTo_sat {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = (blkPl_54).base)
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 720#64) 1152) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s0 (ENfs1PlacedSat x s0 sp0) := by
  have hsub_976 : 0 < 976 ∧ ((sp0 - 544#64) - (sp0 - 720#64)).toNat + 976 ≤ 1152 := by
    have heq : (sp0 - 544#64) - (sp0 - 720#64) = 176#64 := by bv_lin
    rw [heq]; decide
  have h0 := seg0_placed_runsTo (H := H)
    hpc hstat hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_some sv hsv).1, (hsalt_some sv hsv).2.1,
      disj_stkSat_sub_right (hsalt_some sv hsv).2.2 (sp0 - 544#64) 976 hsub_976⟩)
  refine h0.mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  have hset0 : s0.setMem s0.mem = s0 := by cases s0; rfl
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved',
    ExtFrameSat.of_extFrame (S2Frame.refl s0.mem _) (by rw [hset0]; exact hframe')⟩, hrest⟩

public theorem nfs1_placed_runsTo_sat {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hInv : Inv s.mem)
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_720 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 720#64) 720)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1PlacedSat x s0 sp0 s) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (ERet1Sat extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 720#64)).toNat + 0x98 ≤ 1152 := by
    have heq : (sp0 + 176#64) - (sp0 - 720#64) = 896#64 := by bv_lin
    rw [heq]; decide
  have hsub_720 : 0 < 720 ∧ ((sp0 - 720#64) - (sp0 - 720#64)).toNat + 720 ≤ 1152 := by
    have heq : (sp0 - 720#64) - (sp0 - 720#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 720#64)).toNat + 96 ≤ 1152 := by
    have heq : (sp0 + 336#64) - (sp0 - 720#64) = 1056#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs_runsTo_placed_sat hNfs hInv
    hpc hstat hx0 hx1 hx2
    (saltSliceOf_length_le x)
    (pointsToBytes_saltRegOf_eq sp0 x hsalt_some_ne)
    hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_720.2))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 720#64 720 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_720)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 720#64 720 336#64 96 (by decide)
  have hframe' : ExtFrameSat s0 sp0 s'.mem :=
    ExtFrameSat.trans_pair hframe hfr' hsub_x0.2 hsub_720.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (offExtract + 80) := by
    rw [hlr, extPlacedFakeB_off_80]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

public theorem seg1a_placed_runsTo_sat {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1Sat extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyPlacedSat C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_976 : ((sp0 - 544#64) - (sp0 - 720#64)).toNat + 976 ≤ 1152 := by
    have heq : (sp0 - 544#64) - (sp0 - 720#64) = 176#64 := by bv_lin
    rw [heq]; decide
  have hrw_976 : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_976)
  have hs_cx : ERet1 extPlacedFakeB C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx20, hx21, hok, hhm⟩
  refine (seg1a_placed_runsTo (C := C) (H := H) hrw_976 hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameSat.of_extFrame hframe hframe'⟩, hrest⟩

/-- `HookSatExactMemcpy` (`∀ c : MemcpyClobber`) sibling of `Extract.seg1b_placed_runsTo`
(`ExtractSegs.lean:1001`) at `1152`-byte `extractStackSat`. -/
public theorem seg1b_placed_runsTo_exact (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 720#64) 1152)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlacedSat C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88Sat extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hsp_s : s.spAligned = true := by
    simpa [State.spAligned, hsp] using hsp_al
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hsub_432 : (sp0 - (sp0 - 720#64)).toNat + 432 ≤ 1152 := by
    have heq : sp0 - (sp0 - 720#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_32 : 0 < 32 ∧ (sp0 - (sp0 - 720#64)).toNat + 32 ≤ 1152 := by
    have heq : sp0 - (sp0 - 720#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkSat_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 :=
    hrw_sp0_s.sub (by bv_omega)
  have hread_ikm_s : s.mem.Readable x.ikmA 32 :=
    readable_of_rw (hframe.rw_of_rw x.ikmA 32 hRW_ikm)
  have hdisj_ikm : 32 = 0 ∨ DisjointRegions sp0 32 x.ikmA 32 :=
    Or.inr (disj_stkSat_sub_right hd_ikm_stk sp0 32 hsub_32).symm
  refine s2_memcpy_step_placed_of_exact H h_mc
    hstat hsp_s hpc hx0 hx1 (by rw [hx2]; rfl) hlr hikm_s hrw_sp0_32 hread_ikm_s hdisj_ikm
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  have hag_mc : AgreesOutside s.mem (s.mem.writeBytes sp0 x.ikm) sp0 328 :=
    (ProofLib.AgreesOutside.writeBytes_self s.mem sp0 x.ikm).mono (by omega)
  have hrw_sp0 : (s.mem.writeBytes sp0 x.ikm).RW sp0 432 :=
    rw_of_perm_eq hag_mc.2 hrw_sp0_s
  iterate 3 s2_step
  refine RunsTo.refl ?_ ⟨rfl, rfl⟩
  have hag : AgreesOutside s.mem ((s.mem.writeBytes sp0 x.ikm).write8 (sp0 + 63#64) 32#8) sp0 328 :=
    agreesOutside_sp0_write8 hag_mc (by decide)
  unfold EC88Sat ExtCommonSat
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.advancePC, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    hsaved.of_agreesOutside_328 hag,
    ExtFrameSat.of_agreesOutside_sp0 hframe (by decide) hag⟩,
    rfl, hx22, HmacSt.of_writeBytes_32_write8_pos hhm hikm_len⟩

public theorem seg1c_placed_runsTo_sat {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88Sat extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EFinPlacedSat C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_976 : ((sp0 - 544#64) - (sp0 - 720#64)).toNat + 976 ≤ 1152 := by
    have heq : (sp0 - 544#64) - (sp0 - 720#64) = 176#64 := by bv_lin
    rw [heq]; decide
  have hrw_976 : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_976)
  have hs_cx : EC88 extPlacedFakeB C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hhm⟩
  refine (seg1c_placed_runsTo (C := C) (H := H) hrw_976 hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameSat.of_extFrame hframe hframe'⟩, hrest⟩

/-- `FinPostS2` (`320`-byte stack `S2Frame`) sibling of `Extract.fin_placed_runsTo`. -/
public theorem fin_placed_runsTo_s2 {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hFin :
      FinPreSat finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
        (FinPostS2 C.F (effectiveSalt x.salt) x.ikm s))
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinPlacedSat C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ERetFinSat extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 720#64)).toNat + 32 ≤ 1152 := by
    have heq : (sp0 + 144#64) - (sp0 - 720#64) = 864#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 720#64)).toNat + 0x90 ≤ 1152 := by
    have heq : (sp0 + 176#64) - (sp0 - 720#64) = 896#64 := by bv_lin
    rw [heq]; decide
  have hsub_m320 : 0 < 320 ∧ ((sp0 - 320#64) - (sp0 - 720#64)).toNat + 320 ≤ 1152 := by
    have heq : (sp0 - 320#64) - (sp0 - 720#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 720#64)).toNat + 96 ≤ 1152 := by
    have heq : (sp0 + 336#64) - (sp0 - 720#64) = 1056#64 := by bv_lin
    rw [heq]; decide
  have hrw_336 : RW s.mem (sp0 + 336#64) 96 :=
    hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_336)
  have hpre : FinPreSat finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s :=
    FinPreSat.of_320
      (hpc.trans finPlacedFakeB_off_0.symm)
      hstat
      (by rw [effectiveSalt_length]; decide)
      (by omega)
      (by rw [hx1]; exact hhm)
      (by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_144.2))
      (by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_176.2))
      (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_m320.2))
      (by rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide))
      (by rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 320#64 320 144#64 32 (by decide)).symm)
      (by rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 320#64 320 176#64 0x90 (by decide)).symm)
      (by rw [hsp]; exact sp0_aligned_0b1111 hsp_al)
  refine (hFin hpre).mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' hrw_336 ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 320#64 320 336#64 96 (by decide)
  have hframe' : ExtFrameSat s0 sp0 s'.mem :=
    ExtFrameSat.trans_triple hframe hfr' hsub_144.2 hsub_176.2 hsub_m320.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (offExtract + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

public theorem seg2_placed_runsTo_sat {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERetFinSat extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ENfs2PlacedSat C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hprk⟩
  have hs_cx : ERetFin extPlacedFakeB C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hprk⟩
  refine (seg2_placed_runsTo (C := C) (H := H) hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameSat.of_extFrame hframe hframe'⟩, hrest⟩

public theorem nfs2_placed_runsTo_sat {Inv : Memory → Prop}
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hInv : Inv s.mem)
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2PlacedSat C.F x s0 sp0 s) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s (ERet2Sat extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 720#64)).toNat + 32 ≤ 1152 := by
    have heq : (sp0 + 144#64) - (sp0 - 720#64) = 864#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 720#64)).toNat + 0x98 ≤ 1152 := by
    have heq : (sp0 + 176#64) - (sp0 - 720#64) = 896#64 := by bv_lin
    rw [heq]; decide
  have hsub_720 : 0 < 720 ∧ ((sp0 - 720#64) - (sp0 - 720#64)).toNat + 720 ≤ 1152 := by
    have heq : (sp0 - 720#64) - (sp0 - 720#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 720#64)).toNat + 96 ≤ 1152 := by
    have heq : (sp0 + 336#64) - (sp0 - 720#64) = 1056#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_runsTo_placed_sat hNfs hInv
    hpc hstat hx0 hx1 hx2
    hprk_len
    hprk
    (hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_x0.2))
    hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_720.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 720#64 720 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 720#64 720 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact disj_sp0_sub_off sp0 720#64 720 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 720#64 720 336#64 96 (by decide)
  have hframe' : ExtFrameSat s0 sp0 s'.mem :=
    ExtFrameSat.trans_pair hframe hfr' hsub_x0.2 hsub_720.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (offExtract + 396) := by
    rw [hlr, extPlacedFakeB_off_396]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

public theorem seg3_placed_runsTo_sat {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 720#64) 1152)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 720#64) 1152)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet2Sat extPlacedFakeB C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EPostSat C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hok, hprk, hhm⟩
  have hsub_976 : 0 < 976 ∧ ((sp0 - 544#64) - (sp0 - 720#64)).toNat + 976 ≤ 1152 := by
    have heq : (sp0 - 544#64) - (sp0 - 720#64) = 176#64 := by bv_lin
    rw [heq]; decide
  have hrw_out_s : RW (s0.setMem s.mem).mem ((s0.setMem s.mem).readReg64 .x0) 0xb0 :=
    hframe.rw_of_rw (s0.readReg64 .x0) 0xb0 hRW_out
  have hrw_976_s : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkSat_sub hRW_stk _ _ hsub_976.2)
  have hd_out_976 : DisjointRegions ((s0.setMem s.mem).readReg64 .x0) 0xb0 (sp0 - 544#64) 976 :=
    disj_stkSat_sub_right hd_out_stk (sp0 - 544#64) 976 hsub_976
  have hs_cx : ERet2 extPlacedFakeB C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hok, hprk, hhm⟩
  refine (seg3_placed_runsTo (C := C) (H := H) (s0 := s0.setMem s.mem)
    hsp0 hrw_out_s hrw_976_s hd_out_976 hsp_al hs_cx).mono
    fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcallee, hprk', hhm', hframe'⟩
  exact ⟨hpc', hstat', hcallee, hprk', hhm', ExtFrameSat.of_extFrame hframe hframe'⟩

end SegmentsPlacedExact

/-- `HookSatExactMemcpy` sibling of `extract_placed_ok_of_inv` at `1152`-byte `extractStackSat`. -/
public theorem extract_placed_ok_of_inv_exact [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks)
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      LibsignalCodeLoaded lsmpl s.mem →
      FinPreSat finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (FinPostS2 C.F key msg s))
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpecSat C.F with pre := fun x s0 => (newFromSliceSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      { extractSpecSat C.F with pre := fun x s0 => (extractSpecSat C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ } := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [extractSpecSat] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hInv0, ⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hInv_cl hInv0
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m1152 : s0.sp - 1152#64 = sp0 - 720#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 1152#64) 1152) ∗ R at hsep
  rw [hsp_m1152] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 720#64) 1152
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 720#64) 1152 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 720#64) 1152 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 720#64) 1152 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 720#64) 1152 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 720#64) 1152 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 720#64) 1152 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 720#64) 1152 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 720#64)).toNat + 432 ≤ 1152 := by
    have heq : sp0 - (sp0 - 720#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stkSat_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 720#64)).toNat + 32 ≤ 1152 := by
    have heq : (sp0 + 144#64) - (sp0 - 720#64) = 864#64 := by bv_lin
    rw [heq]; decide
  have hsub_720 : 0 < 720 ∧ ((sp0 - 720#64) - (sp0 - 720#64)).toNat + 720 ≤ 1152 := by
    have heq : (sp0 - 720#64) - (sp0 - 720#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 720#64)).toNat + 0x98 ≤ 1152 := by
    have heq : (sp0 + 176#64) - (sp0 - 720#64) = 896#64 := by bv_lin
    rw [heq]; decide
  have hsalt_props := extract_salt_props hb_stk hsep
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stkSat_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_720 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 720#64) 720 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 720#64 720 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stkSat_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 720#64) 720 hsub_720
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stkSat_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := RunsTo.toE (seg0_placed_runsTo_sat (H := H)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_placed_runsTo_sat hNfs (hInv_kf hInv0 hkf) hRW_stk hRW_salt hd_salt_720 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_placed_runsTo_sat hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    RunsTo.toE (seg1b_placed_runsTo_exact (C := C) h_mc
      hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_placed_runsTo_sat hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    RunsTo.toE (fin_placed_runsTo_s2
      (fun hpre => hFin (fun i hi hunmut ext panics svc => (hcl0 i hi hunmut ext panics svc).of_keepsFrozen hkf) hpre)
      hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_placed_runsTo_sat hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo_sat hNfs (hInv_kf hInv0 hkf) hRW_stk hsp_al hs
  have h8 := h7.trans fun s hs =>
    RunsTo.toE (seg3_placed_runsTo_sat hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)
  refine h8.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [extractSpecSat]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrameSat at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hb_prk := IsBlock.pointsToBytes_len (a := x.ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [])
      x.ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes x.ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (x.ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 720#64) 1152 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 1152#64) 1152) ∗ R
  rw [hsp_m1152]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `HookSatExactMemcpy` sibling of `extract_placed_ok` (`Extract.lean:1259`) at `1152`-B stack. -/
public theorem extract_placed_ok_exact [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks)
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      LibsignalCodeLoaded lsmpl s.mem →
      FinPreSat finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (FinPostS2 C.F key msg s))
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpecSat C.F))) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)) :=
  extract_placed_ok_of_inv_exact C H h_mc hFin
    (fun hcl hkf i hi hunmut ext panics svc => (hcl i hi hunmut ext panics svc).of_keepsFrozen hkf)
    (fun hcl => hcl)
    hNfs

/-- `HookSatExactMemcpy` sibling of `extract_placed_ok_of_plain` (`Extract.lean:1271`) at `1152`-B stack. -/
public theorem extract_placed_ok_of_plain_exact [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks)
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      LibsignalCodeLoaded lsmpl s.mem →
      FinPreSat finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (FinPostS2 C.F key msg s))
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (newFromSliceSpecSat C.F)) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      (withLsCodeLoaded lsmpl (extractSpecSat C.F)) :=
  extract_placed_ok_exact C H h_mc hFin (subroutine_ok_withLsCodeLoaded_of_plain hNfs)

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact
