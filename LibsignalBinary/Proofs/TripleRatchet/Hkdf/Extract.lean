/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `<GenericHkdf<Hmac<Sha256>>>::extract`

Assembles segment proofs for `GenericHkdf<Hmac<Sha256>>::extract` to establish
`extractSpec` on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and under
`[LibsignalPlacement]`.
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Extract

private theorem extract_salt_props {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64} {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 544#64) 976) (sp0 - 544#64) 976 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 544#64) 976) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 544#64) 976 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

namespace HkdfExt.ExtractX

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

open Extract HkdfExt

abbrev ExtFrameX (s0 : State) (sp0 : BitVec 64) (m : Memory) : Prop :=
  S2Frame s0.mem m [(s0.readReg64 .x0, 0xb0), (sp0 - 16928#64, 17360)]

theorem rw_stkX_sub {m : Memory} {sp0 : BitVec 64}
    (hrw : RW m (sp0 - 16928#64) 17360) (addr : BitVec 64) (sz : ℕ)
    (hsub : (addr - (sp0 - 16928#64)).toNat + sz ≤ 17360) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

theorem rw_sp0_sub {m : Memory} {sp0 : BitVec 64}
    (hrw : RW m sp0 432) (addr : BitVec 64) (sz : ℕ)
    (hsub : (addr - sp0).toNat + sz ≤ 432) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

theorem disj_stkX_sub_right {a : BitVec 64} {n : ℕ} {sp0 : BitVec 64}
    (hd : DisjointRegions a n (sp0 - 16928#64) 17360) (addr : BitVec 64) (sz : ℕ)
    (hsub : 0 < sz ∧ (addr - (sp0 - 16928#64)).toNat + sz ≤ 17360) :
    DisjointRegions a n addr sz :=
  hd.sub_right addr hsub

theorem ExtSaved.changeSetMem {s0 : State} {sp0 : BitVec 64} {m1 m : Memory} :
    ExtSaved (s0.setMem m1) sp0 m ↔ ExtSaved s0 sp0 m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem ExtFrameX.of_extFrame {s0 : State} {sp0 : BitVec 64} {m1 m2 : Memory}
    (hf1 : ExtFrameX s0 sp0 m1) (hf2 : ExtFrame (s0.setMem m1) sp0 m2) :
    ExtFrameX s0 sp0 m2 := by
  refine hf1.trans (hf2.mono fun a ha => ?_)
  have hout : OutsideRegion (s0.readReg64 .x0) 0xb0 a :=
    ha (s0.readReg64 .x0, 0xb0) (by simp)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  intro r hr
  simp only [State.readReg64_setMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · simp only [OutsideRegion] at hstk ⊢
    bv_omega

theorem ExtFrameX.of_agreesOutside_sp0 {s0 : State} {sp0 : BitVec 64} {m m' : Memory} {n : ℕ}
    (hf : ExtFrameX s0 sp0 m) (hn : n ≤ 432) (hag : AgreesOutside m m' sp0 n) :
    ExtFrameX s0 sp0 m' := by
  refine hf.trans ((S2Frame.of_frame (frame_of_agreesOutside hag)).mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem ExtFrameX.trans_pair {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ}
    (hf₁ : ExtFrameX s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp0 - 16928#64)).toNat + n₁ ≤ 17360)
    (hsub₂ : (a₂ - (sp0 - 16928#64)).toNat + n₂ ≤ 17360) :
    ExtFrameX s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega⟩

theorem ExtFrameX.trans_triple {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ} {a₃ : BitVec 64} {n₃ : ℕ}
    (hf₁ : ExtFrameX s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 16928#64)).toNat + n₁ ≤ 17360)
    (hsub₂ : (a₂ - (sp0 - 16928#64)).toNat + n₂ ≤ 17360)
    (hsub₃ : (a₃ - (sp0 - 16928#64)).toNat + n₃ ≤ 17360) :
    ExtFrameX s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem hmacSt_of_memcpy_32_write8_pos {m m1 : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key ikm : List (BitVec 8)}
    (hhm : HmacSt m sp0 F key [])
    (hrw : RW m sp0 432)
    (hikm_len : ikm.length = 32)
    (hdst1 : m1.readBytes sp0 32 = ikm)
    (hfr_mc : S2Frame m m1 [(sp0, 32), (sp0 - 16384#64, 16384)]) :
    HmacSt (m1.write8 (sp0 + 63#64) 32#8) sp0 F key ikm := by
  let m2 := m1.write8 (sp0 + 63#64) 32#8
  have hag2 : AgreesOutside m1 m2 (sp0 + 63#64) 1 :=
    (AgreesOutside.rfl' m1 (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf2 : S2Frame m1 m2 [(sp0 + 63#64, 1)] :=
    S2Frame.of_frame (frame_of_agreesOutside hag2)
  have hfr64 : S2Frame m m2 [(sp0, 64), (sp0 - 16384#64, 16384)] := by
    refine (hfr_mc.mono fun a ha => ?_).trans (hf2.mono fun a ha => ?_)
    · have h64 : OutsideRegion sp0 64 a := ha (sp0, 64) (by simp)
      have hext : OutsideRegion (sp0 - 16384#64) 16384 a := ha (sp0 - 16384#64, 16384) (by simp)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [OutsideRegion] at h64 ⊢; bv_omega
      · exact hext
    · have h64 : OutsideRegion sp0 64 a := ha (sp0, 64) (by simp)
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [OutsideRegion] at h64 ⊢; bv_omega
  have hrw1_32 : RW m1 sp0 32 :=
    hfr_mc.rw_of_rw sp0 32 (rw_sp0_sub hrw sp0 32 (by rw [BitVec.sub_self]; decide))
  have hd64 (off : BitVec 64) (sz : ℕ)
      (h1 : 64 ≤ off.toNat ∧ sz ≤ (0#64 - off).toNat)
      (h2 : 16384 ≤ (off + 16384#64).toNat ∧ sz ≤ (0#64 - (off + 16384#64)).toNat) :
      ∀ r ∈ [(sp0, (64 : ℕ)), (sp0 - 16384#64, 16384)], DisjointRegions r.1 r.2 (sp0 + off) sz := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 64 off sz h1
    · exact disj_sp0_sub_off sp0 16384#64 16384 off sz h2
  have hsub_40 : ((sp0 + 0x40#64) - sp0).toNat + 32 ≤ 432 := by
    have h : (sp0 + 0x40#64) - sp0 = 0x40#64 := by bv_lin
    rw [h]; decide
  have hsub_60 : ((sp0 + 0x60#64) - sp0).toNat + 8 ≤ 432 := by
    have h : (sp0 + 0x60#64) - sp0 = 0x60#64 := by bv_lin
    rw [h]; decide
  have hsub_68 : ((sp0 + 0x68#64) - sp0).toNat + 32 ≤ 432 := by
    have h : (sp0 + 0x68#64) - sp0 = 0x68#64 := by bv_lin
    rw [h]; decide
  have hsub_88 : ((sp0 + 0x88#64) - sp0).toNat + 8 ≤ 432 := by
    have h : (sp0 + 0x88#64) - sp0 = 0x88#64 := by bv_lin
    rw [h]; decide
  rcases hhm with ⟨_, _, _, hin, hinB, hout, houtB⟩
  change HmacSt m2 sp0 F key ikm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hikm_len, hf2.readBytes_eq hrw1_32 ?_ (by decide), hdst1]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (disj_sp0_zero_off sp0 32 63#64 1 (by decide)).symm
  · dsimp [m2]
    rw [Memory.read8_write8_same, hikm_len]
  · rw [hfr64.readBytes_eq (rw_sp0_sub hrw (sp0 + 0x40#64) 32 hsub_40)
      (hd64 0x40#64 32 (by decide) (by decide)) (by decide), hin]
  · rw [hfr64.read64_eq (rw_sp0_sub hrw (sp0 + 0x60#64) 8 hsub_60)
      (hd64 0x60#64 8 (by decide) (by decide)), hinB]
  · rw [hfr64.readBytes_eq (rw_sp0_sub hrw (sp0 + 0x68#64) 32 hsub_68)
      (hd64 0x68#64 32 (by decide) (by decide)) (by decide), hout]
  · rw [hfr64.read64_eq (rw_sp0_sub hrw (sp0 + 0x88#64) 8 hsub_88)
      (hd64 0x88#64 8 (by decide) (by decide)), houtB]

abbrev ExtCommonX (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  s.status = .Running ∧
  s.sp = sp0 ∧
  s.readReg64 .x19 = s0.readReg64 .x0 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x29 = sp0 + 336#64 ∧
  ExtSaved s0 sp0 s.mem ∧
  ExtFrameX s0 sp0 s.mem

@[expose] def EPostX (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = x.prk F ∧
  HmacSt s'.mem (s0.readReg64 .x0 + 0x20#64) F (x.prk F) [] ∧
  ExtFrameX s0 sp0 s'.mem

section SegmentsX

end SegmentsX

theorem extract_salt_props_x {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64} {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 16928#64) 17360) (sp0 - 16928#64) 17360 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 16928#64) 17360) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 16928#64) 17360 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 16928#64) 17360 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

end HkdfExt.ExtractX

/-- Relocatable `[LibsignalPlacement]` contract predicate for `extract`. -/
abbrev ExtractPlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
    (withLsCodeLoaded lsmpl (extractSpec C.F))

/-- Relocatable `subroutine_ok` for `extract` parameterized by any frozen-preserved
memory invariant `Inv` implying `LibsignalCodeLoaded lsmpl`. -/
theorem extract_placed_ok_of_inv [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      { extractSpec C.F with pre := fun x s0 => (extractSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ } := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [extractSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hInv0, ⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hInv_cl hInv0
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R at hsep
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsalt_props := extract_salt_props hb_stk hsep
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stk_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 544#64) 544 hsub_544
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := RunsTo.toE (seg0_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_placed_runsTo hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    RunsTo.toE (seg1b_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    RunsTo.toE (fin_placed_runsTo
      (fun hpre => FinalizeFixedProof.finalize_fixed_placed_runsTo_of_other_block
        (fun i hi hunmut ext panics svc => (hcl0 i hi hunmut ext panics svc).of_keepsFrozen hkf) hpre)
      hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_placed_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hsp_al hs
  have h8 := h7.trans fun s hs =>
    RunsTo.toE (seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)
  refine h8.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [extractSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
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
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem extract_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F))) :
    ExtractPlacedOk C H :=
  extract_placed_ok_of_inv C H
    (fun hcl hkf i hi hunmut ext panics svc => (hcl i hi hunmut ext panics svc).of_keepsFrozen hkf)
    (fun hcl => hcl)
    hNfs

theorem extract_placed_ok_of_plain [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (newFromSliceSpec C.F)) :
    ExtractPlacedOk C H :=
  extract_placed_ok C H (subroutine_ok_withLsCodeLoaded_of_plain hNfs)

end CryptoVerification.LibsignalTripleRatchet
