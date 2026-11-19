/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `<GenericHkdf<Hmac<Sha256>>>::expand_multi_info`

Assembles the Block 1, loop-iteration, and `finalize_fixed` segment proofs to establish
`expandMultiInfoSpec` on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and under
`[LibsignalPlacement]`.
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Expand

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Relocatable `[LibsignalPlacement]` Assembly -/

section AssemblyPlaced

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem ExpandFrame.keepsFrozen {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (hf : ExpandFrame okmLen s₀ m) :
    KeepsFrozenNoAnon s₀.mem m := by
  refine KeepsFrozenNoAnon.of_perm_eq hf.2.1 hf.2.2.2.1 fun a hperm => ?_
  refine hf.1 a (fun r hr => ?_)
  rw [outsideRegion_iff_not_inRegion]
  intro hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_x2 a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm
  · have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_stack a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm

theorem expand_multi_info_placed_runsTo_of_fin
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      ExpandFrame okmLen s₀ s.mem →
      FinalizeFixedProof.FinPre finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (FinalizeFixedProof.FinPost C.F key msg s))
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine (seg0_placed_runsTo hpre).trans fun s1 hs1 => ?_
  refine (seg1_placed_runsTo hpre hs1).trans fun s2 hs2 => ?_
  refine (seg2a_placed_runsTo hpre hs2).trans fun s3 hs3 => ?_
  refine (seg2b_placed_runsTo hpre hs3).trans fun s4 hs4 => ?_
  refine (fin1_placed_runsTo hFin hpre hs4).trans fun s5 hs5 => ?_
  refine (seg3_placed_runsTo hpre hs5).trans fun s6 hs6 => ?_
  rcases hpre.okm_len with rfl | rfl
  · refine (iter_to_fin_placed_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans
      fun s7 hs7 => ?_
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by simp), hkdfExpand_64_eq]
    refine (iter_d_done_placed_runsTo hpre (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs7).trans fun s8 hs8 => ?_
    exact epilogue_placed_runsTo hpre hs8
  · refine (iter_to_fin_placed_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hs6).trans
      fun s7 hs7 => ?_
    refine (iter_d_continue_placed_runsTo (tNext := t2 C.F prk info) hpre rfl (by decide) rfl hs7).trans
      fun s8 hs8 => ?_
    refine (iter_to_fin_placed_runsTo hFin hpre (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hs8).trans
      fun s9 hs9 => ?_
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    refine (iter_d_done_placed_runsTo hpre (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs9).trans fun s10 hs10 => ?_
    exact epilogue_placed_runsTo hpre hs10

theorem expand_multi_info_placed_runsTo
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine expand_multi_info_placed_runsTo_of_fin (fun hf hfin_pre => ?_) hpre
  have hkf : KeepsFrozenNoAnon s₀.mem _ := ExpandFrame.keepsFrozen hpre hf
  have hcl_s : LibsignalCodeLoaded lsmpl _ :=
    fun i hi hunmut ext panics svc => Program.CodeLoaded.of_keepsFrozenNoAnon (hcl i hi hunmut ext panics svc) hkf
  exact FinalizeFixedProof.finalize_fixed_placed_runsTo_of_other_block hcl_s hfin_pre

end AssemblyPlaced
end Expand

/-! ## Separation Logic Bridge and Top-Level `expand_multi_info_ok` -/

open Expand in
theorem ro_outside_rw_shared_lb {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hQPR : m ⊨ Q ∗ (P ∗ R) := by rwa [sepConj_left_comm]
  have hperm : m.perm a = some Perm.rw := hrw.perm_rw hQPR ha_rw
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    hrw.update (IsBlock.memRegion b_rw n_rw) (Nat.le_refl _) hQPR
      (AgreesOutside.rfl' m b_rw n_rw) trivial
  have hm_lf := Satisfies.madvFreeNonFrozen hm_reg
  rw [sepConj_left_comm] at hm_lf
  have hfalse := hro.isLazyFree_false hm_lf ha_ro
  rw [Memory.isLazyFree_madvFreeNonFrozen] at hfalse
  have hin : (a - b_rw).toNat < n_rw := ha_rw
  have hcond : ((some Perm.rw).mapped && !(some Perm.rw).frozen) = true := rfl
  simp only [hin, hperm, decide_true, Bool.true_and, hcond, ↓reduceIte] at hfalse
  cases hfalse

/-- Relocatable `[LibsignalPlacement]` contract predicate for `expand_multi_info`. -/
@[expose] def ExpandMultiInfoPlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
    (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F))

open Expand in
theorem expand_multi_info_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    ExpandMultiInfoPlacedOk C H := by
  unfold ExpandMultiInfoPlacedOk
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [expandMultiInfoSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have h_exp_pre : ExpandPre expPlacedFakeB C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_placed_runsTo (H := H) hcl h_exp_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeLoaded, expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, Expand.hkdfExpand_64_eq]
      simp [Expand.t1_length, Expand.t2_length]
    · rw [h80, Expand.hkdfExpand_80_eq]
      simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end CryptoVerification.LibsignalTripleRatchet
