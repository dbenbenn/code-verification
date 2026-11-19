/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight -- proof-setup: allow-public-import
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import ProofLib.RegChain
import ProofLib.Sep
import ProofLib.SepLogic.WPp

/-!
# Tight-Panic Segment S3 (`DhStep`) Block WP Instances & Step Lemmas

Proves relocatable `DhStepBlockWp` instances for blocks `130` and `433` and placed step lemmas:
every panic in `DhStep` is an allocator failure, discharging `tryDecryptOnPanicTight` via
`spqrNoPanic`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
open CryptoVerification.LibsignalSession

namespace P3kR1bd

/-- Dummy `SpqrModel` that never panics in `recvPanics` and always returns `.error true` in `recv`. -/
@[expose] def spqrNoPanic : SpqrModel where
  send := fun _ _ => none
  draws := fun _ _ => 0
  recv := fun _ _ => .error true
  recvPanics := fun _ _ => false
  sendPanics := fun _ _ => false

/-- If `x.model` panics under `spqrNoPanic`, it panics before `spqr::recv` is reached, so it panics
under any `S : SpqrModel`. -/
theorem model_fst_eq_panic_of_spqrNoPanic (C : Crypto) (S : SpqrModel) (x : TryDecryptGhost)
    (h : (x.model C spqrNoPanic uuidTryParse).1 = .error .panic) :
    (x.model C S uuidTryParse).1 = .error .panic := by
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk res st1 =>
    cases res with
    | error e =>
      rw [(model_of_fromSessionState_error htr).1] at h ⊢
      exact h
    | ok tr =>
      cases herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | mk res1 r1 =>
        cases res1 with
        | error e =>
          rw [model_of_ensureReceiverChain_error htr herc] at h ⊢
          exact h
        | ok ck =>
          cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
              x.msg.counter x.msgType) r1 with
          | mk res2 r2 =>
            cases res2 with
            | error e =>
              rw [model_of_cmk_error htr herc hcmk] at h ⊢
              exact h
            | ok mkg =>
              have hspqr : spqrNoPanic.recv tr.pqrState x.msg.pqRatchet = .error true := rfl
              have hnp : spqrNoPanic.recvPanics tr.pqrState x.msg.pqRatchet = false := rfl
              rw [model_of_spqr_error htr herc hcmk hspqr hnp] at h
              nomatch h

/-- Any panic outcome against `spqrNoPanic` satisfies `tryDecryptOnPanicTight` for any `S`. -/
theorem onPanicTightPlaced_of_spqrNoPanic [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {x : TryDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse spqrNoPanic).onPanic x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  simp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | hpan | ha
  · exact Or.inl (model_fst_eq_panic_of_spqrNoPanic C S x hp)
  · nomatch hpan
  · exact Or.inr ha

end P3kR1bd

/-! ## Relocatable `[LibsignalPlacement]` `DhStepBlockWp` Instances for Block 130 and Block 433 -/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[expose] def dhStepBlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhStepBlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      (lsmpl.ρ "libsignal_session_rng_fill") where
  missingScAddr := lsmpl.ρ "libsignal_session:.rodata..Lanon.19"
  hro_missingSc := by
    intro m P hro hP
    exact lsro_slice_intro hro (sym := "libsignal_session:.rodata..Lanon.19") (off := 0)
      (by simp) (by decide +kernel) hP
  wpp_2dc_to_30c := by
    intro s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 u340 u2d0 u18c u188
      sp hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by ac_rfl) (Eq.trans this (by ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_7f8_to_2dc := by
    intro s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_missing_sc := by
    intro s0 s x u2c0 u2c8 sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_cc1_err := by
    intro s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc1_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_pre_cc1 := by
    intro s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
      sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_err := by
    intro s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_70c_to_778 := by
    intro s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510
      r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
      u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
      sp hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
    rw [show s0.sp - 96#64 = sp + 0x580#64 by dsimp only [sp]; bv_arith] at hx29
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], rfl, rfl, rfl, rfl, rfl,
       by simp [hx23, sp], by simp [hx25, sp], rfl, rfl, by simp [sp],
       by simp [hx29, sp]; bv_arith, rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_778_to_rng := by
    intro s0 s u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx1], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_780_to_7a8 := by
    intro s0 s b0 b31 sp hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, by simp [sp],
       rfl, rfl, rfl, rfl, rfl, by simp [sp], rfl, rfl, rfl, rfl,
       by simp [hx29], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    rw [clamp_byte0 b0, clamp_byte31 b31] at hm
    arm64_sep_close
  wpp_7a8_to_dpk := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx8, sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7b4_to_sd := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7c4_to_cc2 := by
    intro s0 s2 msgA sp hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2 htrace2
    wp_steps
    refine SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2], by simp [sp]; bv_arith, by simp,
       by simp [sp], by simp [sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace2], fun m R hm => ?_⟩
    simpa [emp_sepConj] using hm

@[expose] def dhStepBlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhStepBlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      (lsmpl.base 618) where
  missingScAddr := lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.19"
  hro_missingSc := by
    intro m P hro hP
    exact lsro_slice_intro hro (sym := "libsignal_cli_ratchet:.rodata..Lanon.19") (off := 0)
      (by simp) (by decide +kernel) hP
  wpp_2dc_to_30c := by
    intro s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 u340 u2d0 u18c u188
      sp hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by ac_rfl) (Eq.trans this (by ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_7f8_to_2dc := by
    intro s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_missing_sc := by
    intro s0 s x u2c0 u2c8 sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    dsimp only [sp] at hm ⊢; exact Satisfies.mono (by sep_interval) hm
  wpp_cc1_err := by
    intro s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc1_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_pre_cc1 := by
    intro s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
      sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_err := by
    intro s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_70c_to_778 := by
    intro s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510
      r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
      u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
      sp hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
    rw [show s0.sp - 96#64 = sp + 0x580#64 by dsimp only [sp]; bv_arith] at hx29
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], rfl, rfl, rfl, rfl, rfl,
       by simp [hx23, sp], by simp [hx25, sp], rfl, rfl, by simp [sp],
       by simp [hx29, sp]; bv_arith, rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_778_to_rng := by
    intro s0 s u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx1], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_780_to_7a8 := by
    intro s0 s b0 b31 sp hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, by simp [sp],
       rfl, rfl, rfl, rfl, rfl, by simp [sp], rfl, rfl, rfl, rfl,
       by simp [hx29], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    rw [clamp_byte0 b0, clamp_byte31 b31] at hm
    arm64_sep_close
  wpp_7a8_to_dpk := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx8, sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7b4_to_sd := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7c4_to_cc2 := by
    intro s0 s2 msgA sp hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2 htrace2
    wp_steps
    refine SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2], by simp [sp]; bv_arith, by simp,
       by simp [sp], by simp [sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace2], fun m R hm => ?_⟩
    simpa [emp_sepConj] using hm

theorem dhStep_step_70c_to_778_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (rk1 : RootKey) (rck : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 0x70c#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (_hx28 : s.readReg64 .x28 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64) 0x20 ∗
      ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
      ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
      ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s1, Steps prog s s1 ∧
      s1.pc = entry + 1912#64 ∧
      tryDecryptMidMetaPlaced s0 s1 ∧
      s1.readReg64 .x0 = sp + 0x190#64 ∧
      s1.readReg64 .x1 = 32#64 ∧
      s1.readReg64 .x19 = s.readReg64 .x19 ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x21 = s.readReg64 .x21 ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x23 = sp + 0x500#64 ∧
      s1.readReg64 .x25 = sp + 0x190#64 ∧
      s1.readReg64 .x26 = s.readReg64 .x26 ∧
      s1.readReg64 .x27 = s.readReg64 .x27 ∧
      s1.readReg64 .x28 = sp + 0x3d0#64 ∧
      s1.readVReg128 0#5 = 0#128 ∧
      (s1.mem ⊨
        memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
        memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
        memRegion (sp + 0x190#64) 0x20 ∗
        memRegion (sp + 0x1b0#64) 0x220 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗
        memRegion (sp + 0x400#64) 0xa0 ∗
        ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
        memRegion (sp + 0x4e0#64) 0x20 ∗
        memRegion (sp + 0x500#64) 0x80 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hrk1_len : (keyToBytes32 rk1).length = 32 := length_keyToBytes32 rk1
  have hrck_len : (chainKeyBytes rck).length = 36 := length_chainKeyBytes rck
  obtain ⟨r0, hr0⟩ : ∃ v, pack32 ((keyToBytes32 rk1).take 4) = v := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ v, pack64 (((keyToBytes32 rk1).drop 4).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ v, pack64 (((keyToBytes32 rk1).drop 12).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r3, hr3⟩ : ∃ v, pack64 (((keyToBytes32 rk1).drop 20).take 8) = v := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ v, pack32 ((keyToBytes32 rk1).drop 28) = v := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ v, pack64 ((chainKeyBytes rck).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ v, pack64 (((chainKeyBytes rck).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ v, pack32 (((chainKeyBytes rck).drop 16).take 4) = v := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ v, pack64 (((chainKeyBytes rck).drop 20).take 8) = v := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ v, pack64 ((chainKeyBytes rck).drop 28) = v := ⟨_, rfl⟩
  have h194_split : ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) =
      (((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
       ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗
       ((sp + 0x1b0#64) ↦₃₂ r4)) := by
    rw [pointsTo_32_as_4_8_8_8_4 (sp + 0x194#64) (keyToBytes32 rk1) hrk1_len,
        hr0, hr1, hr2, hr3, hr4,
        show sp + 0x194#64 + 4#64 = sp + 0x198#64 by bv_arith,
        show sp + 0x194#64 + 12#64 = sp + 0x1a0#64 by bv_arith,
        show sp + 0x194#64 + 20#64 = sp + 0x1a8#64 by bv_arith,
        show sp + 0x194#64 + 28#64 = sp + 0x1b0#64 by bv_arith]
  have h1b4_split : ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) =
      (((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗
       ((sp + 0x1c4#64) ↦₃₂ c2) ∗ ((sp + 0x1c8#64) ↦₆₄ c3) ∗
       ((sp + 0x1d0#64) ↦₆₄ c4)) := by
    rw [pointsTo_36_as_8_8_4_8_8 (sp + 0x1b4#64) (chainKeyBytes rck) hrck_len,
        hc0, hc1, hc2, hc3, hc4,
        show sp + 0x1b4#64 + 8#64 = sp + 0x1bc#64 by bv_arith,
        show sp + 0x1b4#64 + 16#64 = sp + 0x1c4#64 by bv_arith,
        show sp + 0x1b4#64 + 20#64 = sp + 0x1c8#64 by bv_arith,
        show sp + 0x1b4#64 + 28#64 = sp + 0x1d0#64 by bv_arith]
  rw [split_sp_20_for_stepA sp, h194_split, h1b4_split, split_1d8_for_stepA sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u510, u508, u500, u4d8, u4d0, u4c8, u4c0, u4bc, u4b4, u4ac, u4a4, u4a0,
    u448, u440, u408, u400, u3ec, u3e4, u3e0, u3d8, u3d0, u1c, u10, hmem⟩
  have hwp1 := hwp.wpp_70c_to_778 s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510 r1 r2 r3 c0 c1 c3 c4
    u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448 u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
    hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
  obtain ⟨s1, hsteps1, hout1⟩ :=
    hwp1.elim (Satisfies.mono (by dsimp only [sp] at hmem ⊢; bi_frame) hmem) hcode
  obtain ⟨hpc1, hrun1, P1, hmem1, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hv0_1, htrace1, hvregs1, hent1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al1 : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp1, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmeta1 : tryDecryptMidMetaPlaced s0 s1 :=
    ⟨hrun1, hsp1, hsp0_al, hsp_al1, hx29_1, htrace1, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1⟩
  have hmem1_0 := hent1 s1.mem _ hmem1
  have h10_fold : ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) = ((sp + 0x10#64) ↦₃₂ c2) := by
    rw [pointsToBytes_4_eq_pointsTo32 _ _ (by simp [hrck_len]), hc2]
  have h3d0_fold : ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) =
      (((sp + 0x3d0#64) ↦₆₄ c0) ∗ ((sp + 0x3d8#64) ↦₆₄ c1) ∗
       ((sp + 0x3e0#64) ↦₃₂ c2) ∗ ((sp + 0x3e4#64) ↦₆₄ c3) ∗
       ((sp + 0x3ec#64) ↦₆₄ c4)) := by
    rw [pointsTo_36_as_8_8_4_8_8 (sp + 0x3d0#64) (chainKeyBytes rck) hrck_len,
        hc0, hc1, hc2, hc3, hc4,
        show sp + 0x3d0#64 + 8#64 = sp + 0x3d8#64 by bv_arith,
        show sp + 0x3d0#64 + 16#64 = sp + 0x3e0#64 by bv_arith,
        show sp + 0x3d0#64 + 20#64 = sp + 0x3e4#64 by bv_arith,
        show sp + 0x3d0#64 + 28#64 = sp + 0x3ec#64 by bv_arith]
  have h4a0_fold : ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) =
      (((sp + 0x4a0#64) ↦₃₂ r0) ∗ ((sp + 0x4a4#64) ↦₆₄ r1) ∗
       ((sp + 0x4ac#64) ↦₆₄ r2) ∗ ((sp + 0x4b4#64) ↦₆₄ r3) ∗
       ((sp + 0x4bc#64) ↦₃₂ r4)) := by
    rw [pointsTo_32_as_4_8_8_8_4 (sp + 0x4a0#64) (keyToBytes32 rk1) hrk1_len,
        hr0, hr1, hr2, hr3, hr4,
        show sp + 0x4a0#64 + 4#64 = sp + 0x4a4#64 by bv_arith,
        show sp + 0x4a0#64 + 12#64 = sp + 0x4ac#64 by bv_arith,
        show sp + 0x4a0#64 + 20#64 = sp + 0x4b4#64 by bv_arith,
        show sp + 0x4a0#64 + 28#64 = sp + 0x4bc#64 by bv_arith]
  have h4c0_fold : ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) =
      (((sp + 0x4c0#64) ↦₆₄ c3) ∗ ((sp + 0x4c8#64) ↦₆₄ c4)) := by
    rw [pointsTo_16_as_two_64 (sp + 0x4c0#64) ((chainKeyBytes rck).drop 20) (by simp [hrck_len]),
        List.drop_drop, hc3, hc4,
        show sp + 0x4c0#64 + 8#64 = sp + 0x4c8#64 by bv_arith]
  have h4d0_fold : ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) =
      (((sp + 0x4d0#64) ↦₆₄ c0) ∗ ((sp + 0x4d8#64) ↦₆₄ c1)) := by
    have htake : ((chainKeyBytes rck).take 16).take 8 = (chainKeyBytes rck).take 8 := by
      rw [List.take_take, Nat.min_eq_left (by decide)]
    have hdrop : ((chainKeyBytes rck).take 16).drop 8 = ((chainKeyBytes rck).drop 8).take 8 := by
      rw [List.drop_take]
    rw [pointsTo_16_as_two_64 (sp + 0x4d0#64) ((chainKeyBytes rck).take 16) (by simp [hrck_len]),
        htake, hdrop, hc0, hc1,
        show sp + 0x4d0#64 + 8#64 = sp + 0x4d8#64 by bv_arith]
  refine ⟨s1, hsteps1, hpc1, hmeta1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hv0_1, ?_⟩
  rw [h10_fold, h3d0_fold, h4a0_fold, h4c0_fold, h4d0_fold]
  exact Satisfies.mono (by dsimp only [sp] at hmem1_0 ⊢; sep_interval) hmem1_0

theorem dhStep_step_778_to_780_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry ctl : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (cur : BitVec 64) (rest : List (BitVec 8)) (Rest : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry (rngFillAtSpec ctl cur rest))
    (hpc : s.pc = entry + 1912#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x190#64)
    (hx1 : s.readReg64 .x1 = 32#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hv0 : s.readVReg128 0#5 = 0#128)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x190#64) 0x20 ∗
      tapeAfter ctl cur rest 0 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧
      s'.pc = entry + 1920#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((sp + 0x190#64) ↦ₛ (Ratchet.keyToBytesVec32 (coinsOf rest)).toList) ∗
        tapeAfter ctl cur rest (min 32 rest.length) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  rw [split_32_four_64 (sp + 0x190#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_778_to_rng s0 s u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
  obtain ⟨sc, hsteps1, hout1⟩ :=
    hwp1.elim (Satisfies.mono (by dsimp only [sp] at hmem ⊢; bi_frame) hmem) hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hsp_c, hx0_c, hx1_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hpre_rng : sc.mem ⊨ (rngFillAtSpec ctl cur rest).pre (sp + 0x190#64, 32) sc ∗ Rest := by
    dsimp only [rngFillAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, by rw [hx1_c]; rfl⟩, Satisfies.mono (by dsimp only [sp] at hmem_c0 ⊢; sep_interval) hmem_c0⟩
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hrng.no_fault_before_outcome (sp + 0x190#64, 32) Rest sc hpcc hrunc hpre_rng hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [rngFillAtSpec] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htrace_s', hpost'⟩
    rw [← keyVec_coinsOf_toList rest] at hpost'
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hret'.1.trans hx30_c, hmeta', hcs', hpost'⟩
  · dsimp only [rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [rngFillAtSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_step_780_to_7a8_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (v : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1920#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨ ((s0.sp - 1504#64 + 0x190#64) ↦ₛ v.toList) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧
      s'.pc = entry + 1960#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x0 = sp + 0x500#64 ∧
      s'.readReg64 .x8 = sp + 0x400#64 ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s.readReg64 .x20 ∧
      s'.readReg64 .x21 = s.readReg64 .x21 ∧
      s'.readReg64 .x22 = s.readReg64 .x22 ∧
      s'.readReg64 .x23 = s.readReg64 .x23 ∧
      s'.readReg64 .x24 = sp + 0x400#64 ∧
      s'.readReg64 .x25 = s.readReg64 .x25 ∧
      s'.readReg64 .x26 = s.readReg64 .x26 ∧
      s'.readReg64 .x27 = s.readReg64 .x27 ∧
      s'.readReg64 .x28 = s.readReg64 .x28 ∧
      (s'.mem ⊨ ((sp + 0x190#64) ↦ₛ (Ratchet.clampScalar v).toList) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  set b0 := v.get ⟨0, by decide⟩
  set b31 := v.get ⟨31, by decide⟩
  rw [pointsTo_vec32_split_ends (sp + 0x190#64) v,
      show sp + 0x190#64 + 1#64 = sp + 0x191#64 by bv_arith,
      show sp + 0x190#64 + 31#64 = sp + 0x1af#64 by bv_arith] at hmem
  have hwp1 := hwp.wpp_780_to_7a8 s0 s b0 b31 hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
  obtain ⟨s', hsteps, hout⟩ :=
    hwp1.elim (Satisfies.mono (by dsimp only [sp] at hmem ⊢; bi_frame) hmem) hcode
  obtain ⟨hpc', hrun', P', hmem', hsp', hx0', hx8', hx19', hx20', hx21', hx22', hx23',
    hx24', hx25', hx26', hx27', hx28', hx29', htrace', hvregs', hent'⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al' : s'.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
    ⟨hrun', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩
  have hmem'_0 := hent' s'.mem _ hmem'
  refine ⟨s', hsteps, hpc', hmeta', hx0', hx8', hx19', hx20', hx21', hx22', hx23',
    hx24', hx25', hx26', hx27', hx28', ?_⟩
  rw [← pointsTo_vec32_clamp_fold (sp + 0x190#64) v,
      show sp + 0x190#64 + 1#64 = sp + 0x191#64 by bv_arith,
      show sp + 0x190#64 + 31#64 = sp + 0x1af#64 by bv_arith]
  exact Satisfies.mono (by dsimp only [sp] at hmem'_0 ⊢; bi_entail) hmem'_0

theorem dhStep_step_7a8_to_7b4_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesSpec C.pubKey))
    (sec : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1960#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x500#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 1504#64 + 0x400#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨
      ((s0.sp - 1504#64 + 0x190#64) ↦ₛ sec.toList) ∗
      memRegion (s0.sp - 1504#64 + 0x400#64) 32 ∗
      memRegion (s0.sp - 1504#64 + 0x500#64) 32 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧
      s'.pc = entry + 1972#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        memRegion (sp + 0x190#64) 32 ∗
        ((sp + 0x400#64) ↦ₛ (C.pubKey sec).toList) ∗
        ((sp + 0x500#64) ↦ₛ sec.toList) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hsec_len : sec.toList.length = 32 := sec.2
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sec.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sec.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sec.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sec.toList.drop 24) = v := ⟨_, rfl⟩
  have h190_split : ((sp + 0x190#64) ↦ₛ sec.toList) =
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x190#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  have h500_fold : ((sp + 0x500#64) ↦ₛ sec.toList) =
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x500#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  rw [h190_split, split_32_four_64 (sp + 0x500#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_7a8_to_dpk s0 s p0 p1 p2 p3 u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
  obtain ⟨sc, hsteps1, hout1⟩ :=
    hwp1.elim (Satisfies.mono (by dsimp only [sp] at hmem ⊢; bi_frame) hmem) hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hsp_c, hx0_c, hx8_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  let dpkG : DerivePublicKeyBytesCall := { secret := sp + 0x500#64, sec := sec, out := sp + 0x400#64 }
  have hpre_dpk : sc.mem ⊨ (derivePublicKeyBytesSpec C.pubKey).pre dpkG sc ∗ (memRegion (sp + 0x190#64) 32 ∗ Rest) := by
    dsimp only [derivePublicKeyBytesSpec, dpkG]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, hx8_c⟩, ?_⟩
    rw [h500_fold]
    exact Satisfies.mono (by dsimp only [sp] at hmem_c0 ⊢; sep_interval) hmem_c0
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hdpk.no_fault_before_outcome dpkG (memRegion (sp + 0x190#64) 32 ∗ Rest) sc hpcc hrunc hpre_dpk hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [derivePublicKeyBytesSpec, dpkG] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨htrace_s', hpost'⟩
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hret'.1.trans hx30_c, hmeta', hcs',
      Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hpost'⟩
  · dsimp only [derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_step_7b4_to_7d4_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (hsd : subroutine_ok prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") zeroizeSecretSpec)
    (msgA : BitVec 64) (sec : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1972#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 1504#64 + 0x400#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 1504#64 + 0x3d0#64)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x420#64) 32 ∗
      ((s0.sp - 1504#64 + 0x500#64) ↦ₛ sec.toList) ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧
      s'.pc = lsmpl.base 40 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      s'.readReg64 .x0 = sp + 0x4a0#64 ∧
      s'.readReg64 .x1 = msgA + 56#64 ∧
      s'.readReg64 .x2 = sp + 0x420#64 ∧
      s'.readReg64 .x8 = sp + 0x190#64 ∧
      s'.readReg64 .x30 = entry + 2008#64 ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((sp + 0x420#64) ↦ₛ sec.toList) ∗
        memRegion (sp + 0x500#64) 32 ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hsec_len : sec.toList.length = 32 := sec.2
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sec.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sec.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sec.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sec.toList.drop 24) = v := ⟨_, rfl⟩
  have h500_split : ((sp + 0x500#64) ↦ₛ sec.toList) =
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x500#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  have h420_fold : ((sp + 0x420#64) ↦ₛ sec.toList) =
      (((sp + 0x420#64) ↦₆₄ p0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x420#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x420#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  rw [split_32_four_64 (sp + 0x420#64), h500_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_7b4_to_sd s0 s p0 p1 p2 p3 u0 u1 u2 u3 hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
  obtain ⟨sc, hsteps1, hout1⟩ :=
    hwp1.elim (Satisfies.mono (by dsimp only [sp] at hmem ⊢; bi_frame) hmem) hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hsp_c, hx0_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hpre_sd : sc.mem ⊨ zeroizeSecretSpec.pre (sp + 0x500#64) sc ∗ (((sp + 0x420#64) ↦ₛ sec.toList) ∗ Rest) := by
    dsimp only [zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0_c, ?_⟩
    rw [h420_fold]
    exact Satisfies.mono (by dsimp only [sp] at hmem_c0 ⊢; sep_interval) hmem_c0
  obtain ⟨s2, hsteps2, ⟨hret2, hpres2, hpost2⟩ | ⟨_, hpost2⟩ | ⟨_, -, hpost2⟩ | ⟨_, hpost2⟩, -⟩ :=
    hsd.no_fault_before_outcome (sp + 0x500#64) (((sp + 0x420#64) ↦ₛ sec.toList) ∗ Rest) sc
      hpcc hrunc hpre_sd hsp_al_c (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [zeroizeSecretSpec] at hpost2
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨htrace2, hpost2⟩
    have hpc2 : s2.pc = entry + 1988#64 := hret2.1.trans hx30_c
    have hrun2 : s2.status = .Running := hret2.2.2
    have hsp2 : s2.sp = sp := hpres2.1.trans hsp_c
    have hsp_al2 : s2.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres2.1]
      exact hsp_al_c
    have hcs12 : CalleeSavedPreserved s s2 := CalleeSavedPreserved.trans hcs_c hpres2.2
    have hx22_2 : s2.readReg64 .x22 = msgA := hcs12.2.2.2.1.trans hx22
    have hx24_2 : s2.readReg64 .x24 = sp + 0x400#64 := hcs12.2.2.2.2.2.1.trans hx24
    have hx28_2 : s2.readReg64 .x28 = sp + 0x3d0#64 := hcs12.2.2.2.2.2.2.2.2.2.1.trans hx28
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs12.2.2.2.2.2.2.2.2.2.2.1.trans hx29
    have hwp2 := hwp.wpp_7c4_to_cc2 s0 s2 msgA hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2
      (htrace2.trans htrace_c)
    have hmem2_in : s2.mem ⊨ emp ∗ (((sp + 0x420#64) ↦ₛ sec.toList) ∗ memRegion (sp + 0x500#64) 32 ∗ Rest) := by
      have hlen0 : (List.replicate 32 0#8).length = 32 := by simp
      rw [emp_sepConj]
      exact Satisfies.mono (by dsimp only [sp] at hpost2 ⊢; sep_interval) hpost2
    obtain ⟨s', hsteps3, hout3⟩ :=
      hwp2.elim hmem2_in (hsteps12.codeLoaded hcode)
    obtain ⟨hpc', hrun', P', hmem', hsp', hx0', hx1', hx2', hx8', hx30', hcs3, htrace', hent'⟩ :=
      hout3.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
    have hsteps123 := Steps.trans hsteps12 hsteps3
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al ⊢
      rw [hsp', ← show s.sp = s0.sp - 1504#64 from hsp]
      exact hsp_al
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs12 hcs3
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hrun', hsp', hsp0_al, hsp_al', hx29', htrace', hcl.of_keepsFrozen hsteps123.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps123, hpc', hmeta', hx0', hx1', hx2', hx8', hx30', hcs', hent' s'.mem _ hmem'⟩
  · dsimp only [zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1
  · dsimp only [zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1
  · dsimp only [zeroizeSecretSpec] at hpost2
    rw [satisfies_pure_sepConj] at hpost2
    exact False.elim hpost2.1

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

