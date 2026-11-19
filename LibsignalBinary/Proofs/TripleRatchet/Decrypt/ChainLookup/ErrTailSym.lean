/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoExt
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Symbolic Execution Step Lemmas for `ErrTail`

Instruction-step and loop lemmas for the `ErrTail` block (`+0x30c .. +0x394`), covering SPE result
copying, the `receiver_chains` element-drop loop, and `receiver_chains` / `pqr_state` buffer
deallocation.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem arrayAt_nil {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (p : BitVec 64) :
    arrayAt elem stride p [] = emp := rfl

theorem arrayAt_cons {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (p : BitVec 64)
    (x : α) (xs : List α) :
    arrayAt elem stride p (x :: xs) =
    (elem x p ∗ arrayAt elem stride (p + BitVec.ofNat 64 stride) xs) := rfl

theorem bv_ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

theorem bv_ofNat_succ_succ_bne_one {n : Nat} (hlt : (n + 1 + 1) * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 (n + 1 + 1) != 1#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n + 1 + 1 = 1 at ht
  omega

theorem bv_ofNat_succ_beq_zero {n : Nat} (hlt : (n + 1) * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n + 1 = 0 at ht
  omega

theorem sp_sub_1504_add_0x38 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0x38#64 = sp0 - 1448#64 := by bv_omega

theorem sp_sub_1504_add_0xe8 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0xe8#64 = sp0 - 1272#64 := by bv_omega

theorem sp_sub_1504_add_0xf0 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0xf0#64 = sp0 - 1264#64 := by bv_omega

theorem errTail_copy_spe_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = errTailPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 820#64) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
       ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗ ((sp + 0x150#64) ↦₆₄ t2) ∗
       words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ chainsLen) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = chainsLen) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errTailPC_placed, tryDecryptEntry_placed] at hpc
  unfold words5At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_one_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = errDropChainLoopPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_131).base + 836#64) s
      (chainAt A gc p ∗ A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧ sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = rem) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdrop := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_chain_placed_ok hdealloc))
  rw [show Getters.blkPl_142.base = lsmpl.base 142 from rfl] at hdrop
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed] at hpc
  refine SepWP.rw_pre (by rw [← hsp]) ?_
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 142); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_call hdrop ⟨p, gc⟩
  wp_finish
  refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hsp]

theorem errTail_drop_exit_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem errTail_drop_cont_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {p chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = (blkPl_131).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) errDropChainLoopPC_placed s emp
      (fun sf P =>
        P = emp ∧ tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧ sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed]
  wp_steps
  try rw [hne, if_pos rfl]
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_loop_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = errDropChainLoopPC_placed →
      tryDecryptWPInv s0 s →
      LibsignalCodeLoaded lsmpl s.mem →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s
        (arrayAt (chainAt A) 104 p (gc :: rest) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  induction rest with
  | nil =>
    intro gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_nil, Nat.zero_add] at hx21
    have hone := errTail_drop_one_wp_placed (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed (F := emp) hone ?_ ?_
    · rw [arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_emp]
    intro s1 P1 ⟨hP1, hmeta1, _, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hexit := errTail_drop_exit_wp_placed (H := H) hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed (F := memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hexit ?_ ?_
    · rw [emp_sepConj, sepConj_emp]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [emp_sepConj, List.length_nil, Nat.zero_add, Nat.one_mul]
  | cons gc' rest' ih =>
    intro gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_cons] at hlt hx21
    have hone := errTail_drop_one_wp_placed (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed_lscl (F := arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hcl hone ?_ ?_
    · rw [arrayAt_cons]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    have hstep := errTail_drop_cont_wp_placed (H := H)
      (bv_ofNat_succ_succ_bne_one hlt) hpc1 hmeta1 hx19_1 hx20_1 hx21_1
    refine SepWP.bind_framed_lscl
      (F := (memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∗
            arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hcl1 hstep ?_ ?_
    · rw [emp_sepConj]
    intro s2 P2 ⟨hP2, hmeta2, hx19_2, hx20_2, hx21_2⟩ hpc2 hcl2
    subst hP2
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 (rest'.length + 1) := by
      rw [hx21_2, bv_ofNat_succ_sub_one (rest'.length + 1)]
    have hlt' : (rest'.length + 1) * 104 < 2 ^ 63 :=
      Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by decide)) hlt
    have hih := ih gc' (p + 104#64) s2 hlt' hpc2 hmeta2 hcl2 hx19_2 hx20_2 hx21_2'
    refine SepWP.bind_framed (F := memRegion p 104) hih ?_ ?_
    · sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    have hcomb : memRegion p ((rest'.length + 1 + 1) * 104) =
        memRegion p 104 ∗ memRegion (p + 104#64) ((rest'.length + 1) * 104) := by
      rw [show (rest'.length + 1 + 1) * 104 = 104 + (rest'.length + 1) * 104 by omega]
      exact memRegion_split p 104 ((rest'.length + 1) * 104) (by omega)
    rw [List.length_cons, hcomb]; sep_ac_rfl

theorem errTail_drop_nil_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem errTail_drop_init_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) errDropChainLoopPC_placed s emp
      (fun s1 P1 =>
        P1 = emp ∧ tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧ s1.readReg64 .x20 = chainsPtr ∧ s1.readReg64 .x21 = rem) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_placed, tryDecryptEntry_placed]
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_chains_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_131).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 848#64) s
      (arrayAt (chainAt A) 104 chainsPtr cs ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  cases cs with
  | nil =>
    rw [List.length_nil] at hx21
    have hstep := errTail_drop_nil_wp_placed (H := H) hpc hmeta hx20 hx21
    refine SepWP.bind_framed (F := A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [arrayAt_nil]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [List.length_nil, Nat.zero_mul, memRegion_zero]
  | cons gc rest =>
    rw [List.length_cons] at hlt hx21 ⊢
    have hstep := errTail_drop_init_wp_placed (H := H) (bv_ofNat_succ_beq_zero hlt) hpc hmeta hx20 hx21
    refine SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A) 104 chainsPtr (gc :: rest) ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) dropChainStack) hcl hstep ?_ ?_
    · rw [emp_sepConj]
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    refine SepWP.rw_pre (emp_sepConj _) ?_
    exact errTail_drop_loop_wp_placed (A := A) (H := H)
      (chainsPtr := chainsPtr) (s0 := s0)
      hdealloc rest gc chainsPtr s1 hlt hpc1 hmeta1 hcl1 hx19_1 hx20_1 hx21_1

theorem errTail_dealloc_chains_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_131).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 876#64) s
      (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0x38#64) ↦₆₄ chainsCap) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_131).rebase (blkPl_131).base H) hdealloc
  by_cases hcap : chainsCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (chainsCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hmul : (chainsCap * 104#64).toNat = chainsCap.toNat * 104 := by
      rw [BitVec.toNat_mul, show (104#64 : BitVec 64).toNat = 104 from rfl,
          Nat.mod_eq_of_lt (by omega)]
    wp_steps; wp_apply; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0x38]; sep_ac_rfl

theorem errTail_dealloc_pq_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hpc : s.pc = (blkPl_131).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 0xe8#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 0xf0#64) ↦₆₄ pqPtr) ∗
             A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := ls_hook_ok_rustDealloc (prog := (blkPC_131).rebase (blkPl_131).base H) hdealloc
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed]
  by_cases hcap : pqCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (pqCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    wp_steps; wp_apply; wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp, sp_sub_1504_add_0xe8, sp_sub_1504_add_0xf0]; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
