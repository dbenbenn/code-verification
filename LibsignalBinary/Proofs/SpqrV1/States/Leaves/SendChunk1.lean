/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Chunked Braid Send-Chunk Leaf Transitions 1 (`SendChunk1`)

**Checked by Lean.** Verifies `<EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`, `32` insns),
`<Ct2Sampled>::send_ct2_chunk` (`0x5f9d4`, `34` insns), and `<HeaderSent>::send_ek_chunk`
(`0x5d860`, `39` insns).
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk (polyNextChunkStack)
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem bv_sub_sub (x y z : BitVec 64) : (x - y) - z = x - (y + z) := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Shared Subroutine Call Helpers (`call_memcpy_relocate` & `call_polyNextChunk`) -/

theorem fnAddr_fwd_eq {c : Program} {f1 f2 : String} {o1 o2 d : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o1 + d = o2) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 d = (c.rebase b X).fnAddr f2 := by
  have hback : (c.rebase b X).fnAddr f1 = (c.rebase b X).fnAddr f2 - BitVec.ofNat 64 d :=
    Program.fnAddr_back (d := d) (b := b) (X := X) ho2 ho1 hd
  rw [hback]
  bv_omega

/-- Callee-saved register values `x19..x27` tracked across mid-function `BL` calls. -/
@[expose] def Regs19To27Eq (s : State) (v19 v20 : BitVec 64) (s0 : State) : Prop :=
  s.readReg64 (Reg.gpr 19#5) = v19 ∧
  s.readReg64 (Reg.gpr 20#5) = v20 ∧
  s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem Regs19To27Eq.of_cs {s sf : State} {v19 v20 : BitVec 64} {s0 : State}
    (h : Regs19To27Eq s v19 v20 s0) (hcs : CalleeSavedPreserved s sf) :
    Regs19To27Eq sf v19 v20 s0 :=
  ⟨hcs.1.trans h.1,
   hcs.2.1.trans h.2.1,
   hcs.2.2.1.trans h.2.2.1,
   hcs.2.2.2.1.trans h.2.2.2.1,
   hcs.2.2.2.2.1.trans h.2.2.2.2.1,
   hcs.2.2.2.2.2.1.trans h.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.1.trans h.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.2.2.trans h.2.2.2.2.2.2.2.2.2⟩

theorem relocate_pre_entails {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : Relocatable n F) (dst src : BitVec 64) (Rest : SepProp) :
    (memRegion dst n ∗ F src) ∗ Rest ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = n⌝ ∗
        ((memRegion dst n ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest)) := by
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  exact Entails.of_eq (by ac_rfl)

theorem relocate_post_entails {n : Nat} {F : BitVec 64 → SepProp}
    (dst src : BitVec 64) {bs : List (BitVec 8)} (hlen : bs.length = n) (Rest : SepProp) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest) ⊢
      (F dst ∗ memRegion src n) ∗ Rest := by
  have hrearrange :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Rest) =
      (((dst ↦ₛ bs) ∗ relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Rest := by ac_rfl
  rw [hrearrange]
  refine sepConj_mono_left (sepConj_mono (relocatedHeap_recompose F bs dst) ?_)
  have hm := pointsToBytes_entails_memRegion src bs
  rwa [hlen] at hm

/-- Framed `memcpy` call rule that relocates any `Relocatable n F` predicate from `src` to `dst`,
leaving `memRegion src n` at `src`, and forwards `Regs19To27Eq`. -/
theorem call_memcpy_relocate {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call v19 v20 : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hregs : Regs19To27Eq s v19 v20 s0)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → Regs19To27Eq sf v19 v20 s0 → sf.trace = s0.trace →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hregs.of_cs hcs_sf) (htr.trans htrace)

theorem wordsAt_4 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl]

theorem wordsAt_6 (a : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl]

theorem wordsAt_7 (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
      ((a + 48#64) ↦₆₄ w6) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl]

theorem wordsAt_10 (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl]

theorem wordsAt_16 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl,
    show (96#64 + 8#64 : BitVec 64) = 104#64 from rfl,
    show (104#64 + 8#64 : BitVec 64) = 112#64 from rfl,
    show (112#64 + 8#64 : BitVec 64) = 120#64 from rfl]

theorem cells_1_unfold (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ v0 : BitVec 64, a ↦₆₄ v0 := by
  rw [ProofLib.memRegion_cells a 1 (by decide), cells_succ, cells_zero]
  simp only [sepConj_emp]
  exact Entails.refl _

theorem cell_0_rejoin_400 (sp d1 d2 : BitVec 64) (v : BitVec 64)
    (hd : sp - d2 = (sp - d1) + 8#64) :
    ((sp - d1) ↦₆₄ v) ∗ memRegion (sp - d2) 392 ⊢
      memRegion (sp - d1) 400 := by
  have h8 : ((sp - d1) ↦₆₄ v) ⊢ memRegion (sp - d1) 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length v]
    exact pointsToBytes_entails_memRegion _ _
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [ProofLib.memRegion_split' (b := sp - d1) (n := 8) (k := 392)
      (b' := sp - d2) rfl hd (by decide)]
  exact Entails.refl _

theorem cells_4_unfold (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) := by
  rw [ProofLib.memRegion_cells a 4 (by decide), cells_succ]
  simp only [cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl]
  exact Entails.refl _

theorem cells_6_unfold (a : BitVec 64) :
    memRegion a 48 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
  rw [ProofLib.memRegion_cells a 6 (by decide), cells_succ]
  simp only [cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl]
  exact Entails.refl _

theorem cells_7_unfold (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6] := by
  rw [ProofLib.memRegion_cells a 7 (by decide), cells_succ]
  simp only [wordsAt_7, cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl]
  exact Entails.refl _

theorem cells_10_unfold (a : BitVec 64) :
    memRegion a 80 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] := by
  rw [ProofLib.memRegion_cells a 10 (by decide), cells_succ]
  simp only [wordsAt_10, cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl]
  exact Entails.refl _

theorem cells_16_unfold (a : BitVec 64) :
    memRegion a 128 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12, ∃∗ v13, ∃∗ v14, ∃∗ v15,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] := by
  rw [ProofLib.memRegion_cells a 16 (by decide), cells_succ]
  simp only [wordsAt_16, cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl,
    show (96#64 + 8#64 : BitVec 64) = 104#64 from rfl,
    show (104#64 + 8#64 : BitVec 64) = 112#64 from rfl,
    show (112#64 + 8#64 : BitVec 64) = 120#64 from rfl]
  exact Entails.refl _

theorem uc_copy_recompose {F_pred : BitVec 64 → SepProp}
    {k : Nat} (hk : 400 + k ≤ 2 ^ 64)
    (stA sp_uc : BitVec 64) (ws : List (BitVec 64)) (hws : 8 * ws.length = k) :
    memRegion stA 400 ∗
      wordsAt (stA + 400#64) ws ∗
      wordsAt sp_uc ws ∗
      relocatedHeap F_pred (wordsBytes ws) ⊢
    memRegion stA (400 + k) ∗ F_pred sp_uc := by
  have hk_mem : wordsAt (stA + 400#64) ws ⊢ memRegion (stA + 400#64) k :=
    wordsAt_entails_memRegion ws (stA + 400#64) k hws
  have hrecomp : wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws) ⊢ F_pred sp_uc := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose F_pred (wordsBytes ws) sp_uc
  have hrearrange :
      memRegion stA 400 ∗ wordsAt (stA + 400#64) ws ∗
        wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws) =
      (memRegion stA 400 ∗ wordsAt (stA + 400#64) ws) ∗
        (wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws)) := by ac_rfl
  rw [hrearrange]
  refine sepConj_mono ?_ hrecomp
  refine Entails.trans (sepConj_mono_right hk_mem) ?_
  rw [ProofLib.memRegion_split' (b := stA) (n := 400) (k := k) (b' := stA + 400#64) rfl rfl hk]
  exact Entails.refl _

theorem uc_dec_copy_recompose {F_pred : BitVec 64 → SepProp}
    {k : Nat} (hk1 : k + 400 ≤ 2 ^ 64) (hk2 : 400 + (k + 400) ≤ 2 ^ 64)
    (stA sp_uc : BitVec 64) (hoff : stA + BitVec.ofNat 64 (400 + k) = stA + 400#64 + BitVec.ofNat 64 k)
    (ws : List (BitVec 64)) (hws : 8 * ws.length = k) :
    memRegion stA 400 ∗
      wordsAt (stA + 400#64) ws ∗
      memRegion (stA + BitVec.ofNat 64 (400 + k)) 400 ∗
      wordsAt sp_uc ws ∗
      relocatedHeap F_pred (wordsBytes ws) ⊢
    memRegion stA (400 + (k + 400)) ∗ F_pred sp_uc := by
  have hk_mem : wordsAt (stA + 400#64) ws ⊢ memRegion (stA + 400#64) k :=
    wordsAt_entails_memRegion ws (stA + 400#64) k hws
  have hrecomp : wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws) ⊢ F_pred sp_uc := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose F_pred (wordsBytes ws) sp_uc
  have hrearrange :
      memRegion stA 400 ∗ wordsAt (stA + 400#64) ws ∗
        memRegion (stA + BitVec.ofNat 64 (400 + k)) 400 ∗
        wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws) =
      (memRegion stA 400 ∗ (wordsAt (stA + 400#64) ws ∗ memRegion (stA + BitVec.ofNat 64 (400 + k)) 400)) ∗
        (wordsAt sp_uc ws ∗ relocatedHeap F_pred (wordsBytes ws)) := by ac_rfl
  rw [hrearrange]
  refine sepConj_mono ?_ hrecomp
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hk_mem)) ?_
  rw [ProofLib.memRegion_split' (b := stA) (n := 400) (k := k + 400) (b' := stA + 400#64) rfl rfl hk2,
      ProofLib.memRegion_split' (b := stA + 400#64) (n := k) (k := 400)
        (b' := stA + BitVec.ofNat 64 (400 + k)) rfl hoff hk1]
  exact Entails.refl _

/-! ## 3. Proof 2: `<EkReceivedCt1Sampled>::send_ct1_chunk` (`0x5e1d0`, 32 insns) -/

theorem stackAt_960_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 960) =
      stackAt (sp - 960#64) polyNextChunkStack ∗
      memRegion (sp - 960#64) 400 ∗
      memRegion (sp - 560#64) 400 ∗
      memRegion (sp - 160#64) 128 ∗
      memRegion (sp - 32#64) 32 := by
  change memRegion (sp - 19392#64) 19392 =
    memRegion (sp - 960#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 960#64 - 18432#64 = sp - 19392#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19392#64) (n := 18432) (k := 960)
        (b' := sp - 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 960#64) (n := 400) (k := 560)
        (b' := sp - 560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 560#64) (n := 400) (k := 160)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 128) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]

theorem stackAt_960_rejoin (sp w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 960#64) polyNextChunkStack ∗
      memRegion (sp - 960#64) 400 ∗
      memRegion (sp - 560#64) 528 ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
    stackAt sp (polyNextChunkStack + 960) := by
  have h4 :
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      memRegion (sp - 32#64) 32 := by
    have heq :
        (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
         ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) =
        wordsAt (sp - 32#64) [w0, w1, w2, w3] := by
      simp only [wordsAt_4, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3] (sp - 32#64) 32 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h4))) ?_
  rw [stackAt_960_split sp,
      ProofLib.memRegion_split' (b := sp - 560#64) (n := 400) (k := 128)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedEkReceivedCt1SampledAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ct1 := outSt.sending_ct1 }) :
    polyEncoderAt A (sp - 560#64) outSt.sending_ct1 ∗
      unchunkedCt1SentEkReceivedAt A (sp - 160#64) st.uc ⊢
    chunkedEkReceivedCt1SampledAt A (sp - 560#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hoff : (sp - 560#64) + 400#64 = sp - 160#64 := by bv_omega
  unfold chunkedEkReceivedCt1SampledAt
  rw [huc, hoff]
  exact Entails.refl _

theorem stackAt_896_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 896) =
      stackAt (sp - 896#64) polyNextChunkStack ∗
      memRegion (sp - 896#64) 8 ∗
      memRegion (sp - 888#64) 400 ∗
      memRegion (sp - 488#64) 400 ∗
      memRegion (sp - 88#64) 56 ∗
      memRegion (sp - 32#64) 32 := by
  change memRegion (sp - 19328#64) 19328 =
    memRegion (sp - 896#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 896#64 - 18432#64 = sp - 19328#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19328#64) (n := 18432) (k := 896)
        (b' := sp - 896#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 896#64) (n := 8) (k := 888)
        (b' := sp - 888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 888#64) (n := 400) (k := 488)
        (b' := sp - 488#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 488#64) (n := 400) (k := 88)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 56) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]

theorem stackAt_896_rejoin (sp w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 896#64) polyNextChunkStack ∗
      memRegion (sp - 896#64) 8 ∗
      memRegion (sp - 888#64) 400 ∗
      memRegion (sp - 488#64) 456 ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
    stackAt sp (polyNextChunkStack + 896) := by
  have h4 :
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      memRegion (sp - 32#64) 32 := by
    have heq :
        (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
         ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) =
        wordsAt (sp - 32#64) [w0, w1, w2, w3] := by
      simp only [wordsAt_4, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3] (sp - 32#64) 32 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right h4)))) ?_
  rw [stackAt_896_split sp,
      ProofLib.memRegion_split' (b := sp - 488#64) (n := 400) (k := 56)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt2SampledAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ct2 := outSt.sending_ct2 }) :
    polyEncoderAt A (sp - 488#64) outSt.sending_ct2 ∗
      unchunkedCt2SentAt A (sp - 88#64) st.uc ⊢
    chunkedCt2SampledAt A (sp - 488#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hoff : (sp - 488#64) + 400#64 = sp - 88#64 := by bv_omega
  unfold chunkedCt2SampledAt
  rw [huc, hoff]
  exact Entails.refl _

theorem stackAt_1328_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 1328) =
      stackAt (sp - 1328#64) polyNextChunkStack ∗
      memRegion (sp - 1328#64) 8 ∗
      memRegion (sp - 1320#64) 392 ∗
      memRegion (sp - 928#64) 400 ∗
      memRegion (sp - 528#64) 80 ∗
      memRegion (sp - 448#64) 400 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 19760#64) 19760 =
    memRegion (sp - 1328#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 1328#64 - 18432#64 = sp - 19760#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19760#64) (n := 18432) (k := 1328)
        (b' := sp - 1328#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1328#64) (n := 8) (k := 1320)
        (b' := sp - 1320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1320#64) (n := 392) (k := 928)
        (b' := sp - 928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 928#64) (n := 400) (k := 528)
        (b' := sp - 528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 528#64) (n := 80) (k := 448)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

theorem stackAt_1328_rejoin (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    stackAt (sp - 1328#64) polyNextChunkStack ∗
      memRegion (sp - 1328#64) 400 ∗
      memRegion (sp - 928#64) 880 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    stackAt sp (polyNextChunkStack + 1328) := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by
      simp only [wordsAt_6, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6))) ?_
  rw [stackAt_1328_split sp,
      ProofLib.memRegion_split' (b := sp - 1328#64) (n := 8) (k := 392)
        (b' := sp - 1320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 928#64) (n := 400) (k := 480)
        (b' := sp - 528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 528#64) (n := 80) (k := 400)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedHeaderSentAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ek := outSt.sending_ek, receiving_ct1 := st.receiving_ct1 }) :
    polyEncoderAt A (sp - 928#64) outSt.sending_ek ∗
      unchunkedEkSentAt A (sp - 528#64) st.uc ∗
      polyDecoderAt A (sp - 448#64) st.receiving_ct1 ⊢
    chunkedHeaderSentAt A (sp - 928#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hdec : st.receiving_ct1 = outSt.receiving_ct1 := by rw [hout]
  have hoff1 : (sp - 928#64) + 400#64 = sp - 528#64 := by bv_omega
  have hoff2 : (sp - 928#64) + 480#64 = sp - 448#64 := by bv_omega
  unfold chunkedHeaderSentAt
  rw [huc, hdec, hoff1, hoff2]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.Leaves
