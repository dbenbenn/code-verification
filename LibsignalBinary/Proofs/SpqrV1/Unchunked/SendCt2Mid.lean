/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Steps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Ct1SentEkReceived>::send_ct2`: Segments 3 and 5a

**Checked by Lean.**

Verifies fixed-base Segment 3 (`encapsulate2`, 128-byte `ct2` allocation/copy, conditional
workspace free) and Segment 5a (`ct1.extend(ct2)`, `slice_concat_3`, `libcrux_hmac::hmac`,
and temporary MAC buffer deallocation).
-/

public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.LibsignalTripleRatchet.Keys
open NextKeyInternalFacts
open AgreeStateSimp
open DoReserveNorm

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

theorem call_mlkemEncaps2 {K : MlKem} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (mlkemEncaps2Spec K))
    (ret esA ekA : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = ret)
    (hx0 : s.readReg64 Reg.x0 = esA) (hx1 : s.readReg64 Reg.x1 = ekA)
    (hsplit : P = ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
      memRegion ret 128 ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨ret, esA, esVec, ekA, ekVec⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [mlkemEncaps2Spec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [mlkemEncaps2Spec]; rw [hsp, htrace]
    refine SepWP.pure_left_focus (sf.trace = s0.trace) (by sep_focus) fun htr_sf => ?_
    have hassoc :
        ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack) ∗ Frame =
        (esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf

theorem call_rustDealloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr : BitVec 64) (size align : Nat)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = ptr)
    (hx1 : (s.readReg64 Reg.x1).toNat = size) (hx2 : (s.readReg64 Reg.x2).toNat = align)
    (hsplit : P = (A.pool ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        ((A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (ptr, size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustDeallocSpec]; rw [hsp, htrace]
    refine SepWP.pure_left_focus (sf.trace = s0.trace) (by sep_focus) fun htr_sf => ?_
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame =
        A.pool ∗ stackAt sp_call allocHookStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf

/-! ## Segment 3 (`0x5e628 → 0x5e690`) -/

@[simp, arm64_norm, wp_norm]
theorem sendCt2_extractLsb'_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[simp, arm64_norm, wp_norm]
theorem sendCt2_extractLsb'_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

theorem memRegion_128_cells (a : BitVec 64) :
    memRegion a 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗
        ((a + 96#64) ↦₆₄ v12) ∗ ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) ∗ ((a + 120#64) ↦₆₄ v15)) := by
  rw [ProofLib.memRegion_cells a 16 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem exists_unpack64_of_length_128 {bs : List (BitVec 8)} (h : bs.length = 128) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
          ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
          ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) := by
  have h1 : (bs.take 64).length = 64 := by rw [List.length_take]; omega
  have h2 : (bs.drop 64).length = 64 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, ha1, _, _⟩ := exists_unpack64_of_length_64_split h1
  obtain ⟨w8, w9, w10, w11, w12, w13, w14, w15, ha2, _, _⟩ := exists_unpack64_of_length_64_split h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, fun a => ?_⟩
  conv_lhs => rw [← List.take_append_drop 64 bs, pointsToBytes_append, h1]
  rw [ha1 a, ha2 (a + BitVec.ofNat 64 64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Residual `es` ownership after borrowing `(esWorkPtr ↦ₛ esVec.toList)`. -/
@[expose] def sendCt2EsAfterWorkAt (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes) : SepProp :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then
    ⌜esWorkPtr ≠ 0#64⌝ ∗ (esPtr ↦ₛ es) ∗ A.live esWorkPtr 2080 1
  else
    ⌜esWorkPtr = esPtr⌝

theorem sendCt2EsWorkAt_entails (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes)
    {esVec : List.Vector (BitVec 8) 2080}
    (hesVec : esVec.toList = if issue1275NeedsFlip ((es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes es else es) :
    sendCt2EsWorkAt A esPtr esWorkPtr es ⊢
      (esWorkPtr ↦ₛ esVec.toList) ∗ sendCt2EsAfterWorkAt A esPtr esWorkPtr es := by
  unfold sendCt2EsWorkAt sendCt2EsAfterWorkAt
  by_cases hflip : issue1275NeedsFlip ((es.drop 1536).take 512) = true
  · simp only [hflip, ↓reduceIte] at hesVec ⊢
    rw [hesVec]
    exact Entails.of_eq (by ac_rfl)
  · simp only [hflip, Bool.false_eq_true, ↓reduceIte] at hesVec ⊢
    rw [hesVec]
    apply Entails.pure_left; intro heq
    subst heq
    rw [sepConj_comm]
    exact Entails.pure_right rfl (Entails.refl _)

theorem page_align_mask {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    b &&& 18446744073709547520#64 = b := by
  have hb : (b &&& 18446744073709547520#64) + (b &&& 4095#64) = b := by bv_kernel
  rw [halign, BitVec.add_zero] at hb
  exact hb

theorem vecU8_expose_nonempty_144 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 144#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 144#64) ↦₆₄ cap) ∗
          ((sp - 136#64) ↦₆₄ ptr) ∗
          ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 144#64) cap ptr bs]
  have h8 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h16 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 144#64) ↦₆₄ cap) ∗ ((sp - 136#64) ↦₆₄ ptr) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 144#64) ↦₆₄ cap) ∗ ((sp - 136#64) ↦₆₄ ptr) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem memRegion_ct1_split_128_len (ptr_ct1' : BitVec 64) {len cap : Nat}
    (hge : len + 128 ≤ cap) (hlt : cap < 2 ^ 63) :
    memRegion (ptr_ct1' + BitVec.ofNat 64 len) (cap - len) =
      memRegion (ptr_ct1' + BitVec.ofNat 64 len) 128 ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 (len + 128)) (cap - (len + 128)) := by
  have h1 : cap - len = 128 + (cap - (len + 128)) := by omega
  have h2 : ptr_ct1' + BitVec.ofNat 64 (len + 128) =
      (ptr_ct1' + BitVec.ofNat 64 len) + BitVec.ofNat 64 128 := by bv_omega
  rw [ProofLib.memRegion_split' (b := ptr_ct1' + BitVec.ofNat 64 len) (n := 128)
        (k := cap - (len + 128)) (b' := ptr_ct1' + BitVec.ofNat 64 (len + 128))
        h1 h2 (by omega)]

theorem pointsToBytes_append_ct1_ct2 (ptr : BitVec 64) (bs1 bs2 : List (BitVec 8)) :
    (ptr ↦ₛ bs1) ∗ ((ptr + BitVec.ofNat 64 bs1.length) ↦ₛ bs2) ⊢ (ptr ↦ₛ (bs1 ++ bs2)) := by
  rw [pointsToBytes_append ptr bs1 bs2]
  exact Entails.refl _

theorem memRegion_sp_272_split_48_80 (sp : BitVec 64) :
    memRegion (sp - 272#64) 128 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 272#64) ↦₆₄ s0) ∗ ((sp - 264#64) ↦₆₄ s1) ∗
        ((sp - 256#64) ↦₆₄ s2) ∗ ((sp - 248#64) ↦₆₄ s3) ∗
        ((sp - 240#64) ↦₆₄ s4) ∗ ((sp - 232#64) ↦₆₄ s5)) ∗
      memRegion (sp - 224#64) 80 := by
  rw [ProofLib.memRegion_split' (b := sp - 272#64) (n := 48) (k := 80)
        (b' := sp - 224#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - 272#64) (8 * 6) ∗ memRegion (sp - 224#64) 80 = _
  rw [ProofLib.memRegion_cells (sp - 272#64) 6 (by decide)]
  have hc6 : cells (sp - 272#64) 6 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 272#64) ↦₆₄ s0) ∗ ((sp - 264#64) ↦₆₄ s1) ∗
        ((sp - 256#64) ↦₆₄ s2) ∗ ((sp - 248#64) ↦₆₄ s3) ∗
        ((sp - 240#64) ↦₆₄ s4) ∗ ((sp - 232#64) ↦₆₄ s5)) := by
    cells_unfold
  rw [hc6]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
        (a ↦₆₄ s0) ∗ ((a + 8#64) ↦₆₄ s1) ∗ ((a + 16#64) ↦₆₄ s2) := by
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  change memRegion a (8 * 3) = _
  rw [ProofLib.memRegion_cells a 3 (by decide)]
  dsimp only [cells]
  simp only [BitVec.add_zero, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]

theorem fold_sp_272_24_24 (sp v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
      ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) ⊢
      memRegion (sp - 272#64) 24 ∗ memRegion (sp - 248#64) 24 := by
  have h1 : (sp - 272#64) + 8#64 = sp - 264#64 := by bv_omega
  have h2 : (sp - 272#64) + 16#64 = sp - 256#64 := by bv_omega
  have h3 : (sp - 248#64) + 8#64 = sp - 240#64 := by bv_omega
  have h4 : (sp - 248#64) + 16#64 = sp - 232#64 := by bv_omega
  have ha : ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ⊢
      memRegion (sp - 272#64) 24 := by
    rw [memRegion_24_cells (sp - 272#64), h1, h2]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))
  have hb : ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) ⊢
      memRegion (sp - 248#64) 24 := by
    rw [memRegion_24_cells (sp - 248#64), h3, h4]
    exact Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5 (Entails.refl _)))
  have hgroup :
      ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
        ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) =
      (((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2)) ∗
        (((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono ha hb

theorem fold_sp_144_24 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ⊢
      memRegion (sp - 144#64) 24 := by
  have ha1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have ha2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [memRegion_24_cells (sp - 144#64), ha1, ha2]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))

theorem bytes_rem_entails_memRegion_cap (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
    conv_lhs => rw [show cap.toNat = bs.length + (cap.toNat - bs.length) by omega]
    exact ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
  rw [hsplit]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

end CryptoVerification.SpqrV1.Unchunked
