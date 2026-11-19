/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
import LibsignalBinary.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03

/-!
# `B19`: `libcrux_ml_kem::mlkem768::incremental::encapsulate1` (`Mlkem768.Encaps1`)

Proves tight-stack (`18,304` B) partial (`MlKemBlockSafeOk 19`) and total (`MlKemBlockOk 19`)
contracts and caller projections for `B19` calling `B03` (`18,160` B).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement add_zero_reloc_cancel
  mbase mlkemCall_of_blockOk mlkemCaller_ok mlkemMpl mlkemSafeCall_of_blockSafeOk
  mlkemSafeCaller_ok resolve_blk03 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved mlkemKeep mlkemRoOk_stripExecOutside
  stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  Mlkem768Encaps1Terminates_matrix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768Encaps1Terminates Shake128MatrixTerminates mlkem768Incremental toByteVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env toByteVec_toList_of_length withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepWP.of_memRegion_vecRangeMem vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args MlkemEncaps1Args SavedFrame19 UnspilledSaved19 blk19_code_eq
  blk19_tree_size blkLib19 blkPC19 blkPl19 blkPlaceable19 blkTree19
  encaps1OutCt1 encaps1OutCt1_take64 encaps1OutEs encaps1OutEs_take64
  encaps1OutSs encaps1OutSs_take64
  mlkem768Incremental_encaps1_ge64 mlkem768Incremental_encaps1_lt64
  mlkemBlk03CoreSpec mlkemBlk03RawSpec mlkemBlk03TermCoreSpec mlkemBlk03TermRawSpec
  mlkemEncaps1CoreSpec mlkemEncaps1ProjSpec mlkemEncaps1RawSpec
  mlkemEncaps1TermCoreSpec mlkemEncaps1TermRawSpec safeSepWP_seq_env
  safe_subroutine_ok_of_simulates savedFrame19_entails_memRegion16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  sepWP_elim_byte step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03 (
  blk03_encaps1_ok blk03_encaps1_raw_ok blk03_encaps1_raw_safe_ok blk03_encaps1_safe_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC19 blkLib19 blkTree19 blk19_code_eq blk19_tree_size
  via_placement blkPl19 blkPlaceable19 [0x0000 → 0x006c]
end

namespace Simp
@[scoped simp] theorem blkPl19_ρ [MlKemPlacement] (sym : String) :
    blkPl19.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl
end Simp
open scoped Simp
attribute [arm64_norm, wp_norm] Simp.blkPl19_ρ

private theorem stackAt18304_split (sp0 : BitVec 64) :
    stackAt sp0 18304 =
      stackAt (sp0 - 144#64) 18160 ∗
      memRegion (sp0 - 144#64) 128 ∗
      memRegion ((sp0 - 144#64) + 128#64) 16 := by
  unfold stackAt
  have h1 : (sp0 - 144#64) - BitVec.ofNat 64 18160 = sp0 - BitVec.ofNat 64 18304 := by bv_omega
  rw [h1,
    memRegion_split' (b := sp0 - BitVec.ofNat 64 18304) (b' := sp0 - 144#64)
      (n := 18160) (k := (144 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 144#64) (b' := (sp0 - 144#64) + 128#64)
      (n := 128) (k := (16 : Nat)) rfl (by bv_omega) (by decide)]

private theorem blk19_short_ok [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl19 b) (_hbase : blkPl19.base = b)
    (s0 : State) (a : MlkemEncaps1Args) (Rest : SepProp)
    (hlt : a.hdr.length < 64)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = a.ret) (hx1 : (s0.readReg64 .x1).toNat = a.hdr.length) :
    SepWP (blkPC19.rebase b (fun _ => none)) (s0.readReg64 .lr) s0
      (memRegion a.ret 961 ∗ Rest)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ (a.ret ↦₈ 1#8) ∗ ((a.ret + 1#64) ↦₈ 0#8) ∗ memRegion (a.ret + 2#64) 959 ∗ Rest)) := by
  rw [memRegion_split' (b := a.ret) (b' := a.ret + 1#64) (n := 1) (k := (960 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a.ret + 1#64) (b' := a.ret + 2#64) (n := 1) (k := (959 : Nat)) rfl (by bv_omega) (by decide),
      sepConj_assoc, sepConj_assoc]
  apply sepWP_elim_byte; intro b0
  rw [← sepConj_assoc, sepConj_comm (a.ret ↦₈ b0), sepConj_assoc]
  apply sepWP_elim_byte; intro b1
  refine SepWP.weaken_pre (P' := (a.ret ↦ₛ [b0, b1]) ∗ memRegion (a.ret + 2#64) 959 ∗ Rest)
    (by simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]; sep_frame) ?_
  subst _hbase
  simp only [Reg.x1] at hx1
  wp_step
  refine step_bCond_not_taken (pc := blkPl19.base + 4#64) (off := 16#64)
    (dst := blkPl19.base + 8#64) (c := .HI)
    (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm])
    (by simp only [wp_norm, arm64_norm, conditionHolds_hi_subsPState64, BitVec.ult]
        rw [hx1]; exact decide_eq_false (by omega))
    (by bv_omega) ?_
  wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨rfl, by simp [CalleeSavedPreserved], ?_⟩
  have hw : ByteSlice.write16 [b0, b1] 0 1#16 = [1#8, 0#8] := by rfl
  rw [hw]; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]; sep_frame

private theorem blk19_epilogue_ok [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl19 b) (hbase : blkPl19.base = b)
    (s0 s : State) (Rest : SepProp)
    (hpc : s.pc = b + 0x0064#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64) (hsp0 : s0.spAligned = true)
    (hus : UnspilledSaved19 s0 s) :
    SepWP (blkPC19.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
        memRegion (s0.sp - 144#64) 128 ∗
        stackAt (s0.sp - 144#64) 18160 ∗ Rest)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ stackAt s0.sp 18304 ∗ Rest)) := by
  subst hbase
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]
    exact spAligned_sub s0.sp 144#64 hsp0 (by decide)
  dsimp only [SavedFrame19]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ⟨by wp_norm_lhs, ?_, ?_⟩
  · rcases hus with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
      hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
    refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
    exact Prod.ext (by wp_norm_lhs) (Prod.ext (by wp_norm_lhs)
      (Prod.ext (by wp_norm_lhs) (Prod.ext (by wp_norm_lhs)
        (Prod.ext (by wp_norm_lhs) (Prod.ext (by wp_norm_lhs)
          (Prod.ext (by wp_norm_lhs) (by wp_norm_lhs)))))))
  · rw [stackAt18304_split s0.sp]
    refine Entails.trans (sepConj_mono_left
      (savedFrame19_entails_memRegion16 ((s0.sp - 144#64) + 128#64) s0)) ?_
    sep_frame

private def blk19Mid (h64 stk : List (BitVec 8)) : List (BitVec 8) :=
  ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 stk
        79 (ByteSlice.readLE h64 16 8)) 87 (ByteSlice.readLE h64 24 8))
      95 (ByteSlice.readLE h64 32 8)) 103 (ByteSlice.readLE h64 40 8))
    111 (ByteSlice.readLE h64 48 8)) 119 (ByteSlice.readLE h64 56 8))
  48 (ByteSlice.readLE h64 48 8)) 56 (ByteSlice.readLE h64 56 8))
  64 (ByteSlice.readLE h64 1 8)) 72 (ByteSlice.readLE h64 9 8)

private def blk19Fin (h64 mid : List (BitVec 8)) : List (BitVec 8) :=
  ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 (h64.getD 0 0#8))
      33 (ByteSlice.readLE mid 96 8)) 41 (ByteSlice.readLE mid 104 8))
    17 (ByteSlice.readLE mid 80 8)) 25 (ByteSlice.readLE mid 88 8))
  1 (ByteSlice.readLE mid 64 8)) 9 (ByteSlice.readLE mid 72 8)

private theorem write64_readLE8_step {bs h64 : List (BitVec 8)} (off src i : Nat)
    (hlen : bs.length = 128) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write64 bs off (ByteSlice.readLE h64 src 8)).getD i 0#8 =
      if off ≤ i ∧ i < off + 8 then h64.getD (src + (i - off)) 0#8 else bs.getD i 0#8 := by
  rw [ByteSlice.getD_write64 bs off _ i 0#8 (by omega)]
  split
  · rw [ByteSlice.extractLsb'_readLE h64 src 8 (i - off)]; simp [show i - off < 8 by omega]
  · rfl

private theorem write64_len128 {bs : List (BitVec 8)} {off : Nat} {v : BitVec 64}
    (h : bs.length = 128) (ho : off + 8 ≤ 128 := by decide) :
    (ByteSlice.write64 bs off v).length = 128 := by
  rw [ByteSlice.write64_length bs off v (by omega), h]

private theorem write8_len128 {bs : List (BitVec 8)} {off : Nat} {v : BitVec 8}
    (h : bs.length = 128) (ho : off + 1 ≤ 128 := by decide) :
    (ByteSlice.write8 bs off v).length = 128 := by
  rw [ByteSlice.write8_length bs off v (by omega), h]

private theorem getD_write8_128 {bs : List (BitVec 8)} (off : Nat) (v : BitVec 8) (i : Nat)
    (h : bs.length = 128) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write8 bs off v).getD i 0#8 = if i = off then v else bs.getD i 0#8 :=
  ByteSlice.getD_write8 bs off v i 0#8 (by omega)

private theorem getD_write64_disj_128 {bs : List (BitVec 8)} (off : Nat) (v : BitVec 64) (i : Nat)
    (h : bs.length = 128) (hd : off + 8 ≤ i) (ho : off ≤ 128 := by decide) :
    (ByteSlice.write64 bs off v).getD i 0#8 = bs.getD i 0#8 := by
  rw [ByteSlice.getD_write64 bs off v i 0#8 (by omega)]
  simp [show ¬(off ≤ i ∧ i < off + 8) by omega]

private theorem readLE_congr {bs bs' : List (BitVec 8)} (off src n : Nat)
    (h : ∀ j, j < n → bs.getD (off + j) 0#8 = bs'.getD (src + j) 0#8) :
    ByteSlice.readLE bs off n = ByteSlice.readLE bs' src n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih (fun j hj => h j (by omega)),
      h n (by omega)]

section Blk19CopyHelpers
attribute [local irreducible] ByteSlice.write64 ByteSlice.write8 ByteSlice.readLE List.getD

private theorem readLE_m1_eq {mid : List (BitVec 8)} (b0 : BitVec 8) (w33 w41 : BitVec 64)
    (off : Nat) (hmid : mid.length = 128) (hoff : 64 ≤ off) :
    ByteSlice.readLE
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 b0) 33 w33) 41 w41) off 8 =
      ByteSlice.readLE mid off 8 := by
  apply readLE_congr; intro j _
  have h1 : (ByteSlice.write8 mid 0 b0).length = 128 := write8_len128 hmid
  have h2 : (ByteSlice.write64 (ByteSlice.write8 mid 0 b0) 33 w33).length = 128 := write64_len128 h1
  rw [getD_write64_disj_128 41 w41 _ h2 (by omega),
      getD_write64_disj_128 33 w33 _ h1 (by omega),
      getD_write8_128 0 b0 _ hmid]
  split <;> first | rfl | omega

private theorem blk19Mid_getD {h64 stk : List (BitVec 8)} (hs : stk.length = 128)
    (i : Nat) (_hi : i < 128) :
    (blk19Mid h64 stk).getD i 0#8 =
      if 64 ≤ i ∧ i < 80 then h64.getD (i - 63) 0#8
      else if 48 ≤ i ∧ i < 64 then h64.getD i 0#8
      else if 80 ≤ i ∧ i < 127 then h64.getD (i - 63) 0#8
      else stk.getD i 0#8 := by
  unfold blk19Mid
  repeat' (rw [write64_readLE8_step _ _ i (by repeat' first | exact hs | refine write64_len128 ?_)])
  repeat' (split <;> try omega)
  all_goals first | rfl | (congr 1; omega)

private theorem blk19Fin_entails (sp1 : BitVec 64) {h64 stk : List (BitVec 8)}
    (hh : h64.length = 64) (hs : stk.length = 128) :
    (sp1 ↦ₛ blk19Fin h64 (blk19Mid h64 stk)) ⊢
      (sp1 ↦ₛ h64) ∗ memRegion (sp1 + 64#64) 64 := by
  set mid := blk19Mid h64 stk with hmid_def
  have hmid : mid.length = 128 := by
    rw [hmid_def]; unfold blk19Mid; repeat' first | exact hs | refine write64_len128 ?_
  have hrmid (off src : Nat) (hb : 64 ≤ off ∧ off + 8 ≤ 127) (hsrc : src + 63 = off) :
      ByteSlice.readLE mid off 8 = ByteSlice.readLE h64 src 8 := by
    apply readLE_congr; intro j hj
    rw [hmid_def, blk19Mid_getD hs (off + j) (by omega)]
    repeat' (split <;> try omega)
    all_goals (congr 1; omega)
  set fin := blk19Fin h64 mid with hfin_def
  have hfin : fin.length = 128 := by
    rw [hfin_def]; unfold blk19Fin
    repeat' first | exact hmid | refine write64_len128 ?_ | refine write8_len128 ?_
  have htake : fin.take 64 = h64 := by
    apply ByteSlice.ext_getD (by simp [hfin, hh])
    intro i hi; simp only [List.length_take, hfin] at hi
    have hgi : (fin.take 64).getD i 0#8 = fin.getD i 0#8 := by
      unfold List.getD; rw [List.getElem?_take_of_lt (by omega)]
    rw [hgi, hfin_def]; unfold blk19Fin
    rw [hrmid 64 1 ⟨by omega, by omega⟩ (by omega), hrmid 72 9 ⟨by omega, by omega⟩ (by omega),
        hrmid 80 17 ⟨by omega, by omega⟩ (by omega), hrmid 88 25 ⟨by omega, by omega⟩ (by omega),
        hrmid 96 33 ⟨by omega, by omega⟩ (by omega), hrmid 104 41 ⟨by omega, by omega⟩ (by omega)]
    repeat' (rw [write64_readLE8_step _ _ i
      (by repeat' first | exact hmid | refine write64_len128 ?_ | refine write8_len128 ?_)])
    rw [getD_write8_128 0 _ i hmid, hmid_def, blk19Mid_getD hs i (by omega)]
    repeat' (split <;> try omega)
    all_goals first | rfl | (congr 1; omega)
  conv => lhs; rw [← List.take_append_drop 64 fin]
  rw [pointsToBytes_append, htake, hh]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion_of_length (by simp [hfin]))

private theorem blk19Mid_len {h64 stk : List (BitVec 8)} (hs : stk.length = 128) :
    (blk19Mid h64 stk).length = 128 := by
  unfold blk19Mid; repeat' first | exact hs | refine write64_len128 ?_

end Blk19CopyHelpers

private theorem blk19_prologue_ok [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl19 b) (hbase : blkPl19.base = b)
    (s0 : State) (a : MlkemEncaps1Args) (Rest : SepProp)
    (hge : 64 ≤ a.hdr.length)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx8 : s0.readReg64 .x8 = a.ret) (hx0 : s0.readReg64 .x0 = a.hdrA)
    (hx1 : (s0.readReg64 .x1).toNat = a.hdr.length)
    (hx2 : s0.readReg64 .x2 = a.randA) (hx3 : s0.readReg64 .x3 = a.esA)
    (hx4 : s0.readReg64 .x4 = 2080#64) (hx5 : s0.readReg64 .x5 = a.ssA)
    (hx6 : s0.readReg64 .x6 = 32#64) :
    SepWP (blkPC19.rebase b (fun _ => none)) (mbase 3) s0
      ((a.hdrA ↦ₛ a.hdr.take 64) ∗
        memRegion (s0.sp - 144#64) 128 ∗
        memRegion ((s0.sp - 144#64) + 128#64) 16 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = s0.sp - 144#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .lr = b + 0x0064#64 ∧
        s1.readReg64 .x0 = a.ret ∧ s1.readReg64 .x1 = s0.sp - 144#64 ∧
        s1.readReg64 .x2 = a.randA ∧ s1.readReg64 .x3 = a.esA ∧
        s1.readReg64 .x4 = 2080#64 ∧ s1.readReg64 .x5 = a.ssA ∧
        s1.readReg64 .x6 = 32#64 ∧ UnspilledSaved19 s0 s1 ∧
        (P1 ⊢ (a.hdrA ↦ₛ a.hdr.take 64) ∗
          ((s0.sp - 144#64) ↦ₛ a.hdr.take 64) ∗
          memRegion ((s0.sp - 144#64) + 64#64) 64 ∗
          SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗ Rest)) := by
  subst hbase
  have hh64 : (a.hdr.take 64).length = 64 := List.length_take_of_le hge
  generalize a.hdr.take 64 = h64 at hh64 ⊢
  rw [memRegion_split' (b := (s0.sp - 144#64) + 128#64) (b' := (s0.sp - 144#64) + 136#64)
        (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  apply SepWP.memRegion8_cell ((s0.sp - 144#64) + 128#64); intro sf0
  apply SepWP.memRegion8_cell ((s0.sp - 144#64) + 136#64); intro sf1
  apply SepWP.of_memRegion_vecRangeMem 8 (s0.sp - 144#64); intro stkV
  rw [vecRangeMem_eq_pointsToBytes]
  have hstk128 : (vecRangeBytes 8 stkV).length = 128 := vecRangeBytes_length 8 stkV
  generalize vecRangeBytes 8 stkV = stk0 at hstk128 ⊢
  simp only [Reg.x1] at hx1
  wp_step
  refine step_bCond_taken (pc := blkPl19.base + 4#64) (off := 16#64)
    (dst := blkPl19.base + 20#64) (c := .HI)
    (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm])
    (by simp only [wp_norm, arm64_norm, conditionHolds_hi_subsPState64, BitVec.ult]
        rw [hx1]; exact decide_eq_true (by omega))
    (by bv_omega) ?_
  wp_steps 13
  have hmid_fold : ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
    (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 stk0
        79 (ByteSlice.readLE h64 16 8)) 87 (ByteSlice.readLE h64 24 8))
      95 (ByteSlice.readLE h64 32 8)) 103 (ByteSlice.readLE h64 40 8))
    111 (ByteSlice.readLE h64 48 8)) 119 (ByteSlice.readLE h64 56 8))
    48 (ByteSlice.readLE h64 48 8)) 56 (ByteSlice.readLE h64 56 8))
    64 (ByteSlice.readLE h64 1 8)) 72 (ByteSlice.readLE h64 9 8) = blk19Mid h64 stk0 := rfl
  rw [hmid_fold]
  have hmid128 : (blk19Mid h64 stk0).length = 128 := blk19Mid_len hstk128
  generalize hmid_eq : blk19Mid h64 stk0 = mid at hmid128 ⊢
  wp_steps 7
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, ?_⟩
  · rw [State.spAligned] at hsp0 ⊢; simp only [wp_norm, arm64_norm]; exact hsp0
  · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs⟩
  · rw [readLE_m1_eq _ _ _ 64 hmid128 (by decide),
        readLE_m1_eq _ _ _ 72 hmid128 (by decide)]
    have hfin_fold : ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write8 mid 0 (h64.getD 0 0#8))
        33 (ByteSlice.readLE mid 96 8)) 41 (ByteSlice.readLE mid 104 8))
      17 (ByteSlice.readLE mid 80 8)) 25 (ByteSlice.readLE mid 88 8))
      1 (ByteSlice.readLE mid 64 8)) 9 (ByteSlice.readLE mid 72 8) = blk19Fin h64 mid := rfl
    rw [hfin_fold, ← hmid_eq]
    dsimp only [SavedFrame19, Reg.x29, Reg.lr]
    have ha16 : (s0.sp - 144#64) + 128#64 = s0.sp - 16#64 := by bv_omega
    have ha8 : ((s0.sp - 144#64) + 128#64) + 8#64 = s0.sp - 8#64 := by bv_omega
    rw [ha8, ha16]
    refine Entails.trans (sepConj_mono_left (blk19Fin_entails (s0.sp - 144#64) hh64 hstk128)) ?_
    sep_frame

private theorem unspilledSaved19_of_cs {s0 s1 s2 : State}
    (hu : UnspilledSaved19 s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    UnspilledSaved19 s0 s2 := by
  rcases hu with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
    hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15⟩
  rcases hcs with ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩
  dsimp only [calleeSavedVRegs, VRegFile.calleeSaved, State.readVReg128] at *
  simp only [Prod.mk.injEq] at cv
  exact ⟨c19.trans h19, c20.trans h20, c21.trans h21, c22.trans h22, c23.trans h23,
    c24.trans h24, c25.trans h25, c26.trans h26, c27.trans h27, c28.trans h28,
    cv.1.trans hv8, cv.2.1.trans hv9, cv.2.2.1.trans hv10, cv.2.2.2.1.trans hv11,
    cv.2.2.2.2.1.trans hv12, cv.2.2.2.2.2.1.trans hv13, cv.2.2.2.2.2.2.1.trans hv14,
    cv.2.2.2.2.2.2.2.trans hv15⟩

private theorem blk19_after_b03_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl19 b) (hbase : blkPl19.base = b)
    (s0 s1 s2 : State) (a : MlkemEncaps1Args) (R : SepProp)
    (hge : 64 ≤ a.hdr.length)
    (hsp0 : s0.spAligned = true) (hsp1 : s1.sp = s0.sp - 144#64)
    (hus1 : UnspilledSaved19 s0 s1)
    (hpc2 : s2.pc = b + 0x0064#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s1.sp) (hcs2 : CalleeSavedPreserved s1 s2) :
    let b03 : MlkemBlk03Args :=
      { ret := a.ret, hdrA := s0.sp - 144#64, hdr64 := a.hdr.take 64,
        randA := a.randA, rand := a.rand.toList, esA := a.esA, ssA := a.ssA }
    let Frame19 : SepProp :=
      SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
      memRegion ((s0.sp - 144#64) + 64#64) 64 ∗
      (a.hdrA ↦ₛ a.hdr.take 64) ∗
      ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64)
    SepWP (blkPC19.rebase b (fun _ => none)) (s0.readReg64 .lr) s2
      ((mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl mlkemBlk03RawSpec)).post
        b03 s1 s2 ∗ Frame19)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R → sf.mem ⊨ mlkemEncaps1RawSpec.post a s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  intro b03 Frame19
  dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, mlkemBlk03RawSpec]
  rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hct_len, hes_len, hss_len⟩
  have hh64 : b03.hdr64.length = 64 := List.length_take_of_le hge
  have h128 : ((s0.sp - 144#64) ↦ₛ b03.hdr64) ∗ memRegion ((s0.sp - 144#64) + 64#64) 64 ⊢
      memRegion (s0.sp - 144#64) 128 := by
    have hp := pointsToBytes_memRegion_entails (s0.sp - 144#64) b03.hdr64 128
      (by omega) (by decide)
    rwa [hh64] at hp
  set OutRest : SepProp :=
    (a.hdrA ↦ₛ a.hdr.take 64) ∗ ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) ∗
    (a.randA ↦ₛ a.rand.toList) ∗ (a.ret ↦₈ 0#8) ∗
    ((a.ret + 1#64) ↦ₛ encaps1OutCt1 b03.hdr64 b03.rand) ∗
    (a.esA ↦ₛ encaps1OutEs b03.hdr64 b03.rand) ∗
    (a.ssA ↦ₛ encaps1OutSs b03.hdr64 b03.rand)
  refine SepWP.weaken_pre
    (P' := SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
      memRegion (s0.sp - 144#64) 128 ∗ stackAt (s0.sp - 144#64) 18160 ∗ OutRest)
    (by dsimp only [b03, Frame19, OutRest]; rw [hsp1]
        have h128' : (((s0.sp - 144#64) ↦ₛ a.hdr.take 64) ∗
            memRegion ((s0.sp - 144#64) + 64#64) 64) ⊢ memRegion (s0.sp - 144#64) 128 := h128
        exact Entails.trans (Q := (((s0.sp - 144#64) ↦ₛ a.hdr.take 64) ∗
            memRegion ((s0.sp - 144#64) + 64#64) 64) ∗ SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
            stackAt (s0.sp - 144#64) 18160 ∗ OutRest)
          (by dsimp only [OutRest, b03]; sep_frame)
          (Entails.trans (sepConj_mono_left h128') (by sep_frame))) ?_
  refine SepWP.mono
    (blk19_epilogue_ok hb hbase s0 s2 OutRest hpc2 hrun2 (hsp2.trans hsp1) hsp0
      (unspilledSaved19_of_cs hus1 hcs2))
    fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
  have hhdr_join : (a.hdrA ↦ₛ a.hdr) =
      (a.hdrA ↦ₛ a.hdr.take 64) ∗ ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) := by
    conv => lhs; rw [← List.take_append_drop 64 a.hdr]
    rw [pointsToBytes_append, List.length_take_of_le hge]
  dsimp only [mlkemEncaps1RawSpec, OutRest, b03] at hm1 ⊢
  rw [mlkem768Incremental_encaps1_ge64 a.hdr a.rand hge, hhdr_join]
  dsimp only []
  dsimp only [b03] at hct_len hes_len hss_len
  rw [encaps1OutCt1_take64] at hct_len hm1
  rw [encaps1OutEs_take64] at hes_len hm1
  rw [encaps1OutSs_take64] at hss_len hm1
  rw [toByteVec_toList_of_length hct_len, toByteVec_toList_of_length hes_len,
      toByteVec_toList_of_length hss_len]
  exact Satisfies.mono (by sep_frame) hm1

/-! ## 2. Block 19 Core `SafeOk` & `Ok` Theorems (`18,304` B Stack) -/

theorem blk19_encaps1_raw_safe_ok :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl mlkemEncaps1RawSpec) := by
  intro _
  refine mlkemSafeCaller_ok blkPC19 blkPl19 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    mlkemEncaps1RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hspat⟩ := hpre
  by_cases hlt : a.hdr.length < 64
  · refine ⟨memRegion a.ret 961 ∗ ((a.hdrA ↦ₛ a.hdr) ∗ (a.randA ↦ₛ a.rand.toList) ∗
        memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18304),
      Satisfies.mono (by sep_frame) hspat, ?_⟩
    refine SafeSepWP.ret_of_sepWP
      (spec := mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl mlkemEncaps1RawSpec))
      (SepWP.mono (blk19_short_ok hb hbase s0 a _ hlt hpc hrun hx8 hx1)
        fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩)
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, mlkemEncaps1RawSpec]
    rw [mlkem768Incremental_encaps1_lt64 a.hdr a.rand hlt]; dsimp only []
    exact Satisfies.mono (by sep_frame) hm1
  · have hge : 64 ≤ a.hdr.length := Nat.le_of_not_lt hlt
    have hhdr_sp : (a.hdrA ↦ₛ a.hdr) =
        (a.hdrA ↦ₛ a.hdr.take 64) ∗ ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) := by
      conv => lhs; rw [← List.take_append_drop 64 a.hdr]
      rw [pointsToBytes_append, List.length_take_of_le hge]
    rw [hhdr_sp, stackAt18304_split s0.sp] at hspat
    set Rest0 : SepProp := ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) ∗ (a.randA ↦ₛ a.rand.toList) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      stackAt (s0.sp - 144#64) 18160
    refine ⟨(a.hdrA ↦ₛ a.hdr.take 64) ∗ memRegion (s0.sp - 144#64) 128 ∗
        memRegion ((s0.sp - 144#64) + 128#64) 16 ∗ Rest0,
      Satisfies.mono (by dsimp only [Rest0]; sep_frame) hspat, ?_⟩
    refine safeSepWP_seq_env hcl0 hro0
      (blk19_prologue_ok hb hbase s0 a Rest0 hge hpc hrun hsp0
        hx8 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hus1, hP1⟩
    let b03 : MlkemBlk03Args :=
      { ret := a.ret, hdrA := s0.sp - 144#64, hdr64 := a.hdr.take 64,
        randA := a.randA, rand := a.rand.toList, esA := a.esA, ssA := a.ssA }
    let Frame19 : SepProp := SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
      memRegion ((s0.sp - 144#64) + 64#64) 64 ∗ (a.hdrA ↦ₛ a.hdr.take 64) ∗
      ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64)
    refine SafeSepWP.weaken_pre
      (SafeSepWP.call_subroutine_frame
        (mlkemSafeCall_of_blockSafeOk (blkPC19.rebase b (fun _ => none)) blk03_encaps1_raw_safe_ok)
        (x := b03) (F := Frame19) (ret_pc := b + 0x0064#64) hpc1 hrun1 hspA1 hlr1
        (fun R1 hm1 => ?_)
        (fun s2 hpc2 hrun2 hsp2 hcs2 => SafeSepWP.ret_of_sepWP
          (spec := mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl mlkemEncaps1RawSpec))
          (blk19_after_b03_wp hb hbase s0 s1 s2 a R hge hsp0 hsp1 hus1 hpc2 hrun2 hsp2 hcs2))) hP1
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, mlkemBlk03RawSpec, b03, Frame19, Rest0] at hm1 ⊢
    rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hro1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      List.length_take_of_le hge, a.rand.toList_length⟩, ?_⟩
    rw [hsp1]; exact Satisfies.mono (by sep_frame) hm1

theorem blk19_encaps1_safe_ok : MlKemBlockSafeOk 19 mlkemEncaps1CoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved (j := 19)
    (spec := fun mpl => withMlKemRoOk mpl mlkemEncaps1RawSpec)
    blk19_encaps1_raw_safe_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [withMlKemRoOk, mlkemEncaps1RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1, ?_⟩
      simpa only [stripS_readReg64, stripS_sp] using h.2)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [withMlKemRoOk, mlkemEncaps1RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

theorem blk19_encaps1_raw_ok :
    MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl mlkemEncaps1TermRawSpec) := by
  intro _
  refine mlkemCaller_ok blkPC19 blkPl19 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    mlkemEncaps1TermRawSpec, mlkemEncaps1RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hspat⟩ := hpre
  by_cases hlt : a.hdr.length < 64
  · refine ⟨memRegion a.ret 961 ∗ ((a.hdrA ↦ₛ a.hdr) ∗ (a.randA ↦ₛ a.rand.toList) ∗
        memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18304),
      Satisfies.mono (by sep_frame) hspat, ?_⟩
    refine SepWP.mono (blk19_short_ok hb hbase s0 a _ hlt hpc hrun hx8 hx1)
      fun sf Pf _ _ ⟨hspf, hcsf, hPf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
    rw [mlkem768Incremental_encaps1_lt64 a.hdr a.rand hlt]; dsimp only []
    exact Satisfies.mono (by sep_frame) hm1
  · have hge : 64 ≤ a.hdr.length := Nat.le_of_not_lt hlt
    have hMat : Shake128MatrixTerminates ((a.hdr.take 64).take 32) 3 := by
      rw [List.take_take]; exact hTerm.resolve_left hlt
    have hhdr_sp : (a.hdrA ↦ₛ a.hdr) =
        (a.hdrA ↦ₛ a.hdr.take 64) ∗ ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) := by
      conv => lhs; rw [← List.take_append_drop 64 a.hdr]
      rw [pointsToBytes_append, List.length_take_of_le hge]
    rw [hhdr_sp, stackAt18304_split s0.sp] at hspat
    set Rest0 : SepProp := ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64) ∗ (a.randA ↦ₛ a.rand.toList) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      stackAt (s0.sp - 144#64) 18160
    refine ⟨(a.hdrA ↦ₛ a.hdr.take 64) ∗ memRegion (s0.sp - 144#64) 128 ∗
        memRegion ((s0.sp - 144#64) + 128#64) 16 ∗ Rest0,
      Satisfies.mono (by dsimp only [Rest0]; sep_frame) hspat, ?_⟩
    refine sepWP_seq_env hcl0 hro0
      (blk19_prologue_ok hb hbase s0 a Rest0 hge hpc hrun hsp0
        hx8 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hus1, hP1⟩
    let b03 : MlkemBlk03Args :=
      { ret := a.ret, hdrA := s0.sp - 144#64, hdr64 := a.hdr.take 64,
        randA := a.randA, rand := a.rand.toList, esA := a.esA, ssA := a.ssA }
    let Frame19 : SepProp := SavedFrame19 ((s0.sp - 144#64) + 128#64) s0 ∗
      memRegion ((s0.sp - 144#64) + 64#64) 64 ∗ (a.hdrA ↦ₛ a.hdr.take 64) ∗
      ((a.hdrA + 64#64) ↦ₛ a.hdr.drop 64)
    refine SepWP.weaken_pre hP1
      (SepWP.call_subroutine_frame
        (mlkemCall_of_blockOk (blkPC19.rebase b (fun _ => none)) blk03_encaps1_raw_ok)
        (x := b03) (F := Frame19) (ret_pc := b + 0x0064#64) hpc1 hrun1 hspA1 hlr1
        (fun R1 hm1 => ?_)
        (fun _ _ _ => not_satisfies_false_sepConj)
        (fun _ _ _ _ => not_satisfies_false_sepConj)
        (fun s2 hpc2 hrun2 hsp2 hcs2 =>
          blk19_after_b03_wp hb hbase s0 s1 s2 a R hge hsp0 hsp1 hus1 hpc2 hrun2 hsp2 hcs2))
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, mlkemBlk03TermRawSpec,
      mlkemBlk03RawSpec, b03, Frame19, Rest0] at hm1 ⊢
    rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hro1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hMat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      List.length_take_of_le hge, a.rand.toList_length⟩, ?_⟩
    rw [hsp1]; exact Satisfies.mono (by sep_frame) hm1

theorem blk19_encaps1_ok : MlKemBlockOk 19 mlkemEncaps1TermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved (j := 19)
    (spec := fun mpl => withMlKemRoOk mpl mlkemEncaps1TermRawSpec)
    blk19_encaps1_raw_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [withMlKemRoOk, mlkemEncaps1TermRawSpec, mlkemEncaps1RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1, ?_⟩
      simpa only [stripS_readReg64, stripS_sp] using h.2)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [withMlKemRoOk, mlkemEncaps1TermRawSpec, mlkemEncaps1RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-! ## 3. `SpecSimulates` Bridges & Caller-Struct Projections (`18,304 ≤ stk`) -/

private theorem pointsTo8_sepExists_entails (p : BitVec 64) (v : BitVec 8) :
    (p ↦₈ v) ⊢ ∃∗ (err : BitVec 8), (p ↦₈ err) := by
  rw [← sepConj_emp (∃∗ (err : BitVec 8), (p ↦₈ err))]
  exact Entails.sepExists_intro_frame (P := fun err : BitVec 8 => p ↦₈ err) (R := emp) v
    (by rw [sepConj_emp]; exact Entails.refl _)

theorem mlkemBlockOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl)) (h : MlKemBlockOk j spec₁) :
    MlKemBlockOk j spec₂ :=
  fun [MlKemPlacement] => ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok h

theorem mlkemBlockSafeOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl)) (h : MlKemBlockSafeOk j spec₁) :
    MlKemBlockSafeOk j spec₂ :=
  fun [MlKemPlacement] =>
    safe_subroutine_ok_of_simulates h ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl)

theorem mlkemEncaps1Core_simulates_proj (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) (mpl : MultiPlacement) :
    SpecSimulates (mlkemEncaps1CoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec stk K ret hdrA hdr randA rand esA ssA))) := by
  refine SpecSimulates.of_map fun y R s0 hm => ?_
  dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps1ProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hregs, hm⟩
  rw [stackAt_shrink s0.sp stk 18304 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 18304)
  refine ⟨⟨ret y, hdrA y, hdr y, randA y, rand y, esA y, ssA y⟩, slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemEncaps1CoreSpec, withNonSyscallPreserved, withMlKemRoOk, mlkemEncaps1RawSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hregs, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro sf _ _ hpost
    dsimp only [mlkemEncaps1CoreSpec, withNonSyscallPreserved, withMlKemRoOk, mlkemEncaps1RawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps1ProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hnsp.1, ?_⟩
    rw [stackAt_shrink s0.sp stk 18304 hstk hstk_fit, hK]
    rcases heq : mlkem768Incremental.encaps1 (hdr y) (rand y) with _ | ⟨ct1, es, ss⟩ <;>
      rw [heq] at hpost <;> dsimp only [] at hpost ⊢
    · have he := pointsTo8_sepExists_entails (ret y + 1#64) 0#8
      exact Satisfies.mono (by sep_frame) hpost
    · exact Satisfies.mono (by sep_frame) hpost

theorem mlkemEncaps1TermCore_simulates_proj (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) (mpl : MultiPlacement) :
    SpecSimulates (mlkemEncaps1TermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec stk K ret hdrA hdr randA rand esA ssA))) := by
  refine SpecSimulates.of_map fun y R s0 hm => ?_
  dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps1ProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hregs, hm⟩
  rw [stackAt_shrink s0.sp stk 18304 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 18304)
  refine ⟨⟨ret y, hdrA y, hdr y, randA y, rand y, esA y, ssA y⟩, slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemEncaps1TermCoreSpec, withNonSyscallPreserved, withMlKemRoOk,
      mlkemEncaps1TermRawSpec, mlkemEncaps1RawSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hTerm y, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hregs, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro sf _ _ hpost
    dsimp only [mlkemEncaps1TermCoreSpec, withNonSyscallPreserved, withMlKemRoOk,
      mlkemEncaps1TermRawSpec, mlkemEncaps1RawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps1ProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hnsp.1, ?_⟩
    rw [stackAt_shrink s0.sp stk 18304 hstk hstk_fit, hK]
    rcases heq : mlkem768Incremental.encaps1 (hdr y) (rand y) with _ | ⟨ct1, es, ss⟩ <;>
      rw [heq] at hpost <;> dsimp only [] at hpost ⊢
    · have he := pointsTo8_sepExists_entails (ret y + 1#64) 0#8
      exact Satisfies.mono (by sep_frame) hpost
    · exact Satisfies.mono (by sep_frame) hpost

theorem blk19_encaps1_proj_safe_ok (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec stk K ret hdrA hdr randA rand esA ssA))) :=
  mlkemBlockSafeOk_simulates
    (mlkemEncaps1Core_simulates_proj stk hstk hstk_fit K hK ret hdrA hdr randA rand esA ssA)
    blk19_encaps1_safe_ok

theorem blk19_encaps1_proj_ok (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec stk K ret hdrA hdr randA rand esA ssA))) :=
  mlkemBlockOk_simulates
    (mlkemEncaps1TermCore_simulates_proj stk hstk hstk_fit K hK ret hdrA hdr randA rand esA ssA hTerm)
    blk19_encaps1_ok

theorem blk19_encaps1_65536_proj_safe_ok (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec 65536 K ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_safe_ok 65536 (by decide) (by decide) K hK ret hdrA hdr randA rand esA ssA

theorem blk19_encaps1_65536_proj_ok (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps1ProjSpec 65536 K ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_ok 65536 (by decide) (by decide) K hK ret hdrA hdr randA rand esA ssA hTerm

theorem blk19_encaps1_extHookStack_proj_safe_ok (hstk : 18304 ≤ extHookStack := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec extHookStack K ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_safe_ok extHookStack hstk (by decide) K hK ret hdrA hdr randA rand esA ssA

theorem blk19_encaps1_extHookStack_proj_ok (hstk : 18304 ≤ extHookStack := by decide) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec extHookStack K ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_ok extHookStack hstk (by decide) K hK ret hdrA hdr randA rand esA ssA hTerm

theorem blk19_encaps1_inc_proj_safe_ok (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec stk mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_safe_ok stk hstk hstk_fit mlkem768Incremental (fun _ _ => rfl)
    ret hdrA hdr randA rand esA ssA

theorem blk19_encaps1_inc_proj_ok (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec stk mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_proj_ok stk hstk hstk_fit mlkem768Incremental (fun _ _ => rfl)
    ret hdrA hdr randA rand esA ssA hTerm

theorem blk19_encaps1_65536_inc_proj_safe_ok {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec 65536 mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_inc_proj_safe_ok 65536 (by decide) (by decide) ret hdrA hdr randA rand esA ssA

theorem blk19_encaps1_65536_inc_proj_ok {C : Type}
    (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemEncaps1ProjSpec 65536 mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_inc_proj_ok 65536 (by decide) (by decide) ret hdrA hdr randA rand esA ssA hTerm

theorem blk19_encaps1_extHookStack_inc_proj_safe_ok (hstk : 18304 ≤ extHookStack := by decide)
    {C : Type} (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64) :
    MlKemBlockSafeOk 19 (fun mpl => withMlKemRoOk mpl (keepsFs
      (mlkemEncaps1ProjSpec extHookStack mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_inc_proj_safe_ok extHookStack hstk (by decide) ret hdrA hdr randA rand esA ssA

theorem blk19_encaps1_extHookStack_inc_proj_ok (hstk : 18304 ≤ extHookStack := by decide)
    {C : Type} (ret hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA ssA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768Encaps1Terminates (hdr x)) :
    MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl (keepsFs
      (mlkemEncaps1ProjSpec extHookStack mlkem768Incremental ret hdrA hdr randA rand esA ssA))) :=
  blk19_encaps1_inc_proj_ok extHookStack hstk (by decide) ret hdrA hdr randA rand esA ssA hTerm

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1
