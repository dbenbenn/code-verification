/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeWords
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTailSteps

/-!
# `Fixslice64` 1-Block Tail CBC Decryption Loop (`CbcDec.SoftTail`)

Verifies `fnAddr + 0xbc0#64 -> fnAddr + 0xd20#64` (`0x4c9d14..0x4c9e70`), completing the
software (`STORAGE != 1`) decryption path at the shared PKCS#7 unpad join point `fnAddr + 0xd20#64`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTail

open Arm64 ProofLib SepProp ProofLib.SepLogic
open CryptoGames.CBC (bytesToBlock blockToBytesLE blockToBytesLE_bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (AesCall)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap (PoolAesInitSplit)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (Blocks4 aes256KeyScheduleFs aes256DecryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing (Blocks4.Wf)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved fsKeys256At blocks4Bytes)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (blocks4Bytes_aes256DecryptFs_quad)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Code
  (Aes256DecHwAddrs Aes256CbcDecryptCallees)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.CodeSegs (CbcDecCodeSegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
  (cbcChainAt cbcChainAt_succ cbcChainAt_length
   cbcPrefixBytes cbcPrefixBytes_length cbcPrefixBytes_step1)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.StoreRules
  (sepWP_weaken_pre pack8LE bytes16At pointsToBytes16_eq_bytes16At
   pointsToBytes16_eq_pts64_pair pts64_pair_eq_bytes16At exists_bytes16
   pts64x8At sepWP_memRegion8_elim sepWP_memRegion64_pts64x8_elim)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.Common
  (step_bl_decrypt stackAt_allocHook_split208 slots56)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftCommon
  (cbcSoftWork lsr6_ofNat_eq bv64_ofNat_sub_one bv64_ofNat_beq_zero
   bv64_add_ofNat_16 drop_eq_take_append_drop pts64x8At_pack8LE_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTailSteps
  (cbc_tail_pre cbc_tail_post1 cbc_tail_post2a cbc_tail_post2b)

private theorem bv64_and_neg64_orr7_aux (v : BitVec 64) :
    ((v &&& 0xffffffffffffffc0#64) ||| 7#64) = ((v >>> 6) <<< 6) + 7#64 := by bv_bits

private theorem bv64_and_neg64_orr7 {n : Nat} (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n &&& 0xffffffffffffffc0#64) ||| 7#64) =
      BitVec.ofNat 64 (16 * (4 * (n / 64))) + 7#64 := by
  rw [bv64_and_neg64_orr7_aux, lsr6_ofNat_eq n hn]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n / 64 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 16 * (4 * (n / 64)) < 2 ^ 64)]; omega

private theorem list_slice16_eq {ct : List (BitVec 8)} {m : Nat} (_hm : 16 * (m + 1) ≤ ct.length) :
    ct = ct.take (16 * m) ++ ((ct.drop (16 * m)).take 16 ++ ct.drop (16 * (m + 1))) := by
  rw [show 16 * (m + 1) = 16 * m + 16 from by omega, ← drop_eq_take_append_drop ct (16 * m) 16,
      List.take_append_drop]

private theorem sepWP_bytes16_elim {P : Program} {target_pc a : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 : BitVec 8,
      SepWP P target_pc s (bytes16At a z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗ Rest) post oom) :
    SepWP P target_pc s (memRegion a 16 ∗ Rest) post oom := by
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide), sepConj_assoc]
  refine sepWP_memRegion8_elim fun w0 => ?_
  rw [sepConj_left_comm (a ↦₆₄ w0) (memRegion (a + 8#64) 8)]
  refine sepWP_memRegion8_elim fun w1 => ?_
  obtain ⟨z0,z1,z2,z3,z4,z5,z6,z7, hw0⟩ :
      ∃ z0 z1 z2 z3 z4 z5 z6 z7 : BitVec 8, unpack64 w0 = [z0,z1,z2,z3,z4,z5,z6,z7] := by
    have hl : (unpack64 w0).length = 8 := unpack64_length w0
    rcases hx : unpack64 w0 with _ | ⟨z0, _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, _ | ⟨z5, _ | ⟨z6, _ | ⟨z7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp_all
  obtain ⟨z8,z9,z10,z11,z12,z13,z14,z15, hw1⟩ :
      ∃ z8 z9 z10 z11 z12 z13 z14 z15 : BitVec 8, unpack64 w1 = [z8,z9,z10,z11,z12,z13,z14,z15] := by
    have hl : (unpack64 w1).length = 8 := unpack64_length w1
    rcases hx : unpack64 w1 with _ | ⟨z8, _ | ⟨z9, _ | ⟨z10, _ | ⟨z11, _ | ⟨z12, _ | ⟨z13, _ | ⟨z14, _ | ⟨z15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp_all
  have hp : ((a + 8#64) ↦₆₄ w1) ∗ ((a ↦₆₄ w0) ∗ Rest) =
      bytes16At a z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗ Rest := by
    rw [pointsTo64_eq_pointsToBytes a w0, pointsTo64_eq_pointsToBytes (a + 8#64) w1, hw0, hw1,
        ← pointsToBytes16_eq_bytes16At,
        show [z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15] =
          [z0,z1,z2,z3,z4,z5,z6,z7] ++ [z8,z9,z10,z11,z12,z13,z14,z15] from rfl,
        pointsToBytes_append, show ([z0,z1,z2,z3,z4,z5,z6,z7] : List (BitVec 8)).length = 8 from rfl]
    sep_ac_rfl
  rw [hp]; exact h z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15

/-! ## 1. Single 16-Byte (1-Block) Tail Iteration (`+0xbe4 -> +0xbe4 | +0xd20`) -/

set_option maxHeartbeats 500000 in
theorem cbc_tail_iter {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (m : Nat) (Other : SepProp) (s0 s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hm : m < x.input.length / 16) (hmod16 : x.input.length % 16 = 0)
    (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0xbe4#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = sp + 0x870#64)
    (hx20 : s.readReg64 .x20 = x.inA + BitVec.ofNat 64 (16 * m) + 7#64)
    (hx21 : s.readReg64 .x21 = outBuf + BitVec.ofNat 64 (16 * m) + 7#64)
    (hx22 : s.readReg64 .x22 = sp + 0xb40#64) (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.input.length)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.input.length / 16 - m))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16))
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State,
      sf.pc = (if m + 1 = x.input.length / 16 then fnAddr + 0xd20#64 else fnAddr + 0xbe4#64) →
      sf.status = .Running → sf.sp = sp → sf.readReg64 .x19 = sp + 0x870#64 →
      sf.readReg64 .x20 = x.inA + BitVec.ofNat 64 (16 * (m + 1)) + 7#64 →
      sf.readReg64 .x21 = outBuf + BitVec.ofNat 64 (16 * (m + 1)) + 7#64 →
      sf.readReg64 .x22 = sp + 0xb40#64 → sf.readReg64 .x23 = BitVec.ofNat 64 x.input.length →
      sf.readReg64 .x24 = sp + 0x4b0#64 →
      sf.readReg64 .x25 = BitVec.ofNat 64 (x.input.length / 16 - (m + 1)) →
      sf.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → PureStepPreserved s sf →
      SepWP P target_pc sf
        (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input (m + 1)) ∗
         (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (m + 1) ++
           List.replicate (x.input.length - 16 * (m + 1)) 0#8)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other) post oom) :
    SepWP P target_pc s
      (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input m) ∗
       (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input m ++
         List.replicate (x.input.length - 16 * m) 0#8)) ∗
       (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other) post oom := by
  let ks := aes256KeyScheduleFs x.key
  let src := x.inA + BitVec.ofNat 64 (16 * m)
  let dst := outBuf + BitVec.ofNat 64 (16 * m)
  have h16m : 16 * (m + 1) ≤ x.input.length := by omega
  let c0_bs := (x.input.drop (16 * m)).take 16
  let prev_bs := cbcChainAt x.iv x.input m
  have hc0_len : c0_bs.length = 16 := by dsimp [c0_bs]; rw [List.length_take, List.length_drop]; omega
  have hp_len : prev_bs.length = 16 := cbcChainAt_length hiv16 (by omega)
  have hin_split :
      (x.inA ↦ₛ x.input) =
        ((x.inA ↦ₛ x.input.take (16 * m)) ∗ (src ↦ₛ c0_bs) ∗
         ((x.inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ x.input.drop (16 * (m + 1)))) := by
    conv => lhs; rw [list_slice16_eq h16m]
    change (x.inA ↦ₛ (x.input.take (16 * m) ++ (c0_bs ++ x.input.drop (16 * (m + 1))))) = _
    have htake_len : (x.input.take (16 * m)).length = 16 * m := by rw [List.length_take]; omega
    rw [pointsToBytes_append, htake_len, pointsToBytes_append, hc0_len]
    dsimp only [src]; rw [bv64_add_ofNat_16 x.inA (by omega)]
  have hpre_len : (cbcPrefixBytes x.key x.iv x.input m).length = 16 * m := cbcPrefixBytes_length (by omega)
  have hrep_split : List.replicate (x.input.length - 16 * m) 0#8 =
      List.replicate 16 0#8 ++ List.replicate (x.input.length - 16 * (m + 1)) 0#8 := by
    rw [← List.replicate_add]; exact congrArg (List.replicate · 0#8) (by omega)
  have hout_split :
      (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input m ++ List.replicate (x.input.length - 16 * m) 0#8)) =
        ((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input m) ∗ (dst ↦ₛ List.replicate 16 0#8) ∗
         ((outBuf + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ List.replicate (x.input.length - 16 * (m + 1)) 0#8)) := by
    rw [hrep_split, pointsToBytes_append, hpre_len, pointsToBytes_append, List.length_replicate]
    dsimp only [dst]; rw [bv64_add_ofNat_16 outBuf (by omega)]
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15, hc0_eq⟩ := exists_bytes16 hc0_len
  obtain ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15, hp_eq⟩ := exists_bytes16 hp_len
  have hdst_mem : (dst ↦ₛ List.replicate 16 0#8) ⊢ memRegion dst 16 := by
    simpa only [List.length_replicate] using pointsToBytes_entails_memRegion dst (List.replicate 16 0#8)
  let TailRest :=
    memRegion (sp + 0x03c#64) 168 ∗
    (outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input m) ∗
    ((outBuf + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ List.replicate (x.input.length - 16 * (m + 1)) 0#8) ∗
    (x.inA ↦ₛ x.input.take (16 * m)) ∗
    ((x.inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ x.input.drop (16 * (m + 1))) ∗ Other
  rw [hin_split, hout_split]
  dsimp only [cbcSoftWork]
  refine sepWP_weaken_pre
    (P2 := memRegion (sp + 0x870#64) 64 ∗ memRegion dst 16 ∗
      ((src ↦ₛ c0_bs) ∗ ((sp + 0xf00#64) ↦ₛ prev_bs) ∗ memRegion (sp + 0x4b0#64) 64 ∗
       fsKeys256At (sp + 0xb40#64) ks ∗ stackAt sp allocHookStack ∗ TailRest))
    (by
      dsimp only [TailRest]
      refine Entails.trans (Entails.of_eq (show _ = (dst ↦ₛ List.replicate 16 0#8) ∗ _ by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hdst_mem) (Entails.of_eq (by sep_ac_rfl))) ?_
  refine sepWP_memRegion64_pts64x8_elim fun i0 i1 i2 i3 i4 i5 i6 i7 => ?_
  refine sepWP_weaken_pre (Entails.of_eq (show _ = memRegion dst 16 ∗ _ by sep_ac_rfl))
    (sepWP_bytes16_elim fun z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 => ?_)
  have hc0_p : (src ↦ₛ c0_bs) =
      ((src ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
       ((src + 8#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15)) := by
    rw [hc0_eq, pointsToBytes16_eq_pts64_pair]
  have hp_at : ((sp + 0xf00#64) ↦ₛ prev_bs) =
      bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 := by
    rw [hp_eq, pointsToBytes16_eq_bytes16At]
  let StableRest :=
    bytes16At dst z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗
    bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
    memRegion (sp + 0x4b0#64) 64 ∗ fsKeys256At (sp + 0xb40#64) ks ∗
    stackAt sp allocHookStack ∗ TailRest
  refine sepWP_weaken_pre (Entails.of_eq (by rw [hc0_p, hp_at]; dsimp only [StableRest]; sep_ac_rfl))
    (cbc_tail_pre cs.softTailPre
      (pack8LE c0 c1 c2 c3 c4 c5 c6 c7) (pack8LE c8 c9 c10 c11 c12 c13 c14 c15)
      i0 i1 i2 i3 i4 i5 i6 i7 StableRest s hpc hrun hsp hx19 hx20 hx24
      fun s2 hpc2 hrun2 hsp2 hx0_2 hx1_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          hx25_2 hx26_2 hx29_2 hv2 hpure2 => ?_)
  let z16 := List.replicate 16 (0#8)
  let bs_in : Blocks4 := ⟨c0_bs, z16, z16, z16⟩
  have hwf_in : Blocks4.Wf bs_in := ⟨hc0_len, rfl, rfl, rfl⟩
  have hin64_eq :
      pts64x8At (sp + 0x870#64)
        (pack8LE c0 c1 c2 c3 c4 c5 c6 c7) (pack8LE c8 c9 c10 c11 c12 c13 c14 c15)
        0#64 0#64 0#64 0#64 0#64 0#64 = ((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) := by
    have hz64 : (0#64 : BitVec 64) = pack8LE 0#8 0#8 0#8 0#8 0#8 0#8 0#8 0#8 := rfl
    conv => lhs; rw [hz64]
    rw [pts64x8At_pack8LE_eq_pointsToBytes]; dsimp only [blocks4Bytes, bs_in, z16]; rw [hc0_eq]; rfl
  let CallFrame :=
    (src ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
    ((src + 8#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15) ∗
    bytes16At dst z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 ∗
    bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
    stackFrameAt (sp - 208#64) 3888 ∗ TailRest
  refine step_bl_decrypt (sp := sp) (outPtr := sp + 0x4b0#64) (keysPtr := sp + 0xb40#64)
    (inPtr := sp + 0x870#64) cs.bl_decTail hCal.decrypt_ok
    hpc2 hrun2 hsp2 (by simpa [State.spAligned, hsp2] using hspAl)
    hx0_2 hx1_2 hx8_2 hwf_in (F := CallFrame)
    (by rw [hin64_eq]; dsimp only [StableRest, CallFrame]; rw [stackAt_allocHook_split208 sp]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 hpure3 => ?_
  have hpc3' : s3.pc = fnAddr + 0xc08#64 := by simpa [BitVec.add_assoc] using hpc3
  have hx19_3 : s3.readReg64 .x19 = sp + 0x870#64 := hcs3.readReg64_x19.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = src + 7#64 := hcs3.readReg64_x20.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = dst + 7#64 := hcs3.readReg64_x21.trans (hx21_2.trans hx21)
  have hx22_3 : s3.readReg64 .x22 = sp + 0xb40#64 := hcs3.readReg64_x22.trans (hx22_2.trans hx22)
  have hx23_3 : s3.readReg64 .x23 = BitVec.ofNat 64 x.input.length := hcs3.readReg64_x23.trans (hx23_2.trans hx23)
  have hx24_3 : s3.readReg64 .x24 = sp + 0x4b0#64 := hcs3.readReg64_x24.trans hx24_2
  have hx25_3 : s3.readReg64 .x25 = BitVec.ofNat 64 (x.input.length / 16 - m) := hcs3.readReg64_x25.trans (hx25_2.trans hx25)
  have hx26_3 : s3.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) := hcs3.readReg64_x26.trans (hx26_2.trans hx26)
  have hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29 := hcs3.readReg64_x29.trans hx29_2
  have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hcs3.vregs.trans (hv2.trans hv)
  have hpure_s3 : PureStepPreserved s s3 := hpure2.trans hpure3
  let dec_bs := blocks4Bytes (aes256DecryptFs ks bs_in)
  have hdec_len : dec_bs.length = 64 := by
    have hc0_b := blockToBytesLE_bytesToBlock c0_bs hc0_len
    have hz_b := blockToBytesLE_bytesToBlock z16 rfl
    have hq4 : dec_bs =
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock c0_bs)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock z16)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock z16)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 x.key) (bytesToBlock z16)) := by
      dsimp only [dec_bs, bs_in, ks]
      conv => lhs; rw [← hc0_b, ← hz_b]
      exact blocks4Bytes_aes256DecryptFs_quad hkey32 _ _ _ _
    rw [hq4]; simp [blockToBytesLE]
  have hd16_len : (dec_bs.take 16).length = 16 := by rw [List.length_take, hdec_len]; omega
  have hd48_len : (dec_bs.drop 16).length = 48 := by rw [List.length_drop, hdec_len]
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15, hd_eq⟩ := exists_bytes16 hd16_len
  have hdec_split : ((sp + 0x4b0#64) ↦ₛ dec_bs) =
      (bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
       ((sp + 0x4c0#64) ↦ₛ dec_bs.drop 16)) := by
    rw [pointsToBytes_take_drop (sp + 0x4b0#64) 16 dec_bs (by omega), hd_eq, pointsToBytes16_eq_bytes16At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hd48_mem : ((sp + 0x4c0#64) ↦ₛ dec_bs.drop 16) ⊢ memRegion (sp + 0x4c0#64) 48 := by
    simpa only [hd48_len] using pointsToBytes_entails_memRegion (sp + 0x4c0#64) (dec_bs.drop 16)
  have hin64_len : (blocks4Bytes bs_in).length = 64 := by
    dsimp only [blocks4Bytes, bs_in, z16]; simp only [List.length_append, hc0_len, List.length_replicate]
  have hin64_mem : ((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) ⊢ memRegion (sp + 0x870#64) 64 := by
    simpa only [hin64_len] using pointsToBytes_entails_memRegion (sp + 0x870#64) (blocks4Bytes bs_in)
  let PostRest :=
    (src ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
    ((src + 8#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15) ∗
    memRegion (sp + 0x870#64) 64 ∗ memRegion (sp + 0x4c0#64) 48 ∗
    fsKeys256At (sp + 0xb40#64) ks ∗ stackAt sp allocHookStack ∗ TailRest
  refine sepWP_weaken_pre (by
      change ((fsKeys256At (sp + 0xb40#64) ks ∗ ((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) ∗
               ((sp + 0x4b0#64) ↦ₛ dec_bs) ∗ stackFrameAt sp 208) ∗ CallFrame) ⊢ _
      rw [hdec_split]; dsimp only [CallFrame, PostRest]; rw [stackAt_allocHook_split208 sp]
      refine Entails.trans (Entails.of_eq (show _ =
          (((sp + 0x870#64) ↦ₛ blocks4Bytes bs_in) ∗ ((sp + 0x4c0#64) ↦ₛ dec_bs.drop 16)) ∗ _ by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left (sepConj_mono hin64_mem hd48_mem)) (Entails.of_eq (by sep_ac_rfl)))
    (cbc_tail_post1 cs.softTailPost1
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
      PostRest s3 hpc3' hrun3 hsp3 hspAl hx21_3
      fun s4 hpc4 hrun4 hsp4 hx9_4 hx10_4 hx11_4 hx12_4 hx13_4 hx14_4
          hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 hpz4 hv4 hpure4 => ?_)
  refine cbc_tail_post2a cs.softTailPost2
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    (p0 ^^^ d0) (p1 ^^^ d1) (p2 ^^^ d2) (p3 ^^^ d3) (p4 ^^^ d4) (p5 ^^^ d5)
    (p6 ^^^ d6) (p7 ^^^ d7) (p8 ^^^ d8)
    z3 z5 z7 z8 z9 z10 z11 z12 z13 z14 z15
    PostRest s4 hpc4 hrun4 hsp4 hspAl hx9_4 hx10_4 hx11_4 hx12_4 hx13_4 hx14_4 hx21_4
    fun s5 hpc5 hrun5 hsp5 hx8_5 hx9_5 hx10_5 hx11_5
        hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx29_5 hpz5 hv5 hpure5 => ?_
  let rem1 := BitVec.ofNat 64 (x.input.length / 16 - (m + 1))
  have hrem1_eq : s3.readReg64 .x25 - 1#64 = rem1 := by
    rw [hx25_3, bv64_ofNat_sub_one (by omega) (by omega),
        show x.input.length / 16 - m - 1 = x.input.length / 16 - (m + 1) from by omega]
  have hx20_5' : s5.readReg64 .x20 = src + 7#64 := hx20_5.trans (hx20_4.trans hx20_3)
  have hx22_5' : s5.readReg64 .x22 = sp + 0xb40#64 := hx22_5.trans (hx22_4.trans hx22_3)
  have hx25_5' : s5.readReg64 .x25 = rem1 := hx25_5.trans (hx25_4.trans hrem1_eq)
  have hpz5' : s5.pstate.z = (rem1 == 0#64) := by rw [hpz5, hpz4, hrem1_eq]
  refine sepWP_weaken_pre (Entails.of_eq (by
      try dsimp only [PostRest]
      rw [← pts64_pair_eq_bytes16At (sp + 0xf00#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))
    (cbc_tail_post2b cs.softTailPost2
      (pack8LE c0 c1 c2 c3 c4 c5 c6 c7) (pack8LE c8 c9 c10 c11 c12 c13 c14 c15)
      (pack8LE p0 p1 p2 p3 p4 p5 p6 p7) (pack8LE p8 p9 p10 p11 p12 p13 p14 p15)
      (p0 ^^^ d0) (p1 ^^^ d1) (p2 ^^^ d2) (p3 ^^^ d3) (p4 ^^^ d4) (p5 ^^^ d5)
      (p6 ^^^ d6) (p7 ^^^ d7) (p8 ^^^ d8) (p9 ^^^ d9) (p10 ^^^ d10) (p11 ^^^ d11)
      (p12 ^^^ d12) (p13 ^^^ d13) (p14 ^^^ d14) (p15 ^^^ d15)
      z12 z13 z14 z15 _
      s5 hpc5 hrun5 hsp5 hx8_5 hx9_5 hx10_5 hx11_5 hx20_5' hx21_5 hx22_5' hx25_5' hpz5'
      fun sf hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f
          hx25_f hx26_f hx29_f hv_f hpure_f => ?_)
  have hpc_f' : sf.pc = (if m + 1 = x.input.length / 16 then fnAddr + 0xd20#64 else fnAddr + 0xbe4#64) := by
    rw [hpc_f]
    have hrem_zero : (rem1 == 0#64) = decide (m + 1 = x.input.length / 16) := by
      dsimp only [rem1]; rw [bv64_ofNat_beq_zero (by omega)]; exact decide_eq_decide.mpr (by omega)
    rw [hrem_zero]; by_cases hm1 : m + 1 = x.input.length / 16 <;> simp [hm1]
  have hx19_f' : sf.readReg64 .x19 = sp + 0x870#64 := hx19_f.trans (hx19_5.trans (hx19_4.trans hx19_3))
  have hx20_f' : sf.readReg64 .x20 = x.inA + BitVec.ofNat 64 (16 * (m + 1)) + 7#64 := by
    rw [hx20_f]; dsimp only [src]; rw [← bv64_add_ofNat_16 x.inA (by omega)]
  have hx21_f' : sf.readReg64 .x21 = outBuf + BitVec.ofNat 64 (16 * (m + 1)) + 7#64 := by
    rw [hx21_f]; dsimp only [dst]; rw [← bv64_add_ofNat_16 outBuf (by omega)]
  have hx23_f' : sf.readReg64 .x23 = BitVec.ofNat 64 x.input.length := hx23_f.trans (hx23_5.trans (hx23_4.trans hx23_3))
  have hx24_f' : sf.readReg64 .x24 = sp + 0x4b0#64 := hx24_f.trans (hx24_5.trans (hx24_4.trans hx24_3))
  have hx26_f' : sf.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) := hx26_f.trans (hx26_5.trans (hx26_4.trans hx26_3))
  have hx29_f' : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans (hx29_5.trans (hx29_4.trans hx29_3))
  have hv_f' : calleeSavedVRegs sf = calleeSavedVRegs s0 := hv_f.trans (hv5.trans (hv4.trans hv3))
  have hpure_all : PureStepPreserved s sf := hpure_s3.trans (hpure4.trans (hpure5.trans hpure_f))
  let z_bs := List.zipWith (· ^^^ ·) (dec_bs.take 16) prev_bs
  have hdst_z :
      bytes16At dst (p0 ^^^ d0) (p1 ^^^ d1) (p2 ^^^ d2) (p3 ^^^ d3) (p4 ^^^ d4) (p5 ^^^ d5)
        (p6 ^^^ d6) (p7 ^^^ d7) (p8 ^^^ d8) (p9 ^^^ d9) (p10 ^^^ d10) (p11 ^^^ d11)
        (p12 ^^^ d12) (p13 ^^^ d13) (p14 ^^^ d14) (p15 ^^^ d15) = (dst ↦ₛ z_bs) := by
    rw [← pointsToBytes16_eq_bytes16At]; congr 1
    dsimp only [z_bs]; rw [hd_eq, hp_eq]; simp only [List.zipWith, BitVec.xor_comm]
  have hstep1 : cbcPrefixBytes x.key x.iv x.input m ++ z_bs = cbcPrefixBytes x.key x.iv x.input (m + 1) :=
    cbcPrefixBytes_step1 hkey32 hiv16 hm (b1 := z16) (b2 := z16) (b3 := z16) rfl rfl rfl
  have hout_recombine :
      ((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input m) ∗ (dst ↦ₛ z_bs) ∗
       ((outBuf + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ List.replicate (x.input.length - 16 * (m + 1)) 0#8)) =
        (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (m + 1) ++
          List.replicate (x.input.length - 16 * (m + 1)) 0#8)) := by
    have hz_len : z_bs.length = 16 := by dsimp only [z_bs]; rw [List.length_zipWith, hd16_len, hp_len]; rfl
    have hrhs : cbcPrefixBytes x.key x.iv x.input (m + 1) ++
        List.replicate (x.input.length - 16 * (m + 1)) 0#8 =
        cbcPrefixBytes x.key x.iv x.input m ++ (z_bs ++ List.replicate (x.input.length - 16 * (m + 1)) 0#8) := by
      rw [← hstep1, List.append_assoc]
    rw [hrhs, pointsToBytes_append, hpre_len, pointsToBytes_append, hz_len]
    dsimp only [dst]; rw [bv64_add_ofNat_16 outBuf (by omega)]
  have hin_recombine :
      ((x.inA ↦ₛ x.input.take (16 * m)) ∗
       (src ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
       ((src + 8#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15) ∗
       ((x.inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ x.input.drop (16 * (m + 1)))) = (x.inA ↦ₛ x.input) := by
    rw [hin_split, hc0_p]; sep_ac_rfl
  have hp_next_eq :
      ((sp + 0xf00#64) ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
      ((sp + 0xf08#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15) =
        ((sp + 0xf00#64) ↦ₛ cbcChainAt x.iv x.input (m + 1)) := by
    rw [cbcChainAt_succ]; change _ = ((sp + 0xf00#64) ↦ₛ c0_bs)
    rw [hc0_eq, pointsToBytes16_eq_pts64_pair (sp + 0xf00#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hd16_mem :
      bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ⊢
        memRegion (sp + 0x4b0#64) 16 := by
    rw [← pointsToBytes16_eq_bytes16At]; exact pointsToBytes_entails_memRegion _ _
  have h4b0_64 : memRegion (sp + 0x4b0#64) 64 =
      memRegion (sp + 0x4b0#64) 16 ∗ memRegion (sp + 0x4c0#64) 48 := by
    rw [memRegion_split (sp + 0x4b0#64) 16 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepWP_weaken_pre ?_
    (hnext sf hpc_f' hrun_f hsp_f hx19_f' hx20_f' hx21_f' hx22_f hx23_f' hx24_f'
      hx25_f hx26_f' hx29_f' hv_f' hpure_all)
  rw [hdst_z]
  dsimp only [cbcSoftWork, ks, TailRest]
  rw [h4b0_64]
  refine Entails.trans (Entails.of_eq (show _ =
      bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
      (((outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input m) ∗ (dst ↦ₛ z_bs) ∗
        ((outBuf + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ List.replicate (x.input.length - 16 * (m + 1)) 0#8)) ∗
       ((x.inA ↦ₛ x.input.take (16 * m)) ∗
        (src ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
        ((src + 8#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15) ∗
        ((x.inA + BitVec.ofNat 64 (16 * (m + 1))) ↦ₛ x.input.drop (16 * (m + 1)))) ∗
       (((sp + 0xf00#64) ↦₆₄ pack8LE c0 c1 c2 c3 c4 c5 c6 c7) ∗
        ((sp + 0xf08#64) ↦₆₄ pack8LE c8 c9 c10 c11 c12 c13 c14 c15)) ∗
       memRegion (sp + 0x4c0#64) 48 ∗ memRegion (sp + 0x870#64) 64 ∗
       memRegion (sp + 0x03c#64) 168 ∗ fsKeys256At (sp + 0xb40#64) ks ∗
       stackAt sp allocHookStack ∗ Other) by
      simp only [src, dst, BitVec.add_assoc]; sep_ac_rfl)) ?_
  rw [hout_recombine, hin_recombine, hp_next_eq]
  exact Entails.trans (sepConj_mono_left hd16_mem) (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Inductive Loop & Entry Setup (`fnAddr + 0xbc0#64 -> fnAddr + 0xd20#64`) -/

private theorem cbc_tail_loop_from {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (Other : SepProp) (s0 : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hmod16 : x.input.length % 16 = 0) (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true) :
    ∀ (k m : Nat) (s : State),
      m + (k + 1) = x.input.length / 16 → s.pc = fnAddr + 0xbe4#64 → s.status = .Running →
      s.sp = sp → s.readReg64 .x19 = sp + 0x870#64 →
      s.readReg64 .x20 = x.inA + BitVec.ofNat 64 (16 * m) + 7#64 →
      s.readReg64 .x21 = outBuf + BitVec.ofNat 64 (16 * m) + 7#64 →
      s.readReg64 .x22 = sp + 0xb40#64 → s.readReg64 .x23 = BitVec.ofNat 64 x.input.length →
      s.readReg64 .x24 = sp + 0x4b0#64 →
      s.readReg64 .x25 = BitVec.ofNat 64 (x.input.length / 16 - m) →
      s.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sf : State,
        sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
        sf.readReg64 .x23 = BitVec.ofNat 64 x.input.length →
        sf.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → PureStepPreserved s sf →
        SepWP P target_pc sf
          (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input (x.input.length / 16)) ∗
           (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (x.input.length / 16) ++
             List.replicate (x.input.length - 16 * (x.input.length / 16)) 0#8)) ∗
           (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other) post oom) →
      SepWP P target_pc s
        (cbcSoftWork sp (aes256KeyScheduleFs x.key) (cbcChainAt x.iv x.input m) ∗
         (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input m ++
           List.replicate (x.input.length - 16 * m) 0#8)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Other) post oom := by
  intro k
  induction k with
  | zero =>
    intro m s hmk hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hv hnext
    refine cbc_tail_iter (hSplit := hSplit) cs hCal x m Other s0 s (by omega) hmod16 hlt40 hkey32 hiv16 hspAl
      hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hv
      fun sf hpc_f hrun_f hsp_f _ _ _ _ hx23_f _ _ hx26_f hx29_f hv_f hpure_f => ?_
    have hm1 : m + 1 = x.input.length / 16 := by omega
    simp only [hm1, ↓reduceIte] at hpc_f
    rw [hm1]
    exact hnext sf hpc_f hrun_f hsp_f hx23_f hx26_f hx29_f hv_f hpure_f
  | succ k ih =>
    intro m s hmk hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hv hnext
    refine cbc_tail_iter (hSplit := hSplit) cs hCal x m Other s0 s (by omega) hmod16 hlt40 hkey32 hiv16 hspAl
      hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hv
      fun s1 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 hv1 hpure1 => ?_
    have hm1 : m + 1 ≠ x.input.length / 16 := by omega
    simp only [hm1, ↓reduceIte] at hpc1
    exact ih (m + 1) s1 (by omega) hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      hx25_1 hx26_1 hv1
      fun sf hpc_f hrun_f hsp_f hx23_f hx26_f hx29_f hv_f hpure_f =>
        hnext sf hpc_f hrun_f hsp_f hx23_f hx26_f (hx29_f.trans hx29_1) hv_f (hpure1.trans hpure_f)

set_option maxHeartbeats 400000 in
theorem cbc_tail_loop {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {fnAddr : BitVec 64} {hw : Aes256DecHwAddrs}
    [hSplit : PoolAesInitSplit A hw.storageAddr]
    {keyScheduleAddr decryptAddr shimAddr allocZeroedAddr deallocAddr memcpyAddr
     handleErrorAddr errStr1Addr errStr2Addr target_pc sp outBuf : BitVec 64}
    {errStr1Relax errStr2Relax : Bool}
    (cs : CbcDecCodeSegs P fnAddr hw keyScheduleAddr decryptAddr shimAddr allocZeroedAddr
      deallocAddr memcpyAddr handleErrorAddr errStr1Addr errStr2Addr errStr1Relax errStr2Relax)
    (hCal : Aes256CbcDecryptCallees M A lim P hw keyScheduleAddr decryptAddr shimAddr
      allocZeroedAddr deallocAddr memcpyAddr handleErrorAddr)
    (x : AesCall) (w0 w4 : BitVec 64) (Rest : SepProp) (s0 s : State)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hmod16 : x.input.length % 16 = 0) (hlt40 : x.input.length < 2 ^ 40)
    (hkey32 : x.key.length = 32) (hiv16 : x.iv.length = 16)
    (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = fnAddr + 0xbc0#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx22 : s.readReg64 .x22 = sp + 0xb40#64)
    (hx24 : s.readReg64 .x24 = sp + 0x4b0#64)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x23 = BitVec.ofNat 64 x.input.length →
      sf.readReg64 .x26 = BitVec.ofNat 64 (x.input.length / 16) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → PureStepPreserved s sf →
      SepWP P target_pc sf
        (slots56 sp w0 (BitVec.ofNat 64 ((x.input.length / 16) % 4))
           (BitVec.ofNat 64 (x.input.length / 16))
           (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗
         cbcSoftWork sp (aes256KeyScheduleFs x.key)
           (cbcChainAt x.iv x.input (x.input.length / 16)) ∗
         (outBuf ↦ₛ cbcPrefixBytes x.key x.iv x.input (x.input.length / 16)) ∗
         (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Rest)
        post oom) :
    SepWP P target_pc s
      (slots56 sp w0 (BitVec.ofNat 64 ((x.input.length / 16) % 4))
         (BitVec.ofNat 64 (x.input.length / 16))
         (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗
       cbcSoftWork sp (aes256KeyScheduleFs x.key)
         (cbcChainAt x.iv x.input (4 * (x.input.length / 64))) ∗
       (outBuf ↦ₛ (cbcPrefixBytes x.key x.iv x.input (4 * (x.input.length / 64)) ++
         List.replicate (x.input.length - 64 * (x.input.length / 64)) 0#8)) ∗
       (x.inA ↦ₛ x.input) ∗ stackAt sp allocHookStack ∗ Rest)
      post oom := by
  have_instrs cs.softTailSetup 0 9
  dsimp only [slots56]
  wp_steps 3
  wp_if h_cbz
  · have htail0 : (x.input.length / 16) % 4 = 0 := by
      have heq : BitVec.ofNat 64 ((x.input.length / 16) % 4) = 0#64 := by
        simpa [wp_norm, arm64_norm] using h_cbz
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact ht
    have hm0_eq : 4 * (x.input.length / 64) = x.input.length / 16 := by omega
    have hrem0 : x.input.length - 64 * (x.input.length / 64) = 0 := by omega
    rw [hm0_eq, hrem0, List.replicate_zero, List.append_nil]
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [slots56]; try sep_ac_rfl))
      (hnext _ (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])))
  · have htail_pos : 0 < (x.input.length / 16) % 4 := by
      rcases Nat.eq_zero_or_pos ((x.input.length / 16) % 4) with hz | hp
      · exfalso; simp [wp_norm, arm64_norm, hz] at h_cbz
      · exact hp
    wp_steps 6
    let m0 := 4 * (x.input.length / 64)
    have h64_eq : 64 * (x.input.length / 64) = 16 * m0 := by dsimp [m0]; omega
    have hcnt_eq : (x.input.length / 16) % 4 = x.input.length / 16 - m0 := by dsimp [m0]; omega
    rw [h64_eq]
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [slots56, m0]; sep_ac_rfl))
      (cbc_tail_loop_from (hSplit := hSplit) cs hCal x
        (slots56 sp w0 (BitVec.ofNat 64 ((x.input.length / 16) % 4))
          (BitVec.ofNat 64 (x.input.length / 16))
          (BitVec.ofNat 64 x.input.length) w4 outBuf x.inA ∗ Rest) s0
        hmod16 hlt40 hkey32 hiv16 hspAl ((x.input.length / 16) % 4 - 1) m0 _ (by dsimp [m0]; omega)
        (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm, hsp]) (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, bv64_and_neg64_orr7 (n := x.input.length) (by omega), m0, BitVec.add_assoc])
        (by simp [wp_norm, arm64_norm, bv64_and_neg64_orr7 (n := x.input.length) (by omega), m0, BitVec.add_assoc])
        (by simp [wp_norm, arm64_norm, hx22]) (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24]) (by simp [wp_norm, arm64_norm, hcnt_eq])
        (by simp [wp_norm, arm64_norm]) (by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hv)
        fun sf hpc_f hrun_f hsp_f hx23_f hx26_f hx29_f hv_f hpure_f => ?_)
    have hrem_end : x.input.length - 16 * (x.input.length / 16) = 0 := by omega
    rw [hrem_end, List.replicate_zero, List.append_nil]
    refine sepWP_weaken_pre (Entails.of_eq (by dsimp only [slots56]; sep_ac_rfl))
      (hnext sf hpc_f hrun_f hsp_f hx23_f hx26_f (hx29_f.trans (by simp [wp_norm, arm64_norm])) hv_f
        (PureStepPreserved.trans
          (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
          hpure_f))

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.SoftTail
