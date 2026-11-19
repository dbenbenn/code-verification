/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic.WP
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Lemmas
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-! # 17-Block Parallel ARMv8 Hardware CBC Decryption Loop (`CbcDec.HwLoopPar17`) -/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopPar17

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE armv8ExpandKey armv8InvExpandedKeys armv8DecryptPar17 blocks17Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
  (decryptPar17InplaceBytesSpec bytesToBlocks17 blocks17Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (pointsTo128_eq_pointsToBytes_u128ToBytesLE u128ToBytesLE_bytesToU128LE step_ldr128 step_str128_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
  (madd_272_ofNat cbcChainAt cbcChainAt_succ cbcChainAt_length cbcPrefixBytes cbcPrefixBytes_zero
   cbcPrefixBytes_length cbcPrefixBytes_step17 zipWith_append_eq bytes16At pointsToBytes16_eq_bytes16At
   exists_bytes16 sepWP_weaken_pre sepWP_checkpoint cs_refl cs_trans step_bl_memcpy step_bl_decryptPar17)

attribute [local irreducible]
  bytesToU128LE armv8ExpandKey armv8InvExpandedKeys armv8DecryptPar17 blocks17Bytes bytesToBlocks17 cbcPrefixBytes

public section

@[expose] def hwPar17InitWords : List (BitVec 32) := [0x9121c3f7#32, 0xaa1f03fc#32, 0x5280221a#32, 0x91001ef9#32, 0x9112c3fb#32]
@[expose] def hwPar17PreMc1Words : List (BitVec 32) := [0xf9401be8#32, 0x9b1a2396#32, 0x9121c3e0#32, 0x52802202#32, 0xaa1603e1#32]
@[expose] def hwPar17PreMc2Words : List (BitVec 32) := [0x9112c3e0#32, 0xaa1603e1#32, 0x52802202#32]
@[expose] def hwPar17PreDecWords : List (BitVec 32) := [0x9103c260#32, 0x9112c3e1#32, 0x9112c3e2#32]
@[expose] def hwPar17Xor0Words : List (BitVec 32) := [
  0x397c03e9#32, 0x3952c3ea#32, 0xaa1f03e8#32, 0x397c07eb#32, 0x3952c7ec#32, 0x397c0bed#32, 0x3952cbee#32, 0x4a090149#32, 0x3952f3ef#32, 0x4a0b018a#32, 0x3912c3e9#32, 0x397c0fe9#32, 0x3912c7ea#32,
  0x4a0d01cb#32, 0x3952cfea#32, 0x3912cbeb#32, 0x3952d3eb#32, 0x397c2fec#32, 0x4a090149#32, 0x397c13ea#32, 0x3952efed#32, 0x3912cfe9#32, 0x397c33ee#32, 0x397c37f0#32, 0x4a0a0169#32, 0x397c17ea#32,
  0x3952d7eb#32, 0x3912d3e9#32, 0x3952f7f1#32, 0x4a0a0169#32, 0x397c1bea#32, 0x3952dbeb#32, 0x3912d7e9#32, 0x4a0a0169#32, 0x397c1fea#32, 0x3952dfeb#32, 0x3912dbe9#32, 0x4a0a0169#32, 0x397c23ea#32,
  0x3952e3eb#32, 0x3912dfe9#32, 0x4a0a0169#32, 0x397c27ea#32, 0x3952e7eb#32, 0x3912e3e9#32, 0x4a0a0169#32, 0x397c2bea#32, 0x3952ebeb#32, 0x3912e7e9#32, 0x4a0e01e9#32, 0x4a0a016a#32, 0x4a0c01ab#32,
  0x3912f3e9#32, 0x3912ebea#32, 0x397c3bea#32, 0x397c3fe9#32, 0x3912efeb#32, 0x3952fbeb#32, 0x3952ffed#32, 0x4a10022c#32, 0x4a0a016a#32, 0x4a0901a9#32, 0x3912f7ec#32, 0x3912fbea#32, 0x3912ffe9#32]
@[expose] def hwPar17XorLoopHeadWords : List (BitVec 32) := [0x8b080369#32, 0x38686aeb#32, 0x8b08032a#32]
@[expose] def hwPar17XorLoopBodyWords : List (BitVec 32) := [
  0x3940412c#32, 0x385fa14d#32, 0x3940452e#32, 0x385fb14f#32, 0x39404930#32, 0x91004108#32, 0x4a0b018b#32, 0x385fc14c#32, 0x4a0d01cd#32, 0x3900412b#32, 0x39404d2b#32, 0x4a0f020e#32, 0x3900452d#32, 0x3940512d#32,
  0x39406d2f#32, 0x4a0c016b#32, 0x385fd14c#32, 0x3900492e#32, 0x39004d2b#32, 0x3940114e#32, 0xf104011f#32, 0x4a0c01ab#32, 0x385fe14c#32, 0x3940552d#32, 0x3900512b#32, 0x39401550#32, 0x39407131#32,
  0x4a0c01ab#32, 0x385ff14c#32, 0x3940592d#32, 0x3900552b#32, 0x39401952#32, 0x39407520#32, 0x4a0c01ab#32, 0x3940014c#32, 0x39405d2d#32, 0x3900592b#32, 0x4a0c01ab#32, 0x3940054c#32, 0x3940612d#32,
  0x39005d2b#32, 0x4a0c01ab#32, 0x3940094c#32, 0x3940652d#32, 0x3900612b#32, 0x4a0c01ab#32, 0x39400d4c#32, 0x3940692d#32, 0x3900652b#32, 0x4a10022b#32, 0x4a0c01ac#32, 0x4a0e01ed#32, 0x3900712b#32,
  0x3900692c#32, 0x39401d4c#32, 0x3940214a#32, 0x39006d2d#32, 0x3940792d#32, 0x39407d2b#32, 0x4a12000e#32, 0x4a0c01ac#32, 0x4a0a016a#32, 0x3900752e#32, 0x3900792c#32, 0x39007d2a#32, 0x54fff781#32]
@[expose] def hwPar17PostMcWords : List (BitVec 32) := [0xf94017e8#32, 0x9b1a2380#32, 0x9112c3e1#32, 0x52802202#32, 0x9100079c#32]
@[expose] def hwPar17TailWords : List (BitVec 32) := [0x3dc042c0#32, 0xeb1c02bf#32, 0x912d03f3#32, 0x3d80f260#32, 0x54ffec41#32]

structure Par17LoopSegs (P : Program) (fnAddr memcpyAddr hwDecryptPar17Addr : BitVec 64) : Prop where
  init    : hasInstrs P (fnAddr + 0x200#64) (decodeWords hwPar17InitWords)
  preMc1  : hasInstrs P (fnAddr + 0x214#64) (decodeWords hwPar17PreMc1Words)
  blMc1   : hasInstrs P (fnAddr + 0x228#64) [.bl (memcpyAddr - (fnAddr + 0x228#64))]
  preMc2  : hasInstrs P (fnAddr + 0x22c#64) (decodeWords hwPar17PreMc2Words)
  blMc2   : hasInstrs P (fnAddr + 0x238#64) [.bl (memcpyAddr - (fnAddr + 0x238#64))]
  preDec  : hasInstrs P (fnAddr + 0x23c#64) (decodeWords hwPar17PreDecWords)
  blDec   : hasInstrs P (fnAddr + 0x248#64) [.bl (hwDecryptPar17Addr - (fnAddr + 0x248#64))]
  xor0    : hasInstrs P (fnAddr + 0x24c#64) (decodeWords hwPar17Xor0Words)
  xorHead : hasInstrs P (fnAddr + 0x350#64) (decodeWords hwPar17XorLoopHeadWords)
  xorBody : hasInstrs P (fnAddr + 0x35c#64) (decodeWords hwPar17XorLoopBodyWords)
  postMc  : hasInstrs P (fnAddr + 0x464#64) (decodeWords hwPar17PostMcWords)
  blMc3   : hasInstrs P (fnAddr + 0x478#64) [.bl (memcpyAddr - (fnAddr + 0x478#64))]
  tail    : hasInstrs P (fnAddr + 0x47c#64) (decodeWords hwPar17TailWords)

local macro "close_cs_pure" : tactic =>
  `(tactic| refine ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [calleeSavedVRegs, wp_norm, arm64_norm]⟩)

private theorem sepWP_eq {P : Program} {pc : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP P pc s P2 post oom) (heq : P1 = P2) : SepWP P pc s P1 post oom := heq ▸ h

private theorem cs19 {a b : State} (h : CalleeSavedPreserved a b) : b.readReg64 (.gpr 19#5) = a.readReg64 (.gpr 19#5) := h.1
private theorem cs22 {a b : State} (h : CalleeSavedPreserved a b) : b.readReg64 (.gpr 22#5) = a.readReg64 (.gpr 22#5) := h.2.2.2.1
private theorem cs28 {a b : State} (h : CalleeSavedPreserved a b) : b.readReg64 (.gpr 28#5) = a.readReg64 (.gpr 28#5) := h.2.2.2.2.2.2.2.2.2.1

set_option maxHeartbeats 500000 in
private theorem step_par17_xor0 {P : Program} {fnAddr target_pc sp : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x24c#64) (decodeWords hwPar17Xor0Words))
    (decBytes prevBs : List (BitVec 8)) (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hdec : decBytes.length = 272) (hprev : prevBs.length = 16) (hpc : s.pc = fnAddr + 0x24c#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x350#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 (.gpr 8#5) = 0#64 → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((sp + 0x4b0#64) ↦ₛ (List.zipWith (· ^^^ ·) (decBytes.take 16) prevBs ++ decBytes.drop 16)) ∗
        ((sp + 0xf00#64) ↦ₛ prevBs) ∗ Rest) post oom) :
    SepWP P target_pc s (((sp + 0x4b0#64) ↦ₛ decBytes) ∗ ((sp + 0xf00#64) ↦ₛ prevBs) ∗ Rest) post oom := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, hd0⟩ :=
    exists_bytes16 (show (decBytes.take 16).length = 16 by rw [List.length_take]; omega)
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, hp0⟩ := exists_bytes16 hprev
  have hsplit : ((sp + 0x4b0#64) ↦ₛ decBytes) =
      bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗ (((sp + 0x4b0#64) + 16#64) ↦ₛ decBytes.drop 16) := by
    rw [pointsToBytes_take_drop (sp + 0x4b0#64) 16 decBytes (by omega), hd0, pointsToBytes16_eq_bytes16At]
  have hp_at : ((sp + 0xf00#64) ↦ₛ prevBs) = bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 := by
    rw [hp0, pointsToBytes16_eq_bytes16At]
  have hmerge : ((sp + 0x4b0#64) ↦ₛ (List.zipWith (· ^^^ ·) (decBytes.take 16) prevBs ++ decBytes.drop 16)) =
      bytes16At (sp + 0x4b0#64) (d0 ^^^ p0) (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5) (d6 ^^^ p6) (d7 ^^^ p7)
        (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11) (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) ∗
      (((sp + 0x4b0#64) + 16#64) ↦ₛ decBytes.drop 16) := by
    rw [pointsToBytes_append, hd0, hp0]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.length_cons, List.length_nil]
    rw [pointsToBytes16_eq_bytes16At]
  refine sepWP_weaken_pre (Entails.of_eq (show _ =
      bytes16At (sp + 0x4b0#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗ (((sp + 0x4b0#64) + 16#64) ↦ₛ decBytes.drop 16) ∗
      bytes16At (sp + 0xf00#64) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ Rest by
      rw [hsplit, hp_at]; simp only [sepConj_assoc])) ?_
  have_instrs hc 0 65; dsimp only [bytes16At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps 10; wp_str8 hf_10 m1 hm1; wp_step; wp_str8 hf_12 m2 hm2; wp_steps 2; wp_str8 hf_15 m3 hm3
  wp_steps 5; wp_str8 hf_21 m4 hm4; wp_steps 5; wp_str8 hf_27 m5 hm5; wp_steps 4
  refine sepWP_checkpoint (φ := fun sM =>
      sM.pc = fnAddr + 0x2cc#64 ∧ sM.status = .Running ∧ sM.sp = sp ∧ sM.readReg64 (.gpr 8#5) = 0#64 ∧
      sM.readReg64 (.gpr 9#5) = (d5.zeroExtend 32 ^^^ p5.zeroExtend 32).zeroExtend 64 ∧
      sM.readReg64 (.gpr 10#5) = p6.zeroExtend 64 ∧ sM.readReg64 (.gpr 11#5) = d6.zeroExtend 64 ∧
      sM.readReg64 (.gpr 12#5) = p11.zeroExtend 64 ∧ sM.readReg64 (.gpr 13#5) = d11.zeroExtend 64 ∧
      sM.readReg64 (.gpr 14#5) = p12.zeroExtend 64 ∧ sM.readReg64 (.gpr 15#5) = d12.zeroExtend 64 ∧
      sM.readReg64 (.gpr 16#5) = p13.zeroExtend 64 ∧ sM.readReg64 (.gpr 17#5) = d13.zeroExtend 64 ∧
      CalleeSavedPreserved s sM ∧ PureStepPreserved s sM)
    ⟨by simp [wp_norm, arm64_norm]; try bv_lin, by simp [wp_norm, arm64_norm, hrun],
     by simp [wp_norm, arm64_norm, hsp], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by close_cs_pure,
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm5, hm4, hm3, hm2, hm1])⟩
    fun sM ⟨hpcM, hrunM, hspM, hx8M, hx9M, hx10M, hx11M, hx12M, hx13M, hx14M, hx15M, hx16M, hx17M, hcsM, hpureM⟩ => ?_
  clear m1 hm1 m2 hm2 m3 hm3 m4 hm4 m5 hm5
  wp_str8 hf_32 m6 hm6; wp_steps 3; wp_str8 hf_36 m7 hm7; wp_steps 3; wp_str8 hf_40 m8 hm8
  wp_steps 3; wp_str8 hf_44 m9 hm9; wp_steps 3; wp_str8 hf_48 m10 hm10; wp_steps 3
  wp_str8 hf_52 m11 hm11; wp_str8 hf_53 m12 hm12; wp_steps 2; wp_str8 hf_56 m13 hm13; wp_steps 5
  wp_str8 hf_62 m14 hm14; wp_str8 hf_63 m15 hm15; wp_str8 hf_64 m16 hm16
  refine sepWP_eq (hnext _ (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrunM])
      (by simp [wp_norm, arm64_norm, hspM]) (by simp [wp_norm, arm64_norm, hx8M]) (cs_trans hcsM (by close_cs_pure))
      (hpureM.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6]))))
    (by rw [hmerge, hp_at]; dsimp only [bytes16At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])

set_option maxHeartbeats 500000 in
private theorem step_par17_xor_body {P : Program} {fnAddr target_pc sp dstBlk srcBlk off : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x35c#64) (decodeWords hwPar17XorLoopBodyWords))
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 8)
    (Rest : SepProp) (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x35c#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 (.gpr 8#5) = off) (hx9 : s.readReg64 (.gpr 9#5) = dstBlk - 0x10#64)
    (hx10 : s.readReg64 (.gpr 10#5) = srcBlk + 7#64) (hx11 : s.readReg64 (.gpr 11#5) = p0.zeroExtend 64)
    (hnext : ∀ sf : State, sf.pc = (if (off + 0x10#64) != 0x100#64 then fnAddr + 0x350#64 else fnAddr + 0x464#64) →
      sf.status = .Running → sf.sp = sp → sf.readReg64 (.gpr 8#5) = off + 0x10#64 → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (bytes16At dstBlk (d0 ^^^ p0) (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5) (d6 ^^^ p6)
          (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11) (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) ∗
        bytes16At srcBlk p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ Rest) post oom) :
    SepWP P target_pc s (bytes16At dstBlk d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
      bytes16At srcBlk p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ Rest) post oom := by
  have_instrs hc 0 66; dsimp only [bytes16At]; simp only [sepConj_assoc]
  wp_steps 9; wp_str8 hf_9 m1 hm1; wp_steps 2; wp_str8 hf_12 m2 hm2; wp_steps 4
  wp_str8 hf_17 m3 hm3; wp_str8 hf_18 m4 hm4; wp_steps 5; wp_str8 hf_24 m5 hm5; wp_steps 5; wp_str8 hf_30 m6 hm6
  refine sepWP_checkpoint (φ := fun sM =>
      sM.pc = fnAddr + 0x3d8#64 ∧ sM.status = .Running ∧ sM.sp = sp ∧ sM.readReg64 (.gpr 8#5) = off + 0x10#64 ∧
      sM.readReg64 (.gpr 9#5) = dstBlk - 0x10#64 ∧ sM.readReg64 (.gpr 10#5) = srcBlk + 7#64 ∧
      sM.readReg64 (.gpr 12#5) = p6.zeroExtend 64 ∧ sM.readReg64 (.gpr 13#5) = d6.zeroExtend 64 ∧
      sM.readReg64 (.gpr 14#5) = p11.zeroExtend 64 ∧ sM.readReg64 (.gpr 15#5) = d11.zeroExtend 64 ∧
      sM.readReg64 (.gpr 16#5) = p12.zeroExtend 64 ∧ sM.readReg64 (.gpr 17#5) = d12.zeroExtend 64 ∧
      sM.pstate = subsPState64 (off + 0x10#64) 0x100#64 ∧ CalleeSavedPreserved s sM ∧ PureStepPreserved s sM)
    ⟨by simp [wp_norm, arm64_norm]; try bv_lin, by simp [wp_norm, arm64_norm, hrun], by simp [wp_norm, arm64_norm, hsp],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx9], by simp [wp_norm, arm64_norm, hx10],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by close_cs_pure,
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm6, hm5, hm4, hm3, hm2, hm1])⟩
    fun sM ⟨hpcM, hrunM, hspM, hx8M, hx9M, hx10M, hx12M, hx13M, hx14M, hx15M, hx16M, hx17M, hpsM, hcsM, hpureM⟩ => ?_
  clear m1 hm1 m2 hm2 m3 hm3 m4 hm4 m5 hm5 m6 hm6
  wp_steps 5; wp_str8 hf_36 m7 hm7; wp_steps 3; wp_str8 hf_40 m8 hm8; wp_steps 3; wp_str8 hf_44 m9 hm9
  wp_steps 3; wp_str8 hf_48 m10 hm10; wp_steps 3; wp_str8 hf_52 m11 hm11; wp_str8 hf_53 m12 hm12
  wp_steps 2; wp_str8 hf_56 m13 hm13; wp_steps 5; wp_str8 hf_62 m14 hm14; wp_str8 hf_63 m15 hm15; wp_str8 hf_64 m16 hm16
  refine sepWP_weaken_pre (Entails.of_eq (show _ =
      bytes16At dstBlk (d0 ^^^ p0) (d1 ^^^ p1) (d2 ^^^ p2) (d3 ^^^ p3) (d4 ^^^ p4) (d5 ^^^ p5) (d6 ^^^ p6)
        (d7 ^^^ p7) (d8 ^^^ p8) (d9 ^^^ p9) (d10 ^^^ p10) (d11 ^^^ p11) (d12 ^^^ p12) (d13 ^^^ p13) (d14 ^^^ p14) (d15 ^^^ p15) ∗
      bytes16At srcBlk p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ Rest by dsimp only [bytes16At]; simp only [sepConj_assoc])) ?_
  wp_step; wp_if hbr
  · have hcond : ((off + 0x10#64) != 0x100#64) = true := by
      rw [bne_iff_ne]; simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hpsM] using hbr
    exact hnext _ (by simp [wp_norm, arm64_norm, hcond]; try bv_lin) (by simp [wp_norm, arm64_norm, hrunM])
      (by simp [wp_norm, arm64_norm, hspM]) (by simp [wp_norm, arm64_norm, hx8M]) (cs_trans hcsM (by close_cs_pure))
      (hpureM.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7])))
  · have hcond : ((off + 0x10#64) != 0x100#64) = false := by
      rw [bne_eq_false_iff_eq]; simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hpsM] using hbr
    exact hnext _ (by simp [wp_norm, arm64_norm, hcond]; try bv_lin) (by simp [wp_norm, arm64_norm, hrunM])
      (by simp [wp_norm, arm64_norm, hspM]) (by simp [wp_norm, arm64_norm, hx8M]) (cs_trans hcsM (by close_cs_pure))
      (hpureM.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7])))

private theorem step_par17_xor_loop_from {P : Program}
    {fnAddr memcpyAddr hwDecryptPar17Addr target_pc sp : BitVec 64}
    (cs : Par17LoopSegs P fnAddr memcpyAddr hwDecryptPar17Addr)
    (decBytes prevBs ctChunk : List (BitVec 8)) (Rest : SepProp)
    (rem j : Nat) (hrem : rem = 16 - j) (hj : j ≤ 16)
    (hdec : decBytes.length = 272) (hprev : prevBs.length = 16) (hct : ctChunk.length = 272)
    (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (if j < 16 then fnAddr + 0x350#64 else fnAddr + 0x464#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (16 * j)) (hx23 : s.readReg64 (.gpr 23#5) = sp + 0x870#64)
    (hx25 : s.readReg64 (.gpr 25#5) = sp + 0x877#64) (hx27 : s.readReg64 (.gpr 27#5) = sp + 0x4b0#64)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x464#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((sp + 0x4b0#64) ↦ₛ List.zipWith (· ^^^ ·) decBytes (prevBs ++ ctChunk.take 256)) ∗
        ((sp + 0x870#64) ↦ₛ ctChunk) ∗ Rest) post oom) :
    SepWP P target_pc s (((sp + 0x4b0#64) ↦ₛ (List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 1)))
        (prevBs ++ ctChunk.take (16 * j)) ++ decBytes.drop (16 * (j + 1)))) ∗
      ((sp + 0x870#64) ↦ₛ ctChunk) ∗ Rest) post oom := by
  induction rem generalizing j s with
  | zero =>
    have hj16 : j = 16 := by omega
    subst hj16; simp only [Nat.lt_irrefl, ↓reduceIte] at hpc
    refine sepWP_eq (hnext s hpc hrun hsp (cs_refl s) (PureStepPreserved.refl s))
      (by rw [show 16 * (16 + 1) = 272 by rfl, show 16 * 16 = 256 by rfl,
          List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil])
  | succ rem' ih =>
    have hj_lt : j < 16 := by omega
    simp only [hj_lt, ↓reduceIte] at hpc
    let off := BitVec.ofNat 64 (16 * j)
    let dstBlk := (sp + 0x4b0#64) + BitVec.ofNat 64 (16 * (j + 1))
    let srcBlk := (sp + 0x870#64) + off
    let dSlice := (decBytes.drop (16 * (j + 1))).take 16
    let cSlice := (ctChunk.drop (16 * j)).take 16
    have hd_len : dSlice.length = 16 := by dsimp [dSlice]; rw [List.length_take, List.length_drop]; omega
    have hc_len : cSlice.length = 16 := by dsimp [cSlice]; rw [List.length_take, List.length_drop]; omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, hd_eq⟩ := exists_bytes16 hd_len
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, hp_eq⟩ := exists_bytes16 hc_len
    have hpre_len : (List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 1))) (prevBs ++ ctChunk.take (16 * j))).length =
        16 * (j + 1) := by rw [List.length_zipWith, List.length_take, List.length_append, hprev, List.length_take]; omega
    have hbuf_split : ((sp + 0x4b0#64) ↦ₛ (List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 1)))
        (prevBs ++ ctChunk.take (16 * j)) ++ decBytes.drop (16 * (j + 1)))) =
        bytes16At dstBlk d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
        (((sp + 0x4b0#64) ↦ₛ List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 1))) (prevBs ++ ctChunk.take (16 * j))) ∗
         (((sp + 0x4b0#64) + BitVec.ofNat 64 (16 * (j + 2))) ↦ₛ decBytes.drop (16 * (j + 2)))) := by
      have hds : decBytes.drop (16 * (j + 1)) = dSlice ++ decBytes.drop (16 * (j + 2)) := by
        rw [← List.take_append_drop 16 (decBytes.drop (16 * (j + 1))), List.drop_drop, show 16 * (j + 1) + 16 = 16 * (j + 2) by omega]
      rw [hds, pointsToBytes_append, hpre_len, pointsToBytes_append, hd_len, hd_eq, pointsToBytes16_eq_bytes16At]
      have hadj : dstBlk + BitVec.ofNat 64 16 = (sp + 0x4b0#64) + BitVec.ofNat 64 (16 * (j + 2)) := by
        dsimp [dstBlk]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * (j + 1) + 16 = 16 * (j + 2) by omega]
      dsimp [dstBlk] at hadj ⊢; rw [hadj]; sep_ac_rfl
    have hct_split : ((sp + 0x870#64) ↦ₛ ctChunk) =
        bytes16At srcBlk p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗
        (((sp + 0x870#64) ↦ₛ ctChunk.take (16 * j)) ∗ (((sp + 0x870#64) + BitVec.ofNat 64 (16 * (j + 1))) ↦ₛ ctChunk.drop (16 * (j + 1)))) := by
      have hcd : ctChunk.drop (16 * j) = cSlice ++ ctChunk.drop (16 * (j + 1)) := by
        rw [← List.take_append_drop 16 (ctChunk.drop (16 * j)), List.drop_drop, show 16 * j + 16 = 16 * (j + 1) by omega]
      rw [pointsToBytes_take_drop (sp + 0x870#64) (16 * j) ctChunk (by omega), hcd, pointsToBytes_append, hc_len, hp_eq, pointsToBytes16_eq_bytes16At]
      have hadj : srcBlk + BitVec.ofNat 64 16 = (sp + 0x870#64) + BitVec.ofNat 64 (16 * (j + 1)) := by
        dsimp [srcBlk, off]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * j + 16 = 16 * (j + 1) by omega]
      dsimp [srcBlk, off] at hadj ⊢; rw [hadj]; sep_ac_rfl
    let IterRest := ((sp + 0x4b0#64) ↦ₛ List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 1))) (prevBs ++ ctChunk.take (16 * j))) ∗
      (((sp + 0x4b0#64) + BitVec.ofNat 64 (16 * (j + 2))) ↦ₛ decBytes.drop (16 * (j + 2))) ∗
      ((sp + 0x870#64) ↦ₛ ctChunk.take (16 * j)) ∗ (((sp + 0x870#64) + BitVec.ofNat 64 (16 * (j + 1))) ↦ₛ ctChunk.drop (16 * (j + 1))) ∗ Rest
    refine sepWP_weaken_pre (Entails.of_eq (show _ =
        bytes16At dstBlk d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 ∗
        bytes16At srcBlk p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 ∗ IterRest by
        rw [hbuf_split, hct_split]; dsimp only [IterRest]; sep_ac_rfl)) ?_
    have_instrs cs.xorHead 0 3; dsimp only [bytes16At]; wp_steps 3
    have h16_step : BitVec.ofNat 64 (16 * (j + 1)) = BitVec.ofNat 64 (16 * j) + 0x10#64 := by
      show _ = BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 16; rw [← BitVec.ofNat_add, show 16 * j + 16 = 16 * (j + 1) by omega]
    refine step_par17_xor_body (sp := sp) (dstBlk := dstBlk) (srcBlk := srcBlk) (off := off)
      cs.xorBody d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 IterRest _
      (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hsp]) (by dsimp [off]; simp [wp_norm, arm64_norm]; try exact hx8)
      (by dsimp [dstBlk]; simp [wp_norm, arm64_norm]; rw [h16_step]; bv_lin)
      (by dsimp [srcBlk, off]; simp [wp_norm, arm64_norm]; bv_lin) (by simp [wp_norm, arm64_norm])
      fun sB hpcB hrunB hspB hx8B hcsB hpureB => ?_
    have hcs0 : CalleeSavedPreserved s sB := cs_trans (by close_cs_pure) hcsB
    have hpure0 : PureStepPreserved s sB :=
      (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])).trans hpureB
    have hoff_next : off + 0x10#64 = BitVec.ofNat 64 (16 * (j + 1)) := h16_step.symm
    have hpcB' : sB.pc = (if j + 1 < 16 then fnAddr + 0x350#64 else fnAddr + 0x464#64) := by
      rw [hoff_next] at hpcB
      by_cases hlt : j + 1 < 16
      · have hne : (BitVec.ofNat 64 (16 * (j + 1)) != 0x100#64) = true := by
          rw [bne_iff_ne]; intro heq; have := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * (j + 1) < 2 ^ 64)] at this
          have h256 : (0x100#64 : BitVec 64).toNat = 256 := rfl; omega
        simpa [hlt, hne] using hpcB
      · have hj16 : j + 1 = 16 := by omega
        rw [hj16] at hpcB ⊢; exact hpcB
    refine sepWP_eq (ih (j + 1) (by omega) (by omega) sB hpcB' hrunB hspB (hoff_next ▸ hx8B)
      (hcs0.2.2.2.2.1.trans hx23) (hcs0.2.2.2.2.2.2.1.trans hx25) (hcs0.2.2.2.2.2.2.2.2.1.trans hx27)
      fun sf hpc_f hrun_f hsp_f hcs_f hpure_f =>
        hnext sf hpc_f hrun_f hsp_f (cs_trans hcs0 hcs_f) (hpure0.trans hpure_f)) ?_
    have hdt : decBytes.take (16 * (j + 2)) = decBytes.take (16 * (j + 1)) ++ dSlice := by
      rw [show 16 * (j + 2) = 16 * (j + 1) + 16 by omega, List.take_add]
    have hct' : ctChunk.take (16 * (j + 1)) = ctChunk.take (16 * j) ++ cSlice := by
      rw [show 16 * (j + 1) = 16 * j + 16 by omega, List.take_add]
    have hl : (decBytes.take (16 * (j + 1))).length = (prevBs ++ ctChunk.take (16 * j)).length := by
      rw [List.length_take, List.length_append, hprev, List.length_take]; omega
    have hpost_len : (List.zipWith (· ^^^ ·) (decBytes.take (16 * (j + 2))) (prevBs ++ ctChunk.take (16 * (j + 1)))).length =
        16 * (j + 2) := by rw [List.length_zipWith, List.length_take, List.length_append, hprev, List.length_take]; omega
    rw [pointsToBytes_append (sp + 0x4b0#64), hpost_len, hdt, hct', ← List.append_assoc, zipWith_append_eq _ hl, hd_eq, hp_eq]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [pointsToBytes_append, hpre_len, pointsToBytes16_eq_bytes16At, hct_split]
    dsimp only [IterRest, dstBlk]; sep_ac_rfl

private structure Par17Inv (sp : BitVec 64) (q17 : Nat) (s0 s : State) : Prop where
  x20 : s.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5)
  x21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 q17
  x23 : s.readReg64 (.gpr 23#5) = sp + 0x870#64
  x24 : s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : s.readReg64 (.gpr 25#5) = sp + 0x877#64
  x26 : s.readReg64 (.gpr 26#5) = 0x110#64
  x27 : s.readReg64 (.gpr 27#5) = sp + 0x4b0#64
  x29 : s.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  pure : PureStepPreserved s0 s

private theorem Par17Inv.step {sp : BitVec 64} {q17 : Nat} {s0 s sf : State}
    (inv : Par17Inv sp q17 s0 s) (hcs : CalleeSavedPreserved s sf) (hpure : PureStepPreserved s sf) :
    Par17Inv sp q17 s0 sf :=
  ⟨hcs.2.1.trans inv.x20, hcs.2.2.1.trans inv.x21, hcs.2.2.2.2.1.trans inv.x23,
   hcs.2.2.2.2.2.1.trans inv.x24, hcs.2.2.2.2.2.2.1.trans inv.x25, hcs.2.2.2.2.2.2.2.1.trans inv.x26,
   hcs.2.2.2.2.2.2.2.2.1.trans inv.x27, hcs.2.2.2.2.2.2.2.2.2.2.1.trans inv.x29,
   hcs.2.2.2.2.2.2.2.2.2.2.2.trans inv.vregs, inv.pure.trans hpure⟩

private theorem Par17Inv.step2 {sp : BitVec 64} {q17 : Nat} {s0 sm sf : State}
    (hcs2 : CalleeSavedPreserved sm sf) (hpure2 : PureStepPreserved sm sf)
    (inv1 : Par17Inv sp q17 s0 sm) : Par17Inv sp q17 s0 sf := inv1.step hcs2 hpure2

local macro "step_inv_pure" inv:term "," hmem:term : tactic =>
  `(tactic| refine ⟨(by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x20,
    (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x21, (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x23,
    (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x24, (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x25,
    (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x26, (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x27,
    (by simp [wp_norm, arm64_norm] : _ = _).trans ($inv).x29,
    (by simp [calleeSavedVRegs, wp_norm, arm64_norm] : _ = _).trans ($inv).vregs,
    ($inv).pure.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) $hmem)⟩)

private def par17LoopSpatial (sp outBuf inA : BitVec 64) (key iv ct : List (BitVec 8))
    (k : Nat) (Rest : SepProp) : SepProp :=
  (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * k)) ∗ memRegion (outBuf + BitVec.ofNat 64 (272 * k)) (ct.length - 272 * k) ∗
  (inA ↦ₛ ct) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
  memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
  roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗ ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (17 * k)) ∗ Rest

private theorem step_par17_loop_from {P : Program}
    {fnAddr memcpyAddr hwDecryptPar17Addr target_pc sp outBuf inA : BitVec 64}
    (cs : Par17LoopSegs P fnAddr memcpyAddr hwDecryptPar17Addr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hDecPar17 : subroutine_ok P hwDecryptPar17Addr decryptPar17InplaceBytesSpec)
    (key iv ct : List (BitVec 8)) (Rest : SepProp) (rem k : Nat) (hrem : rem = ct.length / 272 - k) (hk : k < ct.length / 272)
    (hkey : key.length = 32) (hiv : iv.length = 16) (hct_lt : ct.length < 2 ^ 40)
    (s0 s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x214#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 (.gpr 19#5) = sp + 0xb40#64) (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 k)
    (hinv : Par17Inv sp (ct.length / 272) s0 s)
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x490#64 → sf.status = .Running → sf.sp = sp →
      Par17Inv sp (ct.length / 272) s0 sf →
      SepWP P target_pc sf (par17LoopSpatial sp outBuf inA key iv ct (ct.length / 272) Rest) post oom) :
    SepWP P target_pc s (par17LoopSpatial sp outBuf inA key iv ct k Rest) post oom := by
  induction rem generalizing k s with
  | zero => omega
  | succ rem' ih =>
    dsimp only [par17LoopSpatial]
    have hspAl_s : ∀ st : State, st.sp = sp → st.spAligned = true := fun st hst => by simpa [State.spAligned, hst] using hspAl
    let ctChunk := (ct.drop (272 * k)).take 272
    let srcPtr := inA + BitVec.ofNat 64 (272 * k)
    let dstPtr := outBuf + BitVec.ofNat 64 (272 * k)
    let dk := armv8InvExpandedKeys (armv8ExpandKey key)
    let prevBs := cbcChainAt iv ct (17 * k)
    have hchunk_len : ctChunk.length = 272 := by dsimp [ctChunk]; rw [List.length_take, List.length_drop]; omega
    have hprev_len : prevBs.length = 16 := cbcChainAt_length hiv (by omega)
    have hct_split : (inA ↦ₛ ct) = (srcPtr ↦ₛ ctChunk) ∗ ((inA ↦ₛ ct.take (272 * k)) ∗
        ((inA + BitVec.ofNat 64 (272 * (k + 1))) ↦ₛ ct.drop (272 * (k + 1)))) := by
      have hcd : ct.drop (272 * k) = ctChunk ++ ct.drop (272 * (k + 1)) := by
        rw [← List.take_append_drop 272 (ct.drop (272 * k)), List.drop_drop, show 272 * k + 272 = 272 * (k + 1) by omega]
      rw [pointsToBytes_take_drop inA (272 * k) ct (by omega), hcd, pointsToBytes_append, hchunk_len]
      have hadj : srcPtr + BitVec.ofNat 64 272 = inA + BitVec.ofNat 64 (272 * (k + 1)) := by
        dsimp [srcPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 272 * k + 272 = 272 * (k + 1) by omega]
      dsimp [srcPtr] at hadj ⊢; rw [hadj]; sep_ac_rfl
    have hout_split : memRegion dstPtr (ct.length - 272 * k) = memRegion dstPtr 272 ∗
        memRegion (outBuf + BitVec.ofNat 64 (272 * (k + 1))) (ct.length - 272 * (k + 1)) := by
      rw [memRegion_split_le dstPtr 272 (ct.length - 272 * k) (by omega) (by omega)]
      have hadj : dstPtr + BitVec.ofNat 64 272 = outBuf + BitVec.ofNat 64 (272 * (k + 1)) := by
        dsimp [dstPtr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 272 * k + 272 = 272 * (k + 1) by omega]
      rw [hadj, show ct.length - 272 * k - 272 = ct.length - 272 * (k + 1) by omega]
    have_instrs cs.preMc1 0 5; wp_steps 5
    have hx22_val : inA + BitVec.ofNat 64 k * 0x110#64 = srcPtr := madd_272_ofNat inA k
    refine step_bl_memcpy cs.blMc1 hMemcpy (dst := sp + 0x870#64) (src := srcPtr) (bs := ctChunk) (sp := sp)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp])
      (hspAl_s _ (by simp [wp_norm, arm64_norm, hsp])) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hinv.x26, hx22_val])
      (by rw [hchunk_len]; simp [wp_norm, arm64_norm]) (by omega) (by rw [hct_split, hchunk_len]; sep_ac_rfl)
      fun s1 hpc1 hrun1 hsp1 hcs1 hpure1 => ?_
    clear hf_0 hf_1 hf_2 hf_3 hf_4; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpc1
    have hinv1 := Par17Inv.step2 hcs1 hpure1 (by step_inv_pure hinv, (by simp [wp_norm, arm64_norm]))
    have hx19_1 : s1.readReg64 (.gpr 19#5) = sp + 0xb40#64 := (cs19 hcs1).trans (by simp [wp_norm, arm64_norm, hx19])
    have hx22_1 : s1.readReg64 (.gpr 22#5) = srcPtr := (cs22 hcs1).trans (by simp [wp_norm, arm64_norm, hinv.x26, hx22_val])
    have hx28_1 : s1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 k := (cs28 hcs1).trans (by simp [wp_norm, arm64_norm, hx28])
    have_instrs cs.preMc2 0 3; wp_steps 3
    refine step_bl_memcpy cs.blMc2 hMemcpy (dst := sp + 0x4b0#64) (src := srcPtr) (bs := ctChunk) (sp := sp)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1])
      (hspAl_s _ (by simp [wp_norm, arm64_norm, hsp1])) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by rw [hchunk_len]; simp [wp_norm, arm64_norm])
      (by omega) (by rw [hchunk_len]; sep_ac_rfl) fun s2 hpc2 hrun2 hsp2 hcs2 hpure2 => ?_
    clear hf_0 hf_1 hf_2; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpc2
    have hinv2 := Par17Inv.step2 hcs2 hpure2 (by step_inv_pure hinv1, (by simp [wp_norm, arm64_norm]))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = sp + 0xb40#64 := (cs19 hcs2).trans (by simp [wp_norm, arm64_norm, hx19_1])
    have hx22_2 : s2.readReg64 (.gpr 22#5) = srcPtr := (cs22 hcs2).trans (by simp [wp_norm, arm64_norm, hx22_1])
    have hx28_2 : s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 k := (cs28 hcs2).trans (by simp [wp_norm, arm64_norm, hx28_1])
    have_instrs cs.preDec 0 3; wp_steps 3
    refine step_bl_decryptPar17 cs.blDec hDecPar17 (dkPtr := sp + 0xc30#64) (bufPtr := sp + 0x4b0#64)
      (dk := dk) (bs := ctChunk) (sp := sp) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun2]) (by simp [wp_norm, arm64_norm, hsp2])
      (hspAl_s _ (by simp [wp_norm, arm64_norm, hsp2])) (by simp [wp_norm, arm64_norm]; try bv_lin)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) hchunk_len (by dsimp [dk]; sep_ac_rfl)
      fun s3 hpc3 hrun3 hsp3 hcs3 hpure3 => ?_
    clear hf_0 hf_1 hf_2; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpc3
    have hinv3 := Par17Inv.step2 hcs3 hpure3 (by step_inv_pure hinv2, (by simp [wp_norm, arm64_norm]))
    have hx22_3 : s3.readReg64 (.gpr 22#5) = srcPtr := (cs22 hcs3).trans (by simp [wp_norm, arm64_norm, hx22_2])
    have hx28_3 : s3.readReg64 (.gpr 28#5) = BitVec.ofNat 64 k := (cs28 hcs3).trans (by simp [wp_norm, arm64_norm, hx28_2])
    let decBytes := blocks17Bytes (armv8DecryptPar17 dk (bytesToBlocks17 ctChunk))
    have hdec_len : decBytes.length = 272 := blocks17Bytes_length _
    let FrameK := (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * k)) ∗
      memRegion (outBuf + BitVec.ofNat 64 (272 * (k + 1))) (ct.length - 272 * (k + 1)) ∗
      (inA ↦ₛ ct.take (272 * k)) ∗ ((inA + BitVec.ofNat 64 (272 * (k + 1))) ↦ₛ ct.drop (272 * (k + 1))) ∗
      ((sp + 0x030#64) ↦₆₄ inA) ∗ roundKeys15At (sp + 0xc30#64) dk ∗ Rest
    refine sepWP_eq (step_par17_xor0 (sp := sp) cs.xor0 decBytes prevBs
      (((sp + 0x870#64) ↦ₛ ctChunk) ∗ memRegion dstPtr 272 ∗ (srcPtr ↦ₛ ctChunk) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ FrameK)
      s3 hdec_len hprev_len hpc3 hrun3 hsp3 hspAl fun s4 hpc4 hrun4 hsp4 hx8_4 hcs4 hpure4 => ?_)
      (by rw [hout_split]; dsimp only [decBytes, prevBs, FrameK]; sep_frame)
    have hinv4 := hinv3.step hcs4 hpure4
    refine sepWP_eq (step_par17_xor_loop_from (sp := sp) cs decBytes prevBs ctChunk
      (((sp + 0xf00#64) ↦ₛ prevBs) ∗ memRegion dstPtr 272 ∗ (srcPtr ↦ₛ ctChunk) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ FrameK)
      16 0 rfl (by decide) hdec_len hprev_len hchunk_len s4 (by simpa using hpc4) hrun4 hsp4
      (by simpa using hx8_4) hinv4.x23 hinv4.x25 hinv4.x27 fun s5 hpc5 hrun5 hsp5 hcs5 hpure5 => ?_) (by simp; sep_frame)
    have hinv5 := hinv4.step hcs5 hpure5
    have hcs45 := cs_trans hcs4 hcs5
    have hx22_5 : s5.readReg64 (.gpr 22#5) = srcPtr := (cs22 hcs45).trans hx22_3
    have hx28_5 : s5.readReg64 (.gpr 28#5) = BitVec.ofNat 64 k := (cs28 hcs45).trans hx28_3
    let ptChunk := List.zipWith (· ^^^ ·) decBytes (prevBs ++ ctChunk.take 256)
    have hpt_len : ptChunk.length = 272 := by
      dsimp [ptChunk]; rw [List.length_zipWith, hdec_len, List.length_append, hprev_len, List.length_take]; omega
    have_instrs cs.postMc 0 5; wp_steps 5
    have hdst_val : outBuf + BitVec.ofNat 64 k * 0x110#64 = dstPtr := madd_272_ofNat outBuf k
    have hx28_inc : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
      show BitVec.ofNat 64 k + BitVec.ofNat 64 1 = _; rw [← BitVec.ofNat_add]
    refine step_bl_memcpy cs.blMc3 hMemcpy (dst := dstPtr) (src := sp + 0x4b0#64) (bs := ptChunk) (sp := sp)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun5]) (by simp [wp_norm, arm64_norm, hsp5])
      (hspAl_s _ (by simp [wp_norm, arm64_norm, hsp5])) (by simp [wp_norm, arm64_norm, hinv5.x26, hdst_val])
      (by simp [wp_norm, arm64_norm]) (by rw [hpt_len]; simp [wp_norm, arm64_norm])
      (by omega) (by dsimp only [ptChunk]; rw [hpt_len]; sep_frame) fun s6 hpc6 hrun6 hsp6 hcs6 hpure6 => ?_
    clear hf_0 hf_1 hf_2 hf_3 hf_4; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpc6
    have hinv6 := Par17Inv.step2 hcs6 hpure6 (by step_inv_pure hinv5, (by simp [wp_norm, arm64_norm]))
    have hx22_6 : s6.readReg64 (.gpr 22#5) = srcPtr := (cs22 hcs6).trans (by simp [wp_norm, arm64_norm, hx22_5])
    have hx28_6 : s6.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (k + 1) := (cs28 hcs6).trans (by simp [wp_norm, arm64_norm, hx28_inc])
    let nextIv := cbcChainAt iv ct (17 * (k + 1))
    have hnextIv_eq : ctChunk.drop 256 = nextIv := by
      dsimp [ctChunk, nextIv]; rw [show 17 * (k + 1) = (17 * k + 16) + 1 by omega, cbcChainAt_succ,
          List.drop_take, List.drop_drop, show 272 * k + 256 = 16 * (17 * k + 16) by omega]
    have hnextIv_len : nextIv.length = 16 := cbcChainAt_length hiv (by omega)
    have hsrc_split17 : (srcPtr ↦ₛ ctChunk) = ((srcPtr ↦ₛ ctChunk.take 256) ∗ ((srcPtr + 0x100#64) ↦₁₂₈ bytesToU128LE nextIv)) := by
      rw [pointsToBytes_take_drop srcPtr 256 ctChunk (by omega), hnextIv_eq,
          pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hnextIv_len]
    have hprev_128 : ((sp + 0xf00#64) ↦ₛ prevBs) = ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE prevBs) := by
      rw [pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hprev_len]
    have_instrs cs.tail 0 5
    refine sepWP_eq (step_ldr128 hf_0 (ea := srcPtr + 0x100#64) (v := bytesToU128LE nextIv)
      hpc6 hrun6 (by rw [hx22_6]) rfl (F := ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE prevBs) ∗
        ((srcPtr ↦ₛ ctChunk.take 256) ∗ (dstPtr ↦ₛ ptChunk) ∗ ((sp + 0x4b0#64) ↦ₛ ptChunk) ∗
         ((sp + 0x870#64) ↦ₛ ctChunk) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ FrameK)) ?_)
      (by rw [hsrc_split17, hprev_128]; sep_ac_rfl)
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps 2
    refine step_str128_perm hf_3 (ea := sp + 0xf00#64) (old := bytesToU128LE prevBs) (val := bytesToU128LE nextIv)
      (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun6])
      (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm])
      (by rw [sepConj_left_comm]) fun m7 hm7 => ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hout_join : ((outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * k)) ∗ (dstPtr ↦ₛ ptChunk)) =
        (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * (k + 1))) := by
      have hpfx_len : (cbcPrefixBytes key iv ct (17 * k)).length = 272 * k := by rw [cbcPrefixBytes_length (by omega)]; omega
      have hstep17 := cbcPrefixBytes_step17 (m := 17 * k) hkey hiv (by omega)
        (show ctChunk = (ct.drop (16 * (17 * k))).take 272 by dsimp [ctChunk]; rw [show 272 * k = 16 * (17 * k) by omega])
      rw [show 17 * k + 17 = 17 * (k + 1) by omega] at hstep17; rw [← hstep17, pointsToBytes_append, hpfx_len]
    have hent_post :
        (((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE nextIv) ∗ (((srcPtr + 0x100#64) ↦₁₂₈ bytesToU128LE nextIv) ∗
         ((srcPtr ↦ₛ ctChunk.take 256) ∗ (dstPtr ↦ₛ ptChunk) ∗ ((sp + 0x4b0#64) ↦ₛ ptChunk) ∗
          ((sp + 0x870#64) ↦ₛ ctChunk) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ FrameK))) ⊢
        par17LoopSpatial sp outBuf inA key iv ct (k + 1) Rest := by
      dsimp only [FrameK, par17LoopSpatial, dk, nextIv]
      have hm4b0 : ((sp + 0x4b0#64) ↦ₛ ptChunk) ⊢ memRegion (sp + 0x4b0#64) 0x110 := by
        have h := pointsToBytes_entails_memRegion (sp + 0x4b0#64) ptChunk; rwa [hpt_len] at h
      have hm870 : ((sp + 0x870#64) ↦ₛ ctChunk) ⊢ memRegion (sp + 0x870#64) 0x110 := by
        have h := pointsToBytes_entails_memRegion (sp + 0x870#64) ctChunk; rwa [hchunk_len] at h
      have hf00 : ((sp + 0xf00#64) ↦₁₂₈ bytesToU128LE nextIv) = ((sp + 0xf00#64) ↦ₛ nextIv) := by
        rw [pointsTo128_eq_pointsToBytes_u128ToBytesLE, u128ToBytesLE_bytesToU128LE hnextIv_len]
      rw [hf00]
      refine Entails.trans (Entails.of_eq (show _ = (((sp + 0x4b0#64) ↦ₛ ptChunk) ∗ ((sp + 0x870#64) ↦ₛ ctChunk)) ∗
          (((outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * k)) ∗ (dstPtr ↦ₛ ptChunk)) ∗
           (((srcPtr ↦ₛ ctChunk.take 256) ∗ ((srcPtr + 0x100#64) ↦₁₂₈ bytesToU128LE nextIv)) ∗
            ((inA ↦ₛ ct.take (272 * k)) ∗ ((inA + BitVec.ofNat 64 (272 * (k + 1))) ↦ₛ ct.drop (272 * (k + 1))))) ∗
           memRegion (outBuf + BitVec.ofNat 64 (272 * (k + 1))) (ct.length - 272 * (k + 1)) ∗
           ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗ roundKeys15At (sp + 0xc30#64) dk ∗ ((sp + 0xf00#64) ↦ₛ nextIv) ∗ Rest) by sep_ac_rfl)) ?_
      rw [hout_join, ← hsrc_split17]
      refine Entails.trans (sepConj_mono_left (sepConj_mono hm4b0 hm870)) ?_
      rw [← hct_split]; dsimp only [dk, nextIv]; exact Entails.of_eq (by sep_ac_rfl)
    refine sepWP_weaken_pre hent_post ?_
    wp_step; wp_if hbr_outer
    · have hk_lt : k + 1 < ct.length / 272 := by
        have hne : BitVec.ofNat 64 (ct.length / 272) ≠ BitVec.ofNat 64 (k + 1) := by
          simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hinv6.x21, hx28_6] using hbr_outer
        by_contra hge; exact hne (congrArg (BitVec.ofNat 64) (by omega))
      exact ih (k + 1) (by omega) hk_lt _ (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun6]) (by simp [wp_norm, arm64_norm, hsp6])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx28_6])
        (by step_inv_pure hinv6, (by simp [wp_norm, arm64_norm, hm7]))
    · have hk_eq : k + 1 = ct.length / 272 := by
        have heq : BitVec.ofNat 64 (ct.length / 272) = BitVec.ofNat 64 (k + 1) := by
          simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hinv6.x21, hx28_6] using hbr_outer
        have ht := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length / 272 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)] at ht; exact ht.symm
      rw [hk_eq]
      exact hnext _ (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun6])
        (by simp [wp_norm, arm64_norm, hsp6]) (by step_inv_pure hinv6, (by simp [wp_norm, arm64_norm, hm7]))

theorem step_par17_loop {P : Program} {fnAddr memcpyAddr hwDecryptPar17Addr target_pc sp outBuf inA : BitVec 64}
    (cs : Par17LoopSegs P fnAddr memcpyAddr hwDecryptPar17Addr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hDecPar17 : subroutine_ok P hwDecryptPar17Addr decryptPar17InplaceBytesSpec)
    (key iv ct : List (BitVec 8)) (Rest : SepProp) (hq_pos : 0 < ct.length / 272)
    (hkey : key.length = 32) (hiv : iv.length = 16) (hct_lt : ct.length < 2 ^ 40)
    (s : State) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr + 0x200#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (hspAl : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 (.gpr 19#5) = sp + 0xb40#64) (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (ct.length / 272))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x490#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) → sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) → calleeSavedVRegs sf = calleeSavedVRegs s → PureStepPreserved s sf →
      SepWP P target_pc sf ((outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * (ct.length / 272))) ∗
        memRegion (outBuf + BitVec.ofNat 64 (272 * (ct.length / 272))) (ct.length - 272 * (ct.length / 272)) ∗
        (inA ↦ₛ ct) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗ memRegion (sp + 0x4b0#64) 0x110 ∗
        memRegion (sp + 0x870#64) 0x110 ∗ roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
        ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (17 * (ct.length / 272))) ∗ Rest) post oom) :
    SepWP P target_pc s
      (memRegion outBuf ct.length ∗ (inA ↦ₛ ct) ∗ ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
       memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
       roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗ ((sp + 0xf00#64) ↦ₛ iv) ∗ Rest) post oom := by
  have_instrs cs.init 0 5; wp_steps 5
  have hout0 : memRegion outBuf ct.length = (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * 0)) ∗
      memRegion (outBuf + BitVec.ofNat 64 (272 * 0)) (ct.length - 272 * 0) := by simp [cbcPrefixBytes_zero]
  refine sepWP_eq (step_par17_loop_from cs hMemcpy hDecPar17 key iv ct Rest (ct.length / 272) 0 rfl hq_pos hkey hiv hct_lt s _
    (by simp [wp_norm, arm64_norm]; try bv_lin) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hsp]) hspAl (by simp [wp_norm, arm64_norm, hx19]) (by simp [wp_norm, arm64_norm])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx21], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], by simp [calleeSavedVRegs, wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])⟩
    fun sf hpc_f hrun_f hsp_f hinv_f =>
      hnext sf hpc_f hrun_f hsp_f hinv_f.x20 hinv_f.x24 hinv_f.x29 hinv_f.vregs hinv_f.pure)
    (by dsimp only [par17LoopSpatial, cbcChainAt]; rw [hout0]; sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopPar17
