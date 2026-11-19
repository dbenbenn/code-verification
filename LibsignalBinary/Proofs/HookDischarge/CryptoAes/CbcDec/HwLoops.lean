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
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Lemmas
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopPar17
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopRem

/-!
# ARMv8 Hardware CBC Decryption Loops (`CbcDec.HwLoops`)

Top-level verification of the self-contained `266`-instruction ARMv8 hardware CBC decryption loop
slice (`fnAddr + 0x1d4#64 .. fnAddr + 0x5fc#64` → `fnAddr + 0xd20#64`) of
`signal_crypto::aes_cbc::aes_256_cbc_decrypt`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoops

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open CryptoGames.CBC (bytesToBlock blockToBytesLE chunks16 cbcDecryptBlocks)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved step_str64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (armv8ExpandKey armv8InvExpandedKeys roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec (decrypt15InplaceSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17 (decryptPar17InplaceBytesSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
  (hasInstrs_step umulh_magic272_lsr8 add_lsl4_ofNat cbcChainAt cbcChainAt_length
   cbcPrefixBytes cbcPrefixBytes_zero cbcPrefixBytes_full sepWP_weaken_pre)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopPar17
  (hwPar17InitWords hwPar17PreMc1Words hwPar17PreMc2Words hwPar17PreDecWords
   hwPar17Xor0Words hwPar17XorLoopHeadWords hwPar17XorLoopBodyWords
   hwPar17PostMcWords hwPar17TailWords Par17LoopSegs step_par17_loop)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopRem
  (hwRemSetupWords hwRemPreDecWords hwRemPostWords hwRemExitWords RemLoopSegs step_cbcDec_hwRem)

attribute [local irreducible]
  Spec.Aes256.aes256Dec armv8ExpandKey armv8InvExpandedKeys cbcPrefixBytes

public section

/-! ## 1. `266`-Instruction Slice & Segment Decomposition -/

@[expose] def hwSetupWords : List (BitVec 32) := [
  0xb204cfe8#32, 0xf29e1e28#32, 0x9bc87f28#32, 0xd348fd15#32, 0x8b1512a8#32, 0xeb080134#32,
  0xf90073e8#32, 0x540060a3#32, 0xf104433f#32, 0x912d03f3#32, 0x540014a3#32]

/-- Placement-generic `266`-instruction ARMv8 hardware CBC decryption loop slice
    (`fnAddr + 0x1d4#64 .. fnAddr + 0x5fc#64`). -/
@[expose] def cbcDecHwLoopInstrs
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) : List Instr :=
  List.flatten
    [ decodeWords hwSetupWords, decodeWords hwPar17InitWords, decodeWords hwPar17PreMc1Words,
      [.bl (memcpyAddr - (fnAddr + 0x228#64))], decodeWords hwPar17PreMc2Words,
      [.bl (memcpyAddr - (fnAddr + 0x238#64))], decodeWords hwPar17PreDecWords,
      [.bl (hwDecryptPar17Addr - (fnAddr + 0x248#64))],
      decodeWords hwPar17Xor0Words, decodeWords hwPar17XorLoopHeadWords,
      decodeWords hwPar17XorLoopBodyWords, decodeWords hwPar17PostMcWords,
      [.bl (memcpyAddr - (fnAddr + 0x478#64))], decodeWords hwPar17TailWords,
      decodeWords hwRemSetupWords, decodeWords hwRemPreDecWords,
      [.bl (hwDecryptAddr - (fnAddr + 0x4d8#64))],
      decodeWords hwRemPostWords, decodeWords hwRemExitWords ]

/-- Raw `266`-word list parameterized by the 5 relocated `BL` instruction words. -/
@[expose] def cbcDecHwLoopWords (blMc1 blMc2 blDecPar17 blMc3 blDec1 : BitVec 32) :
    List (BitVec 32) :=
  hwSetupWords ++ hwPar17InitWords ++ hwPar17PreMc1Words ++ [blMc1] ++
  hwPar17PreMc2Words ++ [blMc2] ++ hwPar17PreDecWords ++ [blDecPar17] ++
  hwPar17Xor0Words ++ hwPar17XorLoopHeadWords ++ hwPar17XorLoopBodyWords ++
  hwPar17PostMcWords ++ [blMc3] ++ hwPar17TailWords ++ hwRemSetupWords ++
  hwRemPreDecWords ++ [blDec1] ++ hwRemPostWords ++ hwRemExitWords

theorem cbcDecHwLoopInstrs_length
    (fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64) :
    (cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr).length = 266 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [cbcDecHwLoopInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]; rfl

theorem decodeWords_cbcDecHwLoopWords
    {fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64}
    {blMc1 blMc2 blDecPar17 blMc3 blDec1 : BitVec 32}
    (h1 : decodeWord blMc1 = .bl (memcpyAddr - (fnAddr + 0x228#64)))
    (h2 : decodeWord blMc2 = .bl (memcpyAddr - (fnAddr + 0x238#64)))
    (h3 : decodeWord blDecPar17 = .bl (hwDecryptPar17Addr - (fnAddr + 0x248#64)))
    (h4 : decodeWord blMc3 = .bl (memcpyAddr - (fnAddr + 0x478#64)))
    (h5 : decodeWord blDec1 = .bl (hwDecryptAddr - (fnAddr + 0x4d8#64))) :
    decodeWords (cbcDecHwLoopWords blMc1 blMc2 blDecPar17 blMc3 blDec1) =
      cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr := by
  simp [cbcDecHwLoopWords, cbcDecHwLoopInstrs, decodeWords, List.map_append, h1, h2, h3, h4, h5]

private theorem split_cbcDecHwLoopInstrs {P : Program}
    {fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x1d4#64)
      (cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr)) :
    hasInstrs P (fnAddr + 0x1d4#64) (decodeWords hwSetupWords) ∧
    Par17LoopSegs P fnAddr memcpyAddr hwDecryptPar17Addr ∧
    RemLoopSegs P fnAddr hwDecryptAddr := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  have hflat : cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr =
      decodeWords hwSetupWords ++ (decodeWords hwPar17InitWords ++
      (decodeWords hwPar17PreMc1Words ++ ([.bl (memcpyAddr - (fnAddr + 0x228#64))] ++
      (decodeWords hwPar17PreMc2Words ++ ([.bl (memcpyAddr - (fnAddr + 0x238#64))] ++
      (decodeWords hwPar17PreDecWords ++ ([.bl (hwDecryptPar17Addr - (fnAddr + 0x248#64))] ++
      (decodeWords hwPar17Xor0Words ++ (decodeWords hwPar17XorLoopHeadWords ++
      (decodeWords hwPar17XorLoopBodyWords ++ (decodeWords hwPar17PostMcWords ++
      ([.bl (memcpyAddr - (fnAddr + 0x478#64))] ++ (decodeWords hwPar17TailWords ++
      (decodeWords hwRemSetupWords ++ (decodeWords hwRemPreDecWords ++
      ([.bl (hwDecryptAddr - (fnAddr + 0x4d8#64))] ++
      (decodeWords hwRemPostWords ++ decodeWords hwRemExitWords))))))))))))))))) := by
    simp [cbcDecHwLoopInstrs]
  rw [hflat] at hc
  have ⟨s0, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x200#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s1, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x214#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s2, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x228#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s3, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x22c#64) hc (by rw [BitVec.add_assoc]; rfl)
  have ⟨s4, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x238#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s5, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x23c#64) hc (by rw [BitVec.add_assoc]; rfl)
  have ⟨s6, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x248#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s7, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x24c#64) hc (by rw [BitVec.add_assoc]; rfl)
  have ⟨s8, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x350#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s9, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x35c#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s10, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x464#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s11, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x478#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s12, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x47c#64) hc (by rw [BitVec.add_assoc]; rfl)
  have ⟨s13, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x490#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s14, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x4c0#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s15, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x4d8#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  have ⟨s16, hc⟩ := hasInstrs_step (pc2 := fnAddr + 0x4dc#64) hc (by rw [BitVec.add_assoc]; rfl)
  have ⟨s17, s18⟩ := hasInstrs_step (pc2 := fnAddr + 0x5f8#64) hc (by rw [hd, BitVec.add_assoc]; rfl)
  exact ⟨s0, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩, ⟨s14, s15, s16, s17, s18⟩⟩

private theorem sepWP_eq {P : Program} {pc : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP P pc s P2 post oom) (heq : P1 = P2) : SepWP P pc s P1 post oom :=
  heq ▸ h

private theorem sepWP_mem64_elim {P : Program} {pc p : BitVec 64} {Rest : SepProp} {s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hk : ∀ v : BitVec 64, SepWP P pc s ((p ↦₆₄ v) ∗ Rest) post oom) :
    SepWP P pc s (memRegion p 8 ∗ Rest) post oom := by
  rw [memRegion_eq_exists_bytes p 8 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hbs => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at hbs
  rw [pointsToBytes8_eq_pointsTo64]; exact hk _

/-! ## 2. Top-Level `SepWP` Continuation Theorem (`step_cbcDec_hwLoops`) -/

/-- Full verification of the `266`-instruction ARMv8 hardware CBC decryption loops
    (`fnAddr + 0x1d4#64` → `fnAddr + 0xd20#64`), covering magic-constant `272` division,
    `decrypt_par::<15, U17>` `17`-block chunks, and `decrypt::<15>` `1`-block remainder blocks. -/
theorem step_cbcDec_hwLoops {P : Program}
    {fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr target_pc sp outBuf inA : BitVec 64}
    (hc : hasInstrs P (fnAddr + 0x1d4#64)
      (cbcDecHwLoopInstrs fnAddr memcpyAddr hwDecryptPar17Addr hwDecryptAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hDecPar17 : subroutine_ok P hwDecryptPar17Addr decryptPar17InplaceBytesSpec)
    (hDec1 : subroutine_ok P hwDecryptAddr decrypt15InplaceSpec)
    {key iv ct : List (BitVec 8)} {F : SepProp} {s0 : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hkey : key.length = 32) (hiv : iv.length = 16)
    (hct_pos : 0 < ct.length) (hct_mod : ct.length % 16 = 0) (hct_lt : ct.length < 2 ^ 40)
    (hpc : s0.pc = fnAddr + 0x1d4#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (hsp_align : sp &&& 15#64 = 0#64)
    (hx9 : s0.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (ct.length / 16))
    (hx24 : s0.readReg64 (.gpr 24#5) = sp + 0x4b0#64)
    (hx25 : s0.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ct.length)
    (hnext : ∀ sf : State,
      sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      PureStepPreserved s0 sf →
      sf.readReg64 (.gpr 26#5) = BitVec.ofNat 64 (ct.length / 16) →
      sf.readReg64 (.gpr 23#5) = BitVec.ofNat 64 ct.length →
      SepWP P target_pc sf
        (((outBuf ↦ₛ
             (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 key))
               (bytesToBlock iv) (chunks16 ct)).flatMap blockToBytesLE) ∗
          (inA ↦ₛ ct) ∗
          ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
          ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
          ((sp + 0x028#64) ↦₆₄ outBuf) ∗
          ((sp + 0x030#64) ↦₆₄ inA) ∗
          memRegion (sp + 0x0e0#64) 8 ∗
          memRegion (sp + 0x4b0#64) 0x110 ∗
          memRegion (sp + 0x870#64) 0x110 ∗
          memRegion (sp + 0xa50#64) 0x10 ∗
          roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
          memRegion (sp + 0xf00#64) 16 ∗
          stackAt sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s0
      ((((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
        ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp + 0x028#64) ↦₆₄ outBuf) ∗
        ((sp + 0x030#64) ↦₆₄ inA) ∗
        memRegion (sp + 0x0e0#64) 8 ∗
        memRegion (sp + 0x4b0#64) 0x110 ∗
        memRegion (sp + 0x870#64) 0x110 ∗
        memRegion (sp + 0xa50#64) 0x10 ∗
        roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
        ((sp + 0xf00#64) ↦ₛ iv) ∗
        (inA ↦ₛ ct) ∗
        memRegion outBuf ct.length ∗
        stackAt sp allocHookStack) ∗ F) post oom := by
  have ⟨hSetup, csPar17, csRem⟩ := split_cbcDecHwLoopInstrs hc
  have hspAl : (sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp_align
  have hdiv272 : (ct.length / 16) / 17 = ct.length / 272 := by omega
  refine sepWP_eq (sepWP_mem64_elim (p := sp + 0x0e0#64) (Rest :=
      ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
      ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
      ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
      memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
      memRegion (sp + 0xa50#64) 0x10 ∗
      roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
      ((sp + 0xf00#64) ↦ₛ iv) ∗ (inA ↦ₛ ct) ∗ memRegion outBuf ct.length ∗
      stackAt sp allocHookStack ∗ F) fun oldE0 => ?_) (by sep_ac_rfl)
  have_instrs hSetup 0 11
  wp_steps 6
  have hx21_val := umulh_magic272_lsr8 (n := ct.length) (by omega)
  simp only [wp_norm, arm64_norm] at hx21_val
  have hx8_val :
      BitVec.ofNat 64 (ct.length / 272) + (BitVec.ofNat 64 (ct.length / 272) <<< 4) =
      BitVec.ofNat 64 (17 * (ct.length / 272)) := add_lsl4_ofNat _
  have hx20_val :
      BitVec.ofNat 64 (ct.length / 16) - BitVec.ofNat 64 (17 * (ct.length / 272)) =
      BitVec.ofNat 64 ((ct.length / 16) % 17) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length / 16 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 17 * (ct.length / 272) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : (ct.length / 16) % 17 < 2 ^ 64)]; omega
    · rw [BitVec.le_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length / 16 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 17 * (ct.length / 272) < 2 ^ 64)]; omega
  wp_str64 hf_6 m1 hm1
  wp_step; wp_if hlo_sub
  · exfalso
    have hlt : (BitVec.ofNat 64 (ct.length / 16)).toNat <
        (BitVec.ofNat 64 (17 * (ct.length / 272))).toNat := by
      simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, BitVec.ult] using hlo_sub
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length / 16 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 17 * (ct.length / 272) < 2 ^ 64)] at hlt
    omega
  · wp_steps 3
    -- Shared continuation after step_cbcDec_hwRem reaches fnAddr + 0xd20#64
    have hpost_rem : ∀ (sRem sf : State),
        sRem.readReg64 .x29 = s0.readReg64 .x29 →
        calleeSavedVRegs sRem = calleeSavedVRegs s0 →
        PureStepPreserved s0 sRem →
        sf.pc = fnAddr + 0xd20#64 → sf.status = .Running → sf.sp = sp →
        sf.readReg64 .x26 = BitVec.ofNat 64 (ct.length / 16) →
        sf.readReg64 .x23 = BitVec.ofNat 64 ct.length →
        sf.readReg64 .x29 = sRem.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs sRem →
        PureStepPreserved sRem sf →
        SepWP P target_pc sf
          ((outBuf ↦ₛ cbcPrefixBytes key iv ct (ct.length / 16)) ∗ (inA ↦ₛ ct) ∗
           ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
           ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
           ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
           ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗
           memRegion (sp + 0xa50#64) 0x10 ∗
           roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
           ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (ct.length / 16)) ∗
           (memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
            stackAt sp allocHookStack ∗ F)) post oom := by
      intro sRem sf hx29_r hv_r hpure_r hpc_f hrun_f hsp_f hx26_f hx23_f hx29_f hv_f hpure_f
      have hme0 : ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ⊢
          memRegion (sp + 0x0e0#64) 8 := by
        rw [pointsTo64_eq_pointsToBytes]
        have h := pointsToBytes_entails_memRegion (sp + 0x0e0#64)
          (unpack64 (BitVec.ofNat 64 (17 * (ct.length / 272))))
        rwa [show (unpack64 _).length = 8 by simp [unpack64]] at h
      have hmf00 : ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (ct.length / 16)) ⊢
          memRegion (sp + 0xf00#64) 16 := by
        have h := pointsToBytes_entails_memRegion (sp + 0xf00#64) (cbcChainAt iv ct (ct.length / 16))
        rwa [cbcChainAt_length hiv (by omega)] at h
      rw [cbcPrefixBytes_full]
      refine sepWP_weaken_pre (by
          refine Entails.trans (Entails.of_eq (show _ =
              (((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗
               ((sp + 0xf00#64) ↦ₛ cbcChainAt iv ct (ct.length / 16))) ∗
              ((outBuf ↦ₛ (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 key))
                 (bytesToBlock iv) (chunks16 ct)).flatMap blockToBytesLE) ∗
               (inA ↦ₛ ct) ∗ ((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
               ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
               ((sp + 0x028#64) ↦₆₄ outBuf) ∗ ((sp + 0x030#64) ↦₆₄ inA) ∗
               memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
               memRegion (sp + 0xa50#64) 0x10 ∗
               roundKeys15At (sp + 0xc30#64) (armv8InvExpandedKeys (armv8ExpandKey key)) ∗
               stackAt sp allocHookStack ∗ F) by sep_ac_rfl)) ?_
          refine Entails.trans (sepConj_mono_left (sepConj_mono hme0 hmf00)) ?_
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext sf hpc_f hrun_f hsp_f (hx29_f.trans hx29_r) (hv_f.trans hv_r)
          (hpure_r.trans hpure_f) hx26_f hx23_f)
    wp_if hlt272
    · -- Case 1: ct.length < 272 (q17 = 0), jump directly to fnAddr + 0x490#64
      have hq0 : ct.length / 272 = 0 := by
        have hlt : (BitVec.ofNat 64 ct.length).toNat < (0x110#64).toNat := by
          simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hx25, BitVec.ult] using hlt272
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length < 2 ^ 64)] at hlt
        have h272 : (0x110#64 : BitVec 64).toNat = 272 := rfl; omega
      have hout0 : memRegion outBuf ct.length =
          (outBuf ↦ₛ cbcPrefixBytes key iv ct (17 * (ct.length / 272))) ∗
          memRegion (outBuf + BitVec.ofNat 64 (272 * (ct.length / 272)))
            (ct.length - 272 * (ct.length / 272)) := by simp [hq0, cbcPrefixBytes_zero]
      refine sepWP_eq (step_cbcDec_hwRem csRem hDec1 key iv ct
        (memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
         stackAt sp allocHookStack ∗ F)
        hkey hiv hct_mod hct_lt _
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp]) hspAl
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24])
        fun sf hpc_f hrun_f hsp_f hx26_f hx23_f hx29_f hv_f hpure_f => ?_)
        (by rw [hout0, hq0]; dsimp [cbcChainAt]; sep_ac_rfl)
      exact hpost_rem _ sf (by simp [wp_norm, arm64_norm])
        (by simp [calleeSavedVRegs, wp_norm, arm64_norm])
        (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hm1]))
        hpc_f hrun_f hsp_f hx26_f hx23_f hx29_f hv_f hpure_f
    · -- Case 2: 272 ≤ ct.length (0 < q17), run step_par17_loop then step_cbcDec_hwRem
      have hq_pos : 0 < ct.length / 272 := by
        have hge : ¬ (BitVec.ofNat 64 ct.length).toNat < (0x110#64).toNat := by
          simpa [beq_iff_eq, bne_iff_ne, Classical.not_not, wp_norm, arm64_norm, hx25, BitVec.ult] using hlt272
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ct.length < 2 ^ 64)] at hge
        have h272 : (0x110#64 : BitVec 64).toNat = 272 := rfl; omega
      refine sepWP_eq (step_par17_loop csPar17 hMemcpy hDecPar17 key iv ct
        (((sp + 0x010#64) ↦₆₄ BitVec.ofNat 64 (ct.length / 16)) ∗
         ((sp + 0x018#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
         ((sp + 0x0e0#64) ↦₆₄ BitVec.ofNat 64 (17 * (ct.length / 272))) ∗
         memRegion (sp + 0xa50#64) 0x10 ∗ stackAt sp allocHookStack ∗ F)
        hq_pos hkey hiv hct_lt _
        (by simp [wp_norm, arm64_norm]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hsp]) hspAl
        (by simp [wp_norm, arm64_norm]; try simp [hsp])
        (by simp [wp_norm, arm64_norm])
        fun sPar hpc_p hrun_p hsp_p hx20_p hx24_p hx29_p hv_p hpure_p => ?_)
        (by sep_ac_rfl)
      refine sepWP_eq (step_cbcDec_hwRem csRem hDec1 key iv ct
        (memRegion (sp + 0x4b0#64) 0x110 ∗ memRegion (sp + 0x870#64) 0x110 ∗
         stackAt sp allocHookStack ∗ F)
        hkey hiv hct_mod hct_lt sPar hpc_p hrun_p hsp_p hspAl
        (hx20_p.trans (by simp [wp_norm, arm64_norm]))
        (hx24_p.trans (by simp [wp_norm, arm64_norm, hx24]))
        (hpost_rem sPar · (hx29_p.trans (by simp [wp_norm, arm64_norm]))
          (hv_p.trans (by simp [calleeSavedVRegs, wp_norm, arm64_norm]))
          ((PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hm1])).trans hpure_p)))
        (by sep_ac_rfl)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoops
