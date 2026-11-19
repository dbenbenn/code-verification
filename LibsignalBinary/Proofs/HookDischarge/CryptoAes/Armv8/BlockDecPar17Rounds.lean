/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Lemmas
import ProofLib.SepLogic
import ProofLib.SepLogic.Solver
import ProofLib.SepLogic.WP

/-!
# Instruction Words, Code Segments & Rounds `0..11` for `decrypt_par::<15, U17>`

Contains the 503-instruction word decomposition of `aes::armv8::encdec::decrypt_par::<15, U17>`,
`Par17CodeSegs` splitting, reusable 34-instruction single-round step lemmas (`step_round_v26`,
`step_round_v25`, `step_round_v27`), `step_head` (initial 17-block load + round 0), and
`step_rounds_1_to_11` (advancing to `+0x6a0` with `rounds12` in SIMD registers and `dk[14]` in `q27`).
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (evalAesOp_aesimc_vd_irrel roundKeys15At blocks17At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (decRound decRound_machine Par17Regs simdCalleeProj Par17Anchor
   regs_writeVReg128 regs_setPC
   sp_writeVReg128 sp_setPC
   status_writeVReg128 status_setPC
   vreg_setPC vreg_write_same vreg_write_ne
   readReg64_writeVReg128 readReg64_setPC
   step_ldr128 step_ldp128)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
  (pureStepProj_writeVReg128 pureStepProj_setPC
   mem_writeVReg128_eq mem_setPC_eq)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

public section

/-! ## 1. Exact 503-Instruction Word Lists & Code-Segment Splitting -/

@[expose] def par17HeadWords : List (BitVec 32) :=
  [0xad40641a#32, 0x3dc04025#32, 0xad400422#32, 0xad416020#32, 0xad425037#32, 0x4e285b45#32,
   0x4e2878a5#32, 0xad435835#32, 0xad444833#32, 0x4e285b42#32, 0x4e287842#32, 0xad454031#32,
   0xad461827#32, 0x4e285b41#32, 0x4e287821#32, 0xad471023#32, 0x4e285b40#32, 0x4e287800#32,
   0x4e285b58#32, 0x4e287b18#32, 0x4e285b57#32, 0x4e287af7#32, 0x4e285b54#32, 0x4e287a94#32,
   0x4e285b55#32, 0x4e287ab5#32, 0x4e285b56#32, 0x4e287ad6#32, 0x4e285b53#32, 0x4e287a73#32,
   0x4e285b52#32, 0x4e287a52#32, 0x4e285b51#32, 0x4e287a31#32, 0x4e285b50#32, 0x4e287a10#32,
   0x4e285b47#32, 0x4e2878e7#32, 0x4e285b46#32, 0x4e2878c6#32, 0x4e285b43#32, 0x4e287863#32,
   0x4e285b44#32, 0x4e287884#32]

@[expose] def par17RoundV26Words : List (BitVec 32) :=
  [0x4e285b42#32, 0x4e287842#32, 0x4e285b41#32, 0x4e287821#32, 0x4e285b40#32, 0x4e287800#32,
   0x4e285b58#32, 0x4e287b18#32, 0x4e285b57#32, 0x4e287af7#32, 0x4e285b54#32, 0x4e287a94#32,
   0x4e285b55#32, 0x4e287ab5#32, 0x4e285b56#32, 0x4e287ad6#32, 0x4e285b53#32, 0x4e287a73#32,
   0x4e285b52#32, 0x4e287a52#32, 0x4e285b51#32, 0x4e287a31#32, 0x4e285b50#32, 0x4e287a10#32,
   0x4e285b47#32, 0x4e2878e7#32, 0x4e285b46#32, 0x4e2878c6#32, 0x4e285b43#32, 0x4e287863#32,
   0x4e285b44#32, 0x4e287884#32, 0x4e285b45#32, 0x4e2878a5#32]

@[expose] def par17RoundV25Words : List (BitVec 32) :=
  [0x4e285b22#32, 0x4e287842#32, 0x4e285b21#32, 0x4e287821#32, 0x4e285b20#32, 0x4e287800#32,
   0x4e285b38#32, 0x4e287b18#32, 0x4e285b37#32, 0x4e287af7#32, 0x4e285b34#32, 0x4e287a94#32,
   0x4e285b35#32, 0x4e287ab5#32, 0x4e285b36#32, 0x4e287ad6#32, 0x4e285b33#32, 0x4e287a73#32,
   0x4e285b32#32, 0x4e287a52#32, 0x4e285b31#32, 0x4e287a31#32, 0x4e285b30#32, 0x4e287a10#32,
   0x4e285b27#32, 0x4e2878e7#32, 0x4e285b26#32, 0x4e2878c6#32, 0x4e285b23#32, 0x4e287863#32,
   0x4e285b24#32, 0x4e287884#32, 0x4e285b25#32, 0x4e2878a5#32]

@[expose] def par17RoundV27Words : List (BitVec 32) :=
  [0x4e285b62#32, 0x4e287842#32, 0x4e285b61#32, 0x4e287821#32, 0x4e285b60#32, 0x4e287800#32,
   0x4e285b78#32, 0x4e287b18#32, 0x4e285b77#32, 0x4e287af7#32, 0x4e285b74#32, 0x4e287a94#32,
   0x4e285b75#32, 0x4e287ab5#32, 0x4e285b76#32, 0x4e287ad6#32, 0x4e285b73#32, 0x4e287a73#32,
   0x4e285b72#32, 0x4e287a52#32, 0x4e285b71#32, 0x4e287a31#32, 0x4e285b70#32, 0x4e287a10#32,
   0x4e285b67#32, 0x4e2878e7#32, 0x4e285b66#32, 0x4e2878c6#32, 0x4e285b63#32, 0x4e287863#32,
   0x4e285b64#32, 0x4e287884#32, 0x4e285b65#32, 0x4e2878a5#32]

@[expose] def par17TailWordsA : List (BitVec 32) :=
  [0xad466819#32, 0x4e285b22#32, 0x4e287842#32, 0x4e285b21#32, 0x4e287821#32, 0x4e285b20#32,
   0x4e287800#32, 0x4e285b38#32, 0x4e287b18#32, 0x4e285b35#32, 0x4e287ab5#32, 0x4e285b42#32,
   0x4e285b36#32, 0x4e287ad6#32, 0x4e285b41#32, 0x4e285b40#32, 0x4e285b58#32, 0x4e285b37#32,
   0x4e287af7#32, 0x6e221f62#32, 0x4e285b34#32, 0x4e287a94#32, 0x6e211f61#32, 0x4e285b33#32,
   0x4e287a73#32, 0x4e285b32#32, 0x4e287a52#32, 0x6e201f60#32, 0x4e285b55#32, 0x4e285b56#32,
   0x4e285b31#32, 0x4e287a31#32, 0xad000442#32, 0x6e381f61#32, 0x4e285b30#32, 0x4e287a10#32,
   0x4e285b57#32, 0x4e285b54#32, 0x4e285b27#32, 0x4e2878e7#32, 0xad010440#32]

@[expose] def par17TailWordsB : List (BitVec 32) :=
  [0x6e351f60#32, 0x4e285b26#32, 0x4e2878c6#32, 0x6e361f61#32, 0x4e285b53#32, 0x4e285b52#32,
   0x6e371f62#32, 0x6e341f74#32, 0x4e285b23#32, 0x4e287863#32, 0x4e285b51#32, 0xad030440#32,
   0x4e285b24#32, 0x4e287884#32, 0xad025042#32, 0x6e331f60#32, 0x4e285b50#32, 0x6e321f61#32,
   0x4e285b47#32, 0x4e285b25#32, 0x4e2878a5#32, 0x4e285b46#32, 0x6e311f62#32, 0x6e301f70#32,
   0x4e285b43#32, 0x4e285b44#32, 0xad040440#32, 0x6e271f60#32, 0x6e261f61#32, 0x4e285b45#32,
   0xad054042#32, 0x6e231f62#32, 0x6e241f63#32, 0xad060440#32, 0x6e251f60#32, 0xad070c42#32,
   0x3d804040#32, 0xd65f03c0#32]

/-- Complete 503-word encoding of `aes::armv8::encdec::decrypt_par::<15, U17>`. -/
@[expose] def decryptPar17Words : List (BitVec 32) :=
  par17HeadWords ++ par17RoundV25Words ++
  [0xad41641a#32] ++ par17RoundV26Words ++ par17RoundV25Words ++
  [0xad42641a#32] ++ par17RoundV26Words ++ par17RoundV25Words ++
  [0xad43641a#32] ++ par17RoundV26Words ++ par17RoundV25Words ++
  [0xad44641a#32] ++ par17RoundV26Words ++
  [0xad45681b#32] ++ par17RoundV25Words ++ par17RoundV27Words ++
  [0x3dc0381b#32] ++ par17RoundV26Words ++
  par17TailWordsA ++ par17TailWordsB

theorem decryptPar17Words_length : decryptPar17Words.length = 503 := by
  have h0 : par17HeadWords.length = 44 := rfl
  have h1 : par17RoundV26Words.length = 34 := rfl
  have h2 : par17RoundV25Words.length = 34 := rfl
  have h3 : par17RoundV27Words.length = 34 := rfl
  have h4 : par17TailWordsA.length = 41 := rfl
  have h5 : par17TailWordsB.length = 38 := rfl
  simp only [decryptPar17Words, List.length_append, List.length_singleton, h0, h1, h2, h3, h4, h5]

private theorem split_words {P : Program} {fnAddr off1 : BitVec 64} (off2 : BitVec 64)
    {xs ys : List (BitVec 32)} (h : hasInstrs P (fnAddr + off1) (decodeWords (xs ++ ys)))
    (hoff : off1 + BitVec.ofNat 64 (4 * (decodeWords xs).length) = off2) :
    hasInstrs P (fnAddr + off1) (decodeWords xs) ∧ hasInstrs P (fnAddr + off2) (decodeWords ys) := by
  rw [decodeWords, List.map_append] at h
  obtain ⟨h1, h2⟩ := h.split_append (off := BitVec.ofNat 64 (4 * (decodeWords xs).length)) rfl
  exact ⟨h1, (show fnAddr + off1 + BitVec.ofNat 64 (4 * (decodeWords xs).length) = fnAddr + off2 by
    rw [BitVec.add_assoc, hoff]) ▸ h2⟩

structure Par17CodeSegs (P : Program) (fnAddr : BitVec 64) : Prop where
  head   : hasInstrs P fnAddr (decodeWords par17HeadWords)
  r1     : hasInstrs P (fnAddr + 0x0b0#64) (decodeWords par17RoundV25Words)
  ld23   : P.fetch (fnAddr + 0x138#64) = some (.ldpSimd .Q128 26#5 25#5 (.Offset (.gpr 0#5) 0x20#64))
  r2     : hasInstrs P (fnAddr + 0x13c#64) (decodeWords par17RoundV26Words)
  r3     : hasInstrs P (fnAddr + 0x1c4#64) (decodeWords par17RoundV25Words)
  ld45   : P.fetch (fnAddr + 0x24c#64) = some (.ldpSimd .Q128 26#5 25#5 (.Offset (.gpr 0#5) 0x40#64))
  r4     : hasInstrs P (fnAddr + 0x250#64) (decodeWords par17RoundV26Words)
  r5     : hasInstrs P (fnAddr + 0x2d8#64) (decodeWords par17RoundV25Words)
  ld67   : P.fetch (fnAddr + 0x360#64) = some (.ldpSimd .Q128 26#5 25#5 (.Offset (.gpr 0#5) 0x60#64))
  r6     : hasInstrs P (fnAddr + 0x364#64) (decodeWords par17RoundV26Words)
  r7     : hasInstrs P (fnAddr + 0x3ec#64) (decodeWords par17RoundV25Words)
  ld89   : P.fetch (fnAddr + 0x474#64) = some (.ldpSimd .Q128 26#5 25#5 (.Offset (.gpr 0#5) 0x80#64))
  r8     : hasInstrs P (fnAddr + 0x478#64) (decodeWords par17RoundV26Words)
  ld1011 : P.fetch (fnAddr + 0x500#64) = some (.ldpSimd .Q128 27#5 26#5 (.Offset (.gpr 0#5) 0xa0#64))
  r9     : hasInstrs P (fnAddr + 0x504#64) (decodeWords par17RoundV25Words)
  r10    : hasInstrs P (fnAddr + 0x58c#64) (decodeWords par17RoundV27Words)
  ld14   : P.fetch (fnAddr + 0x614#64) = some (.ldrSimd .Q128 27#5 (.Offset (.gpr 0#5) 0xe0#64))
  r11    : hasInstrs P (fnAddr + 0x618#64) (decodeWords par17RoundV26Words)
  tailA  : hasInstrs P (fnAddr + 0x6a0#64) (decodeWords par17TailWordsA)
  tailB  : hasInstrs P (fnAddr + 0x744#64) (decodeWords par17TailWordsB)

theorem Par17CodeSegs.of_hasInstrs {P : Program} {fnAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (decodeWords decryptPar17Words)) : Par17CodeSegs P fnAddr := by
  dsimp only [decryptPar17Words] at hc; simp only [List.append_assoc] at hc
  have hc0 : hasInstrs P (fnAddr + 0#64) _ := (BitVec.add_zero fnAddr).symm ▸ hc
  obtain ⟨s0, hc⟩ := split_words 0x0b0#64 hc0 rfl
  obtain ⟨s1, hc⟩ := split_words 0x138#64 hc rfl
  obtain ⟨s2, hc⟩ := split_words 0x13c#64 hc rfl
  obtain ⟨s3, hc⟩ := split_words 0x1c4#64 hc rfl
  obtain ⟨s4, hc⟩ := split_words 0x24c#64 hc rfl
  obtain ⟨s5, hc⟩ := split_words 0x250#64 hc rfl
  obtain ⟨s6, hc⟩ := split_words 0x2d8#64 hc rfl
  obtain ⟨s7, hc⟩ := split_words 0x360#64 hc rfl
  obtain ⟨s8, hc⟩ := split_words 0x364#64 hc rfl
  obtain ⟨s9, hc⟩ := split_words 0x3ec#64 hc rfl
  obtain ⟨s10, hc⟩ := split_words 0x474#64 hc rfl
  obtain ⟨s11, hc⟩ := split_words 0x478#64 hc rfl
  obtain ⟨s12, hc⟩ := split_words 0x500#64 hc rfl
  obtain ⟨s13, hc⟩ := split_words 0x504#64 hc rfl
  obtain ⟨s14, hc⟩ := split_words 0x58c#64 hc rfl
  obtain ⟨s15, hc⟩ := split_words 0x614#64 hc rfl
  obtain ⟨s16, hc⟩ := split_words 0x618#64 hc rfl
  obtain ⟨s17, hc⟩ := split_words 0x6a0#64 hc rfl
  obtain ⟨s18, s19⟩ := split_words 0x744#64 hc rfl
  exact ⟨(BitVec.add_zero fnAddr) ▸ s0, s1, s2.fetch_at_zero, s3, s4, s5.fetch_at_zero,
    s6, s7, s8.fetch_at_zero, s9, s10, s11.fetch_at_zero, s12, s13.fetch_at_zero,
    s14, s15, s16.fetch_at_zero, s17, s18, s19⟩

/-! ## 2. Reusable 34-Instruction Round Lemmas & Rounds `0..11` -/

/-- Direct `FEAT_AES` single-instruction step rule (`AESE`, `AESD`, `AESMC`, `AESIMC`). -/
theorem step_aes {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {op : AesOp} {vd vn : BitVec 5} {res : BitVec 128}
    (hfetch : prog.fetch pc = some (.aes op vd vn))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hres : evalAesOp op (s.readVReg128 vd) (s.readVReg128 vn) = res)
    (hnext : SepWP prog target_pc ((s.writeVReg128 vd res).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.aes op vd vn) s =
      (s.writeVReg128 vd res).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, State.advancePC, State.setPC, hpc, hres]
  rw [hstep]
  have hmem : ((s.writeVReg128 vd res).setPC (pc + 4#64)).mem = s.mem := by cases s; rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hm)

private theorem setPC_writeVReg128_setPC_same (s : State) (vd : BitVec 5) (v1 v2 : BitVec 128)
    (p1 p2 : BitVec 64) :
    (((s.writeVReg128 vd v1).setPC p1).writeVReg128 vd v2).setPC p2 =
      (s.writeVReg128 vd v2).setPC p2 := by
  have hcomm : ((s.writeVReg128 vd v1).setPC p1).writeVReg128 vd v2 =
      ((s.writeVReg128 vd v1).writeVReg128 vd v2).setPC p1 := by
    cases s; rfl
  rw [hcomm, State.writeVReg128_writeVReg128_same]
  cases s; rfl

/-- Fused 2-instruction `AESD Vd.16B, Vk.16B; AESIMC Vd.16B, Vd.16B` round step rule. -/
theorem step_aesd_imc {prog : Program} {target_pc pc pc1 : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vd vk : BitVec 5}
    (hf1 : prog.fetch pc = some (.aes .AESD vd vk))
    (hf2 : prog.fetch pc1 = some (.aes .AESIMC vd vd))
    (blk rk : BitVec 128)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hpc1 : pc + 4#64 = pc1)
    (hd : s.readVReg128 vd = blk) (hk : s.readVReg128 vk = rk)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vd (decRound rk blk)).setPC (pc1 + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  refine step_aes hf1 hpc hrun (res := evalAesOp .AESD blk rk) (by rw [hd, hk]) ?_
  refine step_aes hf2 (by simp [State.setPC, hpc1])
    (by simp [State.setPC, State.writeVReg128, hrun])
    (res := decRound rk blk)
    (by simp only [vreg_setPC, vreg_write_same, evalAesOp_aesimc_vd_irrel, decRound_machine]) ?_
  rwa [setPC_writeVReg128_setPC_same]

section
arm64_proof_prelude
attribute [local irreducible] decRound State.readVReg128 State.writeVReg128 State.setPC

local macro "wp_aesd_imc " hf1:term:max hf2:term:max blk:term:max rk:term:max : tactic => `(tactic|
  refine step_aesd_imc $hf1 $hf2 $blk $rk
    (by first | assumption | (rw [State.pc_setPC]; try rw [BitVec.add_assoc]; rfl))
    (by first | assumption | (simp only [status_setPC, status_writeVReg128]; assumption))
    (by first | rfl | (rw [BitVec.add_assoc]; rfl))
    (by first | assumption | (simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]; try assumption))
    (by first | assumption | (simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]; try assumption))
    ?_)

private theorem step_round_v26 {P : Program} {rndPc next target_pc : BitVec 64}
    {r : Par17Regs} {rk : BitVec 128} {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P rndPc (decodeWords par17RoundV26Words))
    (hnext_pc : rndPc + 0x88#64 = next)
    (hpc : s.pc = rndPc) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hr : r.holds s) (hk : s.readVReg128 26#5 = rk)
    (hcont : ∀ sf : State, sf.pc = next → sf.status = .Running → Par17Anchor s0 sf →
      (r.step rk).holds sf → sf.readVReg128 25#5 = s.readVReg128 25#5 →
      sf.readVReg128 26#5 = rk → sf.readVReg128 27#5 = s.readVReg128 27#5 →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  have_instrs hc 0 34
  wp_aesd_imc hf_0 hf_1 r.b0 rk; wp_aesd_imc hf_2 hf_3 r.b1 rk
  wp_aesd_imc hf_4 hf_5 r.b2 rk; wp_aesd_imc hf_6 hf_7 r.b3 rk
  wp_aesd_imc hf_8 hf_9 r.b4 rk; wp_aesd_imc hf_10 hf_11 r.b5 rk
  wp_aesd_imc hf_12 hf_13 r.b6 rk; wp_aesd_imc hf_14 hf_15 r.b7 rk
  wp_aesd_imc hf_16 hf_17 r.b8 rk; wp_aesd_imc hf_18 hf_19 r.b9 rk
  wp_aesd_imc hf_20 hf_21 r.b10 rk; wp_aesd_imc hf_22 hf_23 r.b11 rk
  wp_aesd_imc hf_24 hf_25 r.b12 rk; wp_aesd_imc hf_26 hf_27 r.b13 rk
  wp_aesd_imc hf_28 hf_29 r.b14 rk; wp_aesd_imc hf_30 hf_31 r.b15 rk
  wp_aesd_imc hf_32 hf_33 r.b16 rk
  refine hcont _
    (by rw [← hnext_pc, State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC])
      (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_ ?_ ?_ ?_
  · dsimp only [Par17Regs.holds, Par17Regs.step, Par17Regs.map]
    simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128,
      ↓reduceIte, and_self]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte, hk]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]

private theorem step_round_v25 {P : Program} {rndPc next target_pc : BitVec 64}
    {r : Par17Regs} {rk : BitVec 128} {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P rndPc (decodeWords par17RoundV25Words))
    (hnext_pc : rndPc + 0x88#64 = next)
    (hpc : s.pc = rndPc) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hr : r.holds s) (hk : s.readVReg128 25#5 = rk)
    (hcont : ∀ sf : State, sf.pc = next → sf.status = .Running → Par17Anchor s0 sf →
      (r.step rk).holds sf → sf.readVReg128 25#5 = rk →
      sf.readVReg128 26#5 = s.readVReg128 26#5 → sf.readVReg128 27#5 = s.readVReg128 27#5 →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  have_instrs hc 0 34
  wp_aesd_imc hf_0 hf_1 r.b0 rk; wp_aesd_imc hf_2 hf_3 r.b1 rk
  wp_aesd_imc hf_4 hf_5 r.b2 rk; wp_aesd_imc hf_6 hf_7 r.b3 rk
  wp_aesd_imc hf_8 hf_9 r.b4 rk; wp_aesd_imc hf_10 hf_11 r.b5 rk
  wp_aesd_imc hf_12 hf_13 r.b6 rk; wp_aesd_imc hf_14 hf_15 r.b7 rk
  wp_aesd_imc hf_16 hf_17 r.b8 rk; wp_aesd_imc hf_18 hf_19 r.b9 rk
  wp_aesd_imc hf_20 hf_21 r.b10 rk; wp_aesd_imc hf_22 hf_23 r.b11 rk
  wp_aesd_imc hf_24 hf_25 r.b12 rk; wp_aesd_imc hf_26 hf_27 r.b13 rk
  wp_aesd_imc hf_28 hf_29 r.b14 rk; wp_aesd_imc hf_30 hf_31 r.b15 rk
  wp_aesd_imc hf_32 hf_33 r.b16 rk
  refine hcont _
    (by rw [← hnext_pc, State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC])
      (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_ ?_ ?_ ?_
  · dsimp only [Par17Regs.holds, Par17Regs.step, Par17Regs.map]
    simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128,
      ↓reduceIte, and_self]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte, hk]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]

private theorem step_round_v27 {P : Program} {rndPc next target_pc : BitVec 64}
    {r : Par17Regs} {rk : BitVec 128} {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P rndPc (decodeWords par17RoundV27Words))
    (hnext_pc : rndPc + 0x88#64 = next)
    (hpc : s.pc = rndPc) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hr : r.holds s) (hk : s.readVReg128 27#5 = rk)
    (hcont : ∀ sf : State, sf.pc = next → sf.status = .Running → Par17Anchor s0 sf →
      (r.step rk).holds sf → sf.readVReg128 26#5 = s.readVReg128 26#5 →
      SepWP P target_pc sf Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  have_instrs hc 0 34
  wp_aesd_imc hf_0 hf_1 r.b0 rk; wp_aesd_imc hf_2 hf_3 r.b1 rk
  wp_aesd_imc hf_4 hf_5 r.b2 rk; wp_aesd_imc hf_6 hf_7 r.b3 rk
  wp_aesd_imc hf_8 hf_9 r.b4 rk; wp_aesd_imc hf_10 hf_11 r.b5 rk
  wp_aesd_imc hf_12 hf_13 r.b6 rk; wp_aesd_imc hf_14 hf_15 r.b7 rk
  wp_aesd_imc hf_16 hf_17 r.b8 rk; wp_aesd_imc hf_18 hf_19 r.b9 rk
  wp_aesd_imc hf_20 hf_21 r.b10 rk; wp_aesd_imc hf_22 hf_23 r.b11 rk
  wp_aesd_imc hf_24 hf_25 r.b12 rk; wp_aesd_imc hf_26 hf_27 r.b13 rk
  wp_aesd_imc hf_28 hf_29 r.b14 rk; wp_aesd_imc hf_30 hf_31 r.b15 rk
  wp_aesd_imc hf_32 hf_33 r.b16 rk
  refine hcont _
    (by rw [← hnext_pc, State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC])
      (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_ ?_
  · dsimp only [Par17Regs.holds, Par17Regs.step, Par17Regs.map]
    simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128,
      ↓reduceIte, and_self]
  · simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte]

private theorem step_head_tail {P : Program} {fnAddr target_pc : BitVec 64}
    {r : Par17Regs} {rk0 rk1 : BitVec 128} {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P fnAddr (decodeWords par17HeadWords))
    (hpc : s.pc = fnAddr + 0x40#64) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hr : r.holds s) (hk0 : s.readVReg128 26#5 = rk0) (hk1 : s.readVReg128 25#5 = rk1)
    (hcont : ∀ s1 : State, s1.pc = fnAddr + 0x0b0#64 → s1.status = .Running →
      Par17Anchor s0 s1 →
      (Par17Regs.mk r.b0 r.b1
        (decRound rk0 r.b2) (decRound rk0 r.b3) (decRound rk0 r.b4) (decRound rk0 r.b5)
        (decRound rk0 r.b6) (decRound rk0 r.b7) (decRound rk0 r.b8) (decRound rk0 r.b9)
        (decRound rk0 r.b10) (decRound rk0 r.b11) (decRound rk0 r.b12) (decRound rk0 r.b13)
        (decRound rk0 r.b14) (decRound rk0 r.b15) r.b16).holds s1 →
      s1.readVReg128 25#5 = rk1 → SepWP P target_pc s1 Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  have_instrs hc 16 28
  wp_aesd_imc hf_16 hf_17 r.b2 rk0; wp_aesd_imc hf_18 hf_19 r.b3 rk0
  wp_aesd_imc hf_20 hf_21 r.b4 rk0; wp_aesd_imc hf_22 hf_23 r.b5 rk0
  wp_aesd_imc hf_24 hf_25 r.b6 rk0; wp_aesd_imc hf_26 hf_27 r.b7 rk0
  wp_aesd_imc hf_28 hf_29 r.b8 rk0; wp_aesd_imc hf_30 hf_31 r.b9 rk0
  wp_aesd_imc hf_32 hf_33 r.b10 rk0; wp_aesd_imc hf_34 hf_35 r.b11 rk0
  wp_aesd_imc hf_36 hf_37 r.b12 rk0; wp_aesd_imc hf_38 hf_39 r.b13 rk0
  wp_aesd_imc hf_40 hf_41 r.b14 rk0; wp_aesd_imc hf_42 hf_43 r.b15 rk0
  refine hcont _ (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC]) (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq])) ?_
    (by simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte, hk1])
  dsimp only [Par17Regs.holds]
  simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128,
    ↓reduceIte, b0, b1, b16, and_self]

set_option maxHeartbeats 400000 in
theorem step_head {P : Program} {fnAddr dkPtr bufPtr target_pc : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blks : Vector (BitVec 128) 17} {s0 : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P fnAddr (decodeWords par17HeadWords))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dkPtr) (hx1 : s0.readReg64 .x1 = bufPtr)
    (hcont : ∀ s1 : State, s1.pc = fnAddr + 0x0b0#64 → s1.status = .Running →
      Par17Anchor s0 s1 → ((Par17Regs.ofVector blks).step dk[0]).holds s1 →
      s1.readVReg128 25#5 = dk[1] →
      SepWP P target_pc s1 (roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks) post oom) :
    SepWP P target_pc s0 (roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks) post oom := by
  have_instrs hc 0 16
  have hx0' : s0.readReg64 (.gpr 0#5) = dkPtr := hx0
  have hx1' : s0.readReg64 (.gpr 1#5) = bufPtr := hx1
  refine step_ldp128 (ea := dkPtr) hf_0 hpc hrun (by simp only [hx0', BitVec.add_zero])
    (v1 := dk[0]) (v2 := dk[1]) (by dsimp only [roundKeys15At]; sep_focus) ?_
  refine step_ldr128 (ea := bufPtr + 0x100#64) hf_1 (State.pc_setPC _ _)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v := blks[16]) (by dsimp only [blocks17At]; sep_focus) ?_
  refine step_ldp128 (ea := bufPtr) hf_2 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, BitVec.add_zero, hx1'])
    (v1 := blks[0]) (v2 := blks[1]) (by dsimp only [blocks17At]; sep_focus) ?_
  refine step_ldp128 (ea := bufPtr + 0x20#64) hf_3 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[2]) (v2 := blks[3])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  refine step_ldp128 (ea := bufPtr + 0x40#64) hf_4 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[4]) (v2 := blks[5])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  wp_aesd_imc hf_5 hf_6 blks[16] dk[0]
  refine step_ldp128 (ea := bufPtr + 0x60#64) hf_7 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[6]) (v2 := blks[7])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  refine step_ldp128 (ea := bufPtr + 0x80#64) hf_8 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[8]) (v2 := blks[9])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  wp_aesd_imc hf_9 hf_10 blks[0] dk[0]
  refine step_ldp128 (ea := bufPtr + 0xa0#64) hf_11 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[10]) (v2 := blks[11])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  refine step_ldp128 (ea := bufPtr + 0xc0#64) hf_12 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[12]) (v2 := blks[13])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  wp_aesd_imc hf_13 hf_14 blks[1] dk[0]
  refine step_ldp128 (ea := bufPtr + 0xe0#64) hf_15 (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (by simp only [readReg64_setPC, readReg64_writeVReg128, hx1'])
    (v1 := blks[14]) (v2 := blks[15])
    (by dsimp only [blocks17At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  refine step_head_tail hc (r := ⟨decRound dk[0] blks[0], decRound dk[0] blks[1],
      blks[2], blks[3], blks[4], blks[5], blks[6], blks[7], blks[8], blks[9],
      blks[10], blks[11], blks[12], blks[13], blks[14], blks[15], decRound dk[0] blks[16]⟩)
    (rk0 := dk[0]) (rk1 := dk[1])
    (by rw [State.pc_setPC, BitVec.add_assoc]; rfl)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    ((Par17Anchor.refl s0).step (by simp only [regs_writeVReg128, regs_setPC])
      (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_
    (by simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte])
    (by simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte])
    hcont
  dsimp only [Par17Regs.holds]
  simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte, and_self]

private theorem step_key_ldp {P : Program} {pc next dkPtr off target_pc : BitVec 64}
    {vt1 vt2 : BitVec 5} {k1 k2 : BitVec 128} {dk : Vector (BitVec 128) 15} {F F' : SepProp}
    {r : Par17Regs} {s0 s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P.fetch pc = some (.ldpSimd .Q128 vt1 vt2 (.Offset (.gpr 0#5) off)))
    (hnext_pc : pc + 4#64 = next)
    (hvt1 : vt1 = 26#5 ∨ vt1 = 27#5) (hvt2 : vt2 = 25#5 ∨ vt2 = 26#5) (hne : vt1 ≠ vt2)
    (hpc : s.pc = pc) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hx0 : s0.readReg64 .x0 = dkPtr) (hr : r.holds s)
    (hload : roundKeys15At dkPtr dk ∗ F = (((dkPtr + off) ↦₁₂₈ k1) ∗ (((dkPtr + off) + 16#64) ↦₁₂₈ k2)) ∗ F')
    (hcont : ∀ sf : State, sf.pc = next → sf.status = .Running → Par17Anchor s0 sf →
      r.holds sf → sf.readVReg128 vt1 = k1 → sf.readVReg128 vt2 = k2 →
      (vt1 ≠ 25#5 → vt2 ≠ 25#5 → sf.readVReg128 25#5 = s.readVReg128 25#5) →
      SepWP P target_pc sf (roundKeys15At dkPtr dk ∗ F) post oom) :
    SepWP P target_pc s (roundKeys15At dkPtr dk ∗ F) post oom := by
  refine step_ldp128 (ea := dkPtr + off) hf hpc hrun (by rw [ha.readReg64 (.gpr 0#5), hx0]) hload ?_
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  refine hcont _ (by rw [State.pc_setPC]; exact hnext_pc)
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC]) (by simp only [sp_writeVReg128, sp_setPC])
      (by rcases hvt1 with rfl | rfl <;> rcases hvt2 with rfl | rfl <;>
            simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
              State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_
    (by rw [vreg_setPC, vreg_write_ne _ _ _ _ hne, vreg_write_same])
    (by rw [vreg_setPC, vreg_write_same])
    (fun h1 h2 => by rw [vreg_setPC, vreg_write_ne _ _ _ _ h2.symm, vreg_write_ne _ _ _ _ h1.symm])
  dsimp only [Par17Regs.holds]
  rcases hvt1 with rfl | rfl <;> rcases hvt2 with rfl | rfl <;>
    simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, and_self]

theorem step_rounds_1_to_11 {P : Program} {fnAddr dkPtr target_pc : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blks : Vector (BitVec 128) 17} {F : SepProp} {s0 s1 : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : Par17CodeSegs P fnAddr) (hx0 : s0.readReg64 .x0 = dkPtr)
    (hpc1 : s1.pc = fnAddr + 0x0b0#64) (hrun1 : s1.status = .Running) (ha1 : Par17Anchor s0 s1)
    (hr1 : ((Par17Regs.ofVector blks).step dk[0]).holds s1) (hk1 : s1.readVReg128 25#5 = dk[1])
    (hcont : ∀ sf : State, sf.pc = fnAddr + 0x6a0#64 → sf.status = .Running →
      Par17Anchor s0 sf → ((Par17Regs.ofVector blks).rounds12 dk).holds sf →
      sf.readVReg128 27#5 = dk[14] →
      SepWP P target_pc sf (roundKeys15At dkPtr dk ∗ F) post oom) :
    SepWP P target_pc s1 (roundKeys15At dkPtr dk ∗ F) post oom := by
  refine step_round_v25 hseg.r1 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc1 hrun1 ha1 hr1 hk1 fun s hpc hrun ha hr _ _ _ => ?_
  refine step_key_ldp hseg.ld23 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    (.inl rfl) (.inl rfl) (by decide) hpc hrun ha hx0 hr (k1 := dk[2]) (k2 := dk[3])
    (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s hpc hrun ha hr hk26 hk25 _ => ?_
  refine step_round_v26 hseg.r2 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr hk26 fun s hpc hrun ha hr hk25' _ _ => ?_
  refine step_round_v25 hseg.r3 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr (hk25'.trans hk25) fun s hpc hrun ha hr _ _ _ => ?_
  refine step_key_ldp hseg.ld45 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    (.inl rfl) (.inl rfl) (by decide) hpc hrun ha hx0 hr (k1 := dk[4]) (k2 := dk[5])
    (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s hpc hrun ha hr hk26 hk25 _ => ?_
  refine step_round_v26 hseg.r4 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr hk26 fun s hpc hrun ha hr hk25' _ _ => ?_
  refine step_round_v25 hseg.r5 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr (hk25'.trans hk25) fun s hpc hrun ha hr _ _ _ => ?_
  refine step_key_ldp hseg.ld67 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    (.inl rfl) (.inl rfl) (by decide) hpc hrun ha hx0 hr (k1 := dk[6]) (k2 := dk[7])
    (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s hpc hrun ha hr hk26 hk25 _ => ?_
  refine step_round_v26 hseg.r6 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr hk26 fun s hpc hrun ha hr hk25' _ _ => ?_
  refine step_round_v25 hseg.r7 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr (hk25'.trans hk25) fun s hpc hrun ha hr _ _ _ => ?_
  refine step_key_ldp hseg.ld89 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    (.inl rfl) (.inl rfl) (by decide) hpc hrun ha hx0 hr (k1 := dk[8]) (k2 := dk[9])
    (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s hpc hrun ha hr hk26 hk25 _ => ?_
  refine step_round_v26 hseg.r8 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr hk26 fun s hpc hrun ha hr hk25' _ _ => ?_
  have hk9 : s.readVReg128 25#5 = dk[9] := hk25'.trans hk25
  refine step_key_ldp hseg.ld1011 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    (.inr rfl) (.inr rfl) (by decide) hpc hrun ha hx0 hr (k1 := dk[10]) (k2 := dk[11])
    (by dsimp only [roundKeys15At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s hpc hrun ha hr hk27 hk26 hkeep25 => ?_
  have hk9' : s.readVReg128 25#5 = dk[9] := (hkeep25 (by decide) (by decide)).trans hk9
  refine step_round_v25 hseg.r9 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr hk9' fun s hpc hrun ha hr _ hk26' hk27' => ?_
  refine step_round_v27 hseg.r10 (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl)
    hpc hrun ha hr (hk27'.trans hk27) fun s hpc hrun ha hr hk26'' => ?_
  have hk11 : s.readVReg128 26#5 = dk[11] := hk26''.trans (hk26'.trans hk26)
  refine step_ldr128 (ea := dkPtr + 0xe0#64) hseg.ld14 hpc hrun (by rw [ha.readReg64 (.gpr 0#5), hx0])
    (v := dk[14]) (by dsimp only [roundKeys15At]; sep_focus) ?_
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  refine step_round_v26 hseg.r11 (by simp only [BitVec.add_assoc, BitVec.reduceAdd])
    (by rw [State.pc_setPC]; simp only [BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [status_writeVReg128, status_setPC, hrun])
    (ha.step (by simp only [regs_writeVReg128, regs_setPC]) (by simp only [sp_writeVReg128, sp_setPC])
      (by simp (config := { decide := true }) only [simdCalleeProj, vreg_setPC,
        State.readVReg128_writeVReg128, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC])
      (by simp only [mem_writeVReg128_eq, mem_setPC_eq]))
    ?_ (by simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte, hk11])
    fun sf hpc_f hrun_f ha_f hr_f _ _ hk27_f =>
      hcont sf hpc_f hrun_f ha_f hr_f (hk27_f.trans (by rw [vreg_setPC, vreg_write_same]))
  dsimp only [Par17Regs.holds]
  simp (config := { decide := true }) only [vreg_setPC, State.readVReg128_writeVReg128, ↓reduceIte,
    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, and_self]

end
end
end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds
