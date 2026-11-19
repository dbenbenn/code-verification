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
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Abi.Aapcs
import ProofLib.Hoare.Hooks
import ProofLib.Hoare.Model
import ProofLib.Lemmas
import ProofLib.SepLogic
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Solver
import ProofLib.SepLogic.WP

/-!
# `aes::armv8::encdec::decrypt_par::<15, U17>` Machine-Code Proof (`503` Insns)

Position-independent (`0` `adrp`/`bl`, `0` branches) verification of the 503-instruction
17-block parallel ARMv8 AES-256 decryption routine (`0x4c86a8..0x4c8e80` in `libsignal-cli`).
Proves in-place decryption (`x0 = dkPtr`, `x1 = bufPtr`, `x2 = bufPtr`) transforming
`roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks` to
`roundKeys15At dkPtr dk ∗ blocks17At bufPtr (armv8DecryptPar17 dk blks)` while preserving
every GPR `x0..x30`, `sp`, `q8..q15` (`d8..d15`), and `PureStepPreserved`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (armv8DecryptPar17 blocks17Bytes roundKeys15At blocks17At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (bytesToBlocks17 blocks17Bytes_length blocks17At_eq_pointsToBytes pointsToBytes_eq_blocks17At
   decRound decFinish decFinish_machine
   Par17Regs simdCalleeProj Par17Anchor
   regs_writeVReg128 regs_setPC regs_setMem
   sp_writeVReg128 sp_setPC sp_setMem
   status_writeVReg128 status_setPC status_setMem
   vreg_setPC vreg_setMem
   readReg64_writeVReg128 readReg64_setPC readReg64_setMem
   step_ldp128 step_str128_perm step_stp128_perm)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds
  (par17TailWordsA par17TailWordsB decryptPar17Words decryptPar17Words_length
   Par17CodeSegs step_aes step_aesd_imc step_head step_rounds_1_to_11)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
  (pureStepProj_writeVReg128 pureStepProj_setPC pureStepProj_setMem
   mem_writeVReg128_eq mem_setPC_eq mem_setMem_eq)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

public section

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Rounds
  (decryptPar17Words decryptPar17Words_length)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (bytesToBlocks17 blocks17Bytes_length blocks17At_eq_pointsToBytes
   pointsToBytes_eq_blocks17At Par17Anchor)

/-! ## 1. Subroutine Specifications -/

/-- In-place 17-block decryption contract (`x0 = dkPtr`, `x1 = bufPtr`, `x2 = bufPtr`). -/
@[expose] def decryptPar17InplaceSpec :
    Spec (BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × Vector (BitVec 128) 17) where
  pre := fun (dkPtr, bufPtr, dk, blks) s0 =>
    ⌜s0.readReg64 .x0 = dkPtr ∧ s0.readReg64 .x1 = bufPtr ∧ s0.readReg64 .x2 = bufPtr⌝ ∗
    (roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks)
  post := fun (dkPtr, bufPtr, dk, blks) s0 sf =>
    ⌜Par17Anchor s0 sf⌝ ∗
    (roundKeys15At dkPtr dk ∗ blocks17At bufPtr (armv8DecryptPar17 dk blks))
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Byte-slice (`bufPtr ↦ₛ bs`, `bs.length = 272`) in-place decryption contract. -/
@[expose] def decryptPar17InplaceBytesSpec :
    Spec (BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × List (BitVec 8)) where
  pre := fun (dkPtr, bufPtr, dk, bs) s0 =>
    ⌜s0.readReg64 .x0 = dkPtr ∧ s0.readReg64 .x1 = bufPtr ∧ s0.readReg64 .x2 = bufPtr ∧
      bs.length = 272⌝ ∗
    (roundKeys15At dkPtr dk ∗ (bufPtr ↦ₛ bs))
  post := fun (dkPtr, bufPtr, dk, bs) s0 sf =>
    ⌜Par17Anchor s0 sf⌝ ∗
    (roundKeys15At dkPtr dk ∗ (bufPtr ↦ₛ blocks17Bytes (armv8DecryptPar17 dk (bytesToBlocks17 bs))))
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-! ## 2. Tail Rounds `12..14`, Store-Back & `RET` (`+0x6a0 .. +0x7db`) -/

private theorem pc_setMem (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl

private theorem vreg_write_if (s : State) (r1 r2 : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r1 v).readVReg128 r2 =
      if (r2 == r1) = true then v else s.readVReg128 r2 := by
  rw [State.readVReg128_writeVReg128]
  by_cases h : r2 = r1 <;> simp [h]

private def raw17 (p : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128) : SepProp :=
  (p ↦₁₂₈ v0) ∗ ((p + 0x10#64) ↦₁₂₈ v1) ∗ ((p + 0x20#64) ↦₁₂₈ v2) ∗ ((p + 0x30#64) ↦₁₂₈ v3) ∗
  ((p + 0x40#64) ↦₁₂₈ v4) ∗ ((p + 0x50#64) ↦₁₂₈ v5) ∗ ((p + 0x60#64) ↦₁₂₈ v6) ∗ ((p + 0x70#64) ↦₁₂₈ v7) ∗
  ((p + 0x80#64) ↦₁₂₈ v8) ∗ ((p + 0x90#64) ↦₁₂₈ v9) ∗ ((p + 0xa0#64) ↦₁₂₈ v10) ∗ ((p + 0xb0#64) ↦₁₂₈ v11) ∗
  ((p + 0xc0#64) ↦₁₂₈ v12) ∗ ((p + 0xd0#64) ↦₁₂₈ v13) ∗ ((p + 0xe0#64) ↦₁₂₈ v14) ∗ ((p + 0xf0#64) ↦₁₂₈ v15) ∗
  ((p + 0x100#64) ↦₁₂₈ v16)

private theorem blocks17At_eq_raw17 (p : BitVec 64) (blks : Vector (BitVec 128) 17) :
    blocks17At p blks = raw17 p blks[0] blks[1] blks[2] blks[3] blks[4] blks[5] blks[6] blks[7]
      blks[8] blks[9] blks[10] blks[11] blks[12] blks[13] blks[14] blks[15] blks[16] := rfl

private theorem raw17_map_eq_blocks17At (p : BitVec 64) (f : BitVec 128 → BitVec 128) (r : Par17Regs) :
    raw17 p (f r.b0) (f r.b1) (f r.b2) (f r.b3) (f r.b4) (f r.b5) (f r.b6) (f r.b7) (f r.b8)
      (f r.b9) (f r.b10) (f r.b11) (f r.b12) (f r.b13) (f r.b14) (f r.b15) (f r.b16) =
      blocks17At p (r.map f).toVector := by
  dsimp only [raw17, blocks17At, Par17Regs.map, Par17Regs.toVector]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

private theorem rk15_focus_c0 {p : BitVec 64} {dk : Vector (BitVec 128) 15} {F0 : SepProp}
    {k12 k13 : BitVec 128} (h12 : dk[12] = k12) (h13 : dk[13] = k13) :
    ∃ F, roundKeys15At p dk ∗ F0 =
      (((p + 0xc0#64) ↦₁₂₈ k12) ∗ (((p + 0xc0#64) + 16#64) ↦₁₂₈ k13)) ∗ F :=
  ⟨_, by dsimp only [roundKeys15At]; rw [h12, h13]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus⟩

private theorem raw17_upd01 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w0 w1 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           ((p ↦₁₂₈ v0) ∗ ((p + 16#64) ↦₁₂₈ v1)) ∗ F ∧
         ((p ↦₁₂₈ w0) ∗ ((p + 16#64) ↦₁₂₈ w1)) ∗ F =
           R ∗ raw17 p w0 w1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 :=
  ⟨_, by dsimp only [raw17]; sep_focus, by dsimp only [raw17]; sep_eq⟩

private theorem raw17_upd23 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w2 w3 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0x20#64) ↦₁₂₈ v2) ∗ (((p + 0x20#64) + 16#64) ↦₁₂₈ v3)) ∗ F ∧
         (((p + 0x20#64) ↦₁₂₈ w2) ∗ (((p + 0x20#64) + 16#64) ↦₁₂₈ w3)) ∗ F =
           R ∗ raw17 p v0 v1 w2 w3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd45 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w4 w5 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0x40#64) ↦₁₂₈ v4) ∗ (((p + 0x40#64) + 16#64) ↦₁₂₈ v5)) ∗ F ∧
         (((p + 0x40#64) ↦₁₂₈ w4) ∗ (((p + 0x40#64) + 16#64) ↦₁₂₈ w5)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 w4 w5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd67 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w6 w7 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0x60#64) ↦₁₂₈ v6) ∗ (((p + 0x60#64) + 16#64) ↦₁₂₈ v7)) ∗ F ∧
         (((p + 0x60#64) ↦₁₂₈ w6) ∗ (((p + 0x60#64) + 16#64) ↦₁₂₈ w7)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 w6 w7 v8 v9 v10 v11 v12 v13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd89 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w8 w9 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0x80#64) ↦₁₂₈ v8) ∗ (((p + 0x80#64) + 16#64) ↦₁₂₈ v9)) ∗ F ∧
         (((p + 0x80#64) ↦₁₂₈ w8) ∗ (((p + 0x80#64) + 16#64) ↦₁₂₈ w9)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 w8 w9 v10 v11 v12 v13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd1011 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w10 w11 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0xa0#64) ↦₁₂₈ v10) ∗ (((p + 0xa0#64) + 16#64) ↦₁₂₈ v11)) ∗ F ∧
         (((p + 0xa0#64) ↦₁₂₈ w10) ∗ (((p + 0xa0#64) + 16#64) ↦₁₂₈ w11)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 w10 w11 v12 v13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd1213 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w12 w13 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0xc0#64) ↦₁₂₈ v12) ∗ (((p + 0xc0#64) + 16#64) ↦₁₂₈ v13)) ∗ F ∧
         (((p + 0xc0#64) ↦₁₂₈ w12) ∗ (((p + 0xc0#64) + 16#64) ↦₁₂₈ w13)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 w12 w13 v14 v15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd1415 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w14 w15 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           (((p + 0xe0#64) ↦₁₂₈ v14) ∗ (((p + 0xe0#64) + 16#64) ↦₁₂₈ v15)) ∗ F ∧
         (((p + 0xe0#64) ↦₁₂₈ w14) ∗ (((p + 0xe0#64) + 16#64) ↦₁₂₈ w15)) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 w14 w15 v16 :=
  ⟨_, by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_focus,
      by simp only [raw17, BitVec.add_assoc, BitVec.reduceAdd]; sep_eq⟩

private theorem raw17_upd16 {R : SepProp} {p : BitVec 64}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : BitVec 128} (w16 : BitVec 128) :
    ∃ F, R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 =
           ((p + 0x100#64) ↦₁₂₈ v16) ∗ F ∧
         ((p + 0x100#64) ↦₁₂₈ w16) ∗ F =
           R ∗ raw17 p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 w16 :=
  ⟨_, by dsimp only [raw17]; sep_focus, by dsimp only [raw17]; sep_eq⟩

private theorem step_stp128_upd {prog : Program} {target_pc pc ea : BitVec 64}
    {old1 old2 val1 val2 : BitVec 128}
    {s : State} {Pre Post : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hv1 : s.readVReg128 vt1 = val1) (hv2 : s.readVReg128 vt2 = val2)
    (hupd : ∃ F, Pre = ((ea ↦₁₂₈ old1) ∗ ((ea + 16#64) ↦₁₂₈ old2)) ∗ F ∧
      ((ea ↦₁₂₈ val1) ∗ ((ea + 16#64) ↦₁₂₈ val2)) ∗ F = Post)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') Post post oom) :
    SepWP prog target_pc s Pre post oom := by
  obtain ⟨F, hsplit, hmerge⟩ := hupd
  exact step_stp128_perm hfetch hpc hrun haddr hv1 hv2 hsplit fun m' hm' =>
    hmerge ▸ hnext m' hm'

private theorem step_str128_upd {prog : Program} {target_pc pc ea : BitVec 64}
    {old val : BitVec 128}
    {s : State} {Pre Post : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt rn : BitVec 5} {off : BitVec 64}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset (.gpr rn) off)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) + off = ea)
    (hval : s.readVReg128 vt = val)
    (hupd : ∃ F, Pre = (ea ↦₁₂₈ old) ∗ F ∧ (ea ↦₁₂₈ val) ∗ F = Post)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') Post post oom) :
    SepWP prog target_pc s Pre post oom := by
  obtain ⟨F, hsplit, hmerge⟩ := hupd
  exact step_str128_perm hfetch hpc hrun haddr hval hsplit fun m' hm' =>
    hmerge ▸ hnext m' hm'

private theorem step_aesd {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vd vk : BitVec 5} (blk rk : BitVec 128)
    (hfetch : prog.fetch pc = some (.aes .AESD vd vk))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hd : s.readVReg128 vd = blk) (hk : s.readVReg128 vk = rk)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vd (evalAesOp .AESD blk rk)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom :=
  step_aes hfetch hpc hrun (by rw [hd, hk]) hnext

private theorem step_eor_finish {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rm rn rd : BitVec 5} (blk12 k13 k14 : BitVec 128)
    (hfetch : prog.fetch pc = some (.simdThreeSame true true 0#2 rm 3#5 rn rd))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hn : s.readVReg128 rn = k14)
    (hm : s.readVReg128 rm = evalAesOp .AESD blk12 k13)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 rd (decFinish k13 k14 blk12)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hmem_sat
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.simdThreeSame true true 0#2 rm 3#5 rn rd) s =
      (s.writeVReg128 rd (decFinish k13 k14 blk12)).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, State.advancePC, State.setPC, hpc, hn, hm,
      decFinish_machine]
  rw [hstep]
  have hmem : ((s.writeVReg128 rd (decFinish k13 k14 blk12)).setPC (pc + 4#64)).mem = s.mem := by
    cases s; rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hmem_sat)

private theorem step_ret {prog : Program} {target_pc pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rn : Reg}
    (hfetch : prog.fetch pc = some (.ret rn))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (htarget : s.readReg64 rn = target_pc)
    (hnext : SepWP prog target_pc (s.setPC target_pc) P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hmem_sat
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ret rn) s = s.setPC target_pc := by
    simp [Program.evalInst, execInstWithSvc, htarget]
  rw [hstep]
  have hmem : (s.setPC target_pc).mem = s.mem := by cases s; rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hmem_sat)


-- Non-`rfl` wrappers (`Eq.trans`) so Lean 4.35 `simp` (`isRflTheorem`) emits explicit
-- rewrite proof terms instead of `proof? := none`, preventing $O(2^n)$ kernel unfolding
-- of nested `State.writeVReg128` / `State.setPC` chains.
private theorem pc_setPC_nr (s : State) (pc : BitVec 64) :
    (s.setPC pc).pc = pc := (State.pc_setPC s pc).trans (Eq.refl _)
private theorem pc_setMem_nr (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := (pc_setMem s m).trans (Eq.refl _)
private theorem status_setPC_nr (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := (status_setPC s pc).trans (Eq.refl _)
private theorem status_setMem_nr (s : State) (m : Memory) :
    (s.setMem m).status = s.status := (status_setMem s m).trans (Eq.refl _)
private theorem status_writeVReg128_nr (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).status = s.status := (status_writeVReg128 s r v).trans (Eq.refl _)
private theorem vreg_setPC_nr (s : State) (pc : BitVec 64) (r : BitVec 5) :
    (s.setPC pc).readVReg128 r = s.readVReg128 r := (vreg_setPC s pc r).trans (Eq.refl _)
private theorem vreg_setMem_nr (s : State) (m : Memory) (r : BitVec 5) :
    (s.setMem m).readVReg128 r = s.readVReg128 r := (vreg_setMem s m r).trans (Eq.refl _)
private theorem regs_writeVReg128_nr (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).regs = s.regs := (regs_writeVReg128 s r v).trans (Eq.refl _)
private theorem regs_setPC_nr (s : State) (pc : BitVec 64) :
    (s.setPC pc).regs = s.regs := (regs_setPC s pc).trans (Eq.refl _)
private theorem regs_setMem_nr (s : State) (m : Memory) :
    (s.setMem m).regs = s.regs := (regs_setMem s m).trans (Eq.refl _)
private theorem sp_writeVReg128_nr (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := (sp_writeVReg128 s r v).trans (Eq.refl _)
private theorem sp_setPC_nr (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := (sp_setPC s pc).trans (Eq.refl _)
private theorem sp_setMem_nr (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := (sp_setMem s m).trans (Eq.refl _)
private theorem mem_writeVReg128_nr (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).mem = s.mem := (mem_writeVReg128_eq s r v).trans (Eq.refl _)
private theorem mem_setPC_nr (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := (mem_setPC_eq s pc).trans (Eq.refl _)
private theorem mem_setMem_nr (s : State) (m : Memory) :
    (s.setMem m).mem = m := (mem_setMem_eq s m).trans (Eq.refl _)
section
arm64_proof_prelude
attribute [local irreducible] decRound decFinish raw17 roundKeys15At
  State.readVReg128 State.writeVReg128 State.setPC State.setMem

local macro "vreg_lookup" : tactic => `(tactic|
  (try simp only [vreg_setPC_nr, vreg_setMem_nr, vreg_write_if,
    BitVec.reduceBEq, Bool.false_eq_true, eq_self, ↓reduceIte]) <;> assumption)

local macro "wp_aesd_imc " hf1:term:max hf2:term:max blk:term:max rk:term:max : tactic => `(tactic|
  refine step_aesd_imc $hf1 $hf2 $blk $rk
    (by (try simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd]) <;> assumption)
    (by (try simp only [status_setPC_nr, status_setMem_nr, status_writeVReg128_nr]) <;> assumption)
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd])
    (by vreg_lookup) (by vreg_lookup) ?_)

local macro "wp_aesd " hf:term:max blk:term:max rk:term:max : tactic => `(tactic|
  refine step_aesd $blk $rk $hf
    (by (try simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd]) <;> assumption)
    (by (try simp only [status_setPC_nr, status_setMem_nr, status_writeVReg128_nr]) <;> assumption)
    (by vreg_lookup) (by vreg_lookup) ?_)

local macro "wp_eor " hf:term:max blk12:term:max k13:term:max k14:term:max : tactic => `(tactic|
  refine step_eor_finish $blk12 $k13 $k14 $hf
    (by (try simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd]) <;> assumption)
    (by (try simp only [status_setPC_nr, status_setMem_nr, status_writeVReg128_nr]) <;> assumption)
    (by vreg_lookup) (by vreg_lookup) ?_)

local macro "wp_stp128 " hf:term:max ea:term:max hx2:ident upd:term:max m:ident hm:ident : tactic => `(tactic|
  refine step_stp128_upd (ea := $ea) $hf
    (by simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd])
    (by (try simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr]) <;> assumption)
    (by simp only [readReg64_setPC, readReg64_setMem, readReg64_writeVReg128, BitVec.add_zero, $hx2:ident])
    (by vreg_lookup) (by vreg_lookup) $upd fun $m $hm => ?_)

private structure TailMidRegs (k12 k13 k14 : BitVec 128) (r : Par17Regs) (s : State) : Prop where
  v3  : s.readVReg128 3#5  = r.b14
  v4  : s.readVReg128 4#5  = r.b15
  v5  : s.readVReg128 5#5  = r.b16
  v6  : s.readVReg128 6#5  = r.b13
  v7  : s.readVReg128 7#5  = decRound k12 r.b12
  v16 : s.readVReg128 16#5 = decRound k12 r.b11
  v17 : s.readVReg128 17#5 = decRound k12 r.b10
  v18 : s.readVReg128 18#5 = decRound k12 r.b9
  v19 : s.readVReg128 19#5 = decRound k12 r.b8
  v20 : s.readVReg128 20#5 = evalAesOp .AESD (decRound k12 r.b5) k13
  v21 : s.readVReg128 21#5 = evalAesOp .AESD (decRound k12 r.b6) k13
  v22 : s.readVReg128 22#5 = evalAesOp .AESD (decRound k12 r.b7) k13
  v23 : s.readVReg128 23#5 = evalAesOp .AESD (decRound k12 r.b4) k13
  v25 : s.readVReg128 25#5 = k12
  v26 : s.readVReg128 26#5 = k13
  v27 : s.readVReg128 27#5 = k14

private abbrev outBlk (k12 k13 k14 x : BitVec 128) : BitVec 128 :=
  decFinish k13 k14 (decRound k12 x)

set_option maxHeartbeats 400000 in
private theorem step_tailA {P : Program} {fnAddr dkPtr bufPtr target_pc : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blks : Vector (BitVec 128) 17}
    {k12 k13 k14 : BitVec 128} {r : Par17Regs} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x6a0#64) (decodeWords par17TailWordsA))
    (hx0 : s0.readReg64 .x0 = dkPtr) (hx2 : s0.readReg64 .x2 = bufPtr)
    (hk12_eq : dk[12] = k12) (hk13_eq : dk[13] = k13)
    (hpc : s.pc = fnAddr + 0x6a0#64) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hr : r.holds s) (hk14 : s.readVReg128 27#5 = k14)
    (hcont : ∀ sM : State, sM.pc = fnAddr + 0x744#64 → sM.status = .Running →
      Par17Anchor s0 sM → TailMidRegs k12 k13 k14 r sM →
      SepWP P target_pc sM
        (roundKeys15At dkPtr dk ∗
          raw17 bufPtr (outBlk k12 k13 k14 r.b0) (outBlk k12 k13 k14 r.b1)
            (outBlk k12 k13 k14 r.b2) (outBlk k12 k13 k14 r.b3)
            blks[4] blks[5] blks[6] blks[7] blks[8] blks[9]
            blks[10] blks[11] blks[12] blks[13] blks[14] blks[15] blks[16]) post oom) :
    SepWP P target_pc s (roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks) post oom := by
  rcases hr with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩
  have_instrs hc 0 41
  have hx0_s : s.readReg64 (.gpr 0#5) = dkPtr := (ha.readReg64 (.gpr 0#5)).trans hx0
  have hx2_s : s.readReg64 (.gpr 2#5) = bufPtr := (ha.readReg64 (.gpr 2#5)).trans hx2
  rw [blocks17At_eq_raw17]
  obtain ⟨Fk, hfk⟩ := rk15_focus_c0 (p := dkPtr) (dk := dk)
    (F0 := raw17 bufPtr blks[0] blks[1] blks[2] blks[3] blks[4] blks[5] blks[6] blks[7]
      blks[8] blks[9] blks[10] blks[11] blks[12] blks[13] blks[14] blks[15] blks[16])
    hk12_eq hk13_eq
  refine step_ldp128 (ea := dkPtr + 0xc0#64) hf_0 hpc hrun (by rw [hx0_s]) hfk ?_
  wp_aesd_imc hf_1 hf_2 r.b0 k12; wp_aesd_imc hf_3 hf_4 r.b1 k12
  wp_aesd_imc hf_5 hf_6 r.b2 k12; wp_aesd_imc hf_7 hf_8 r.b3 k12
  wp_aesd_imc hf_9 hf_10 r.b6 k12; wp_aesd hf_11 (decRound k12 r.b0) k13
  wp_aesd_imc hf_12 hf_13 r.b7 k12; wp_aesd hf_14 (decRound k12 r.b1) k13
  wp_aesd hf_15 (decRound k12 r.b2) k13; wp_aesd hf_16 (decRound k12 r.b3) k13
  wp_aesd_imc hf_17 hf_18 r.b4 k12; wp_eor hf_19 (decRound k12 r.b0) k13 k14
  wp_aesd_imc hf_20 hf_21 r.b5 k12; wp_eor hf_22 (decRound k12 r.b1) k13 k14
  wp_aesd_imc hf_23 hf_24 r.b8 k12; wp_aesd_imc hf_25 hf_26 r.b9 k12
  wp_eor hf_27 (decRound k12 r.b2) k13 k14; wp_aesd hf_28 (decRound k12 r.b6) k13
  wp_aesd hf_29 (decRound k12 r.b7) k13; wp_aesd_imc hf_30 hf_31 r.b10 k12
  wp_stp128 hf_32 bufPtr hx2_s (raw17_upd01 (outBlk k12 k13 k14 r.b0) (outBlk k12 k13 k14 r.b1)) m1 hm1
  wp_eor hf_33 (decRound k12 r.b3) k13 k14; wp_aesd_imc hf_34 hf_35 r.b11 k12
  wp_aesd hf_36 (decRound k12 r.b4) k13; wp_aesd hf_37 (decRound k12 r.b5) k13
  wp_aesd_imc hf_38 hf_39 r.b12 k12
  wp_stp128 hf_40 (bufPtr + 0x20#64) hx2_s (raw17_upd23 (outBlk k12 k13 k14 r.b2) (outBlk k12 k13 k14 r.b3)) m2 hm2
  have hperm2 : m2.perm = s.mem.perm := by
    simp only [mem_writeVReg128_nr, mem_setPC_nr, mem_setMem_nr] at hm1 hm2
    exact hm2.trans hm1
  refine hcont _ (by simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr, hrun])
    (ha.step (by simp only [regs_writeVReg128_nr, regs_setPC_nr, regs_setMem_nr])
      (by simp only [sp_writeVReg128_nr, sp_setPC_nr, sp_setMem_nr])
      (by simp only [simdCalleeProj, vreg_setPC_nr, vreg_setMem_nr, vreg_write_if,
        BitVec.reduceBEq, Bool.false_eq_true, eq_self, ↓reduceIte])
      (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC, pureStepProj_setMem])
      (by simpa only [mem_setMem_nr] using hperm2))
    ⟨by vreg_lookup, by vreg_lookup, by vreg_lookup, by vreg_lookup,
     by vreg_lookup, by vreg_lookup, by vreg_lookup, by vreg_lookup,
     by vreg_lookup, by vreg_lookup, by vreg_lookup, by vreg_lookup,
     by vreg_lookup, by vreg_lookup, by vreg_lookup, by vreg_lookup⟩

set_option maxHeartbeats 400000 in
private theorem step_tailB {P : Program} {fnAddr dkPtr bufPtr target_pc : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blks outBlks : Vector (BitVec 128) 17}
    {k12 k13 k14 : BitVec 128} {r : Par17Regs} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P (fnAddr + 0x744#64) (decodeWords par17TailWordsB))
    (hx2 : s0.readReg64 .x2 = bufPtr) (hlr : target_pc = s0.readReg64 .lr)
    (hpc : s.pc = fnAddr + 0x744#64) (hrun : s.status = .Running) (ha : Par17Anchor s0 s)
    (hmr : TailMidRegs k12 k13 k14 r s)
    (hfin : (r.map (outBlk k12 k13 k14)).toVector = outBlks)
    (hpost : ∀ sf : State, sf.pc = target_pc → sf.status = .Running → Par17Anchor s0 sf →
      post sf (roundKeys15At dkPtr dk ∗ blocks17At bufPtr outBlks)) :
    SepWP P target_pc s
      (roundKeys15At dkPtr dk ∗
        raw17 bufPtr (outBlk k12 k13 k14 r.b0) (outBlk k12 k13 k14 r.b1)
          (outBlk k12 k13 k14 r.b2) (outBlk k12 k13 k14 r.b3)
          blks[4] blks[5] blks[6] blks[7] blks[8] blks[9]
          blks[10] blks[11] blks[12] blks[13] blks[14] blks[15] blks[16]) post oom := by
  rcases hmr with ⟨v3, v4, v5, v6, v7, v16, v17, v18, v19, v20, v21, v22, v23, v25, v26, v27⟩
  have_instrs hc 0 38
  have hx2_s : s.readReg64 (.gpr 2#5) = bufPtr := (ha.readReg64 (.gpr 2#5)).trans hx2
  wp_eor hf_0 (decRound k12 r.b6) k13 k14; wp_aesd_imc hf_1 hf_2 r.b13 k12
  wp_eor hf_3 (decRound k12 r.b7) k13 k14; wp_aesd hf_4 (decRound k12 r.b8) k13
  wp_aesd hf_5 (decRound k12 r.b9) k13; wp_eor hf_6 (decRound k12 r.b4) k13 k14
  wp_eor hf_7 (decRound k12 r.b5) k13 k14; wp_aesd_imc hf_8 hf_9 r.b14 k12
  wp_aesd hf_10 (decRound k12 r.b10) k13
  wp_stp128 hf_11 (bufPtr + 0x60#64) hx2_s (raw17_upd67 (outBlk k12 k13 k14 r.b6) (outBlk k12 k13 k14 r.b7)) m1 hm1
  wp_aesd_imc hf_12 hf_13 r.b15 k12
  wp_stp128 hf_14 (bufPtr + 0x40#64) hx2_s (raw17_upd45 (outBlk k12 k13 k14 r.b4) (outBlk k12 k13 k14 r.b5)) m2 hm2
  wp_eor hf_15 (decRound k12 r.b8) k13 k14; wp_aesd hf_16 (decRound k12 r.b11) k13
  wp_eor hf_17 (decRound k12 r.b9) k13 k14; wp_aesd hf_18 (decRound k12 r.b12) k13
  wp_aesd_imc hf_19 hf_20 r.b16 k12; wp_aesd hf_21 (decRound k12 r.b13) k13
  wp_eor hf_22 (decRound k12 r.b10) k13 k14; wp_eor hf_23 (decRound k12 r.b11) k13 k14
  wp_aesd hf_24 (decRound k12 r.b14) k13; wp_aesd hf_25 (decRound k12 r.b15) k13
  wp_stp128 hf_26 (bufPtr + 0x80#64) hx2_s (raw17_upd89 (outBlk k12 k13 k14 r.b8) (outBlk k12 k13 k14 r.b9)) m3 hm3
  wp_eor hf_27 (decRound k12 r.b12) k13 k14; wp_eor hf_28 (decRound k12 r.b13) k13 k14
  wp_aesd hf_29 (decRound k12 r.b16) k13
  wp_stp128 hf_30 (bufPtr + 0xa0#64) hx2_s (raw17_upd1011 (outBlk k12 k13 k14 r.b10) (outBlk k12 k13 k14 r.b11)) m4 hm4
  wp_eor hf_31 (decRound k12 r.b14) k13 k14; wp_eor hf_32 (decRound k12 r.b15) k13 k14
  wp_stp128 hf_33 (bufPtr + 0xc0#64) hx2_s (raw17_upd1213 (outBlk k12 k13 k14 r.b12) (outBlk k12 k13 k14 r.b13)) m5 hm5
  wp_eor hf_34 (decRound k12 r.b16) k13 k14
  wp_stp128 hf_35 (bufPtr + 0xe0#64) hx2_s (raw17_upd1415 (outBlk k12 k13 k14 r.b14) (outBlk k12 k13 k14 r.b15)) m6 hm6
  refine step_str128_upd (ea := bufPtr + 0x100#64) hf_36
    (by simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr, hrun])
    (by simp only [readReg64_setPC, readReg64_setMem, readReg64_writeVReg128, hx2_s])
    (by vreg_lookup)
    (raw17_upd16 (outBlk k12 k13 k14 r.b16))
    fun m7 hm7 => ?_
  refine step_ret hf_37
    (by simp only [pc_setMem_nr, pc_setPC_nr, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr, hrun])
    (by
      rw [hlr, ← ha.readReg64 .lr]
      simp only [readReg64_setMem, readReg64_writeVReg128, readReg64_setPC])
    ?_
  have hperm_all : m7.perm = s.mem.perm := by
    simp only [mem_writeVReg128_nr, mem_setPC_nr, mem_setMem_nr] at hm1 hm2 hm3 hm4 hm5 hm6 hm7
    exact hm7.trans (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1)))))
  rw [raw17_map_eq_blocks17At bufPtr (outBlk k12 k13 k14) r, hfin]
  refine SepWP.done (pc_setPC_nr _ target_pc)
    (by simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr, hrun])
    (hpost _ (pc_setPC_nr _ target_pc)
      (by simp only [status_writeVReg128_nr, status_setPC_nr, status_setMem_nr, hrun])
      (ha.step (by simp only [regs_writeVReg128_nr, regs_setPC_nr, regs_setMem_nr])
        (by simp only [sp_writeVReg128_nr, sp_setPC_nr, sp_setMem_nr])
        (by simp only [simdCalleeProj, vreg_setPC_nr, vreg_setMem_nr, vreg_write_if,
          BitVec.reduceBEq, Bool.false_eq_true, eq_self, ↓reduceIte])
        (by simp only [pureStepProj_writeVReg128, pureStepProj_setPC, pureStepProj_setMem])
        (by simpa only [mem_setPC_nr, mem_setMem_nr] using hperm_all)))

/-! ## 3. Top-Level `SepWP` and `subroutine_ok` Theorems -/

/-- Direct `SepWP` verification of in-place `decrypt_par::<15, U17>` (`x0 = dkPtr`, `x1 = x2 = bufPtr`). -/
theorem decryptPar17_inplace_wp {P : Program} {fnAddr dkPtr bufPtr : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blks : Vector (BitVec 128) 17} {s0 : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P fnAddr (decodeWords decryptPar17Words))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dkPtr) (hx1 : s0.readReg64 .x1 = bufPtr) (hx2 : s0.readReg64 .x2 = bufPtr)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running → Par17Anchor s0 sf →
      post sf (roundKeys15At dkPtr dk ∗ blocks17At bufPtr (armv8DecryptPar17 dk blks))) :
    SepWP P (s0.readReg64 .lr) s0 (roundKeys15At dkPtr dk ∗ blocks17At bufPtr blks) post oom := by
  have hseg := Par17CodeSegs.of_hasInstrs hc
  refine step_head hseg.head hpc hrun hx0 hx1 fun s1 hpc1 hrun1 ha1 hr1 hk1 => ?_
  refine step_rounds_1_to_11 hseg hx0 hpc1 hrun1 ha1 hr1 hk1 fun s2 hpc2 hrun2 ha2 hr12 hk14 => ?_
  refine step_tailA hseg.tailA hx0 hx2 rfl rfl hpc2 hrun2 ha2 hr12 hk14 fun s3 hpc3 hrun3 ha3 hmr => ?_
  exact step_tailB hseg.tailB hx2 rfl hpc3 hrun3 ha3 hmr
    (Par17Regs.toVector_finish_rounds12 dk blks) hpost

/-- Full `subroutine_ok` contract for in-place `decrypt_par::<15, U17>` over `blocks17At`. -/
theorem decryptPar17_inplace_subroutine_ok {P : Program} {fnAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (decodeWords decryptPar17Words)) :
    subroutine_ok P fnAddr decryptPar17InplaceSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dkPtr, bufPtr, dk, blks⟩ R s0 hpc hrun hpre _
  dsimp only [decryptPar17InplaceSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hpre⟩
  refine ⟨_, hpre, decryptPar17_inplace_wp hc hpc hrun hx0 hx1 hx2 fun sf _ _ ha => ?_⟩
  refine ⟨fun hsat => ?_, ha.sp, ha.calleeSaved⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨ha, hsat⟩

/-- Byte-slice (`bufPtr ↦ₛ bs`, `bs.length = 272`) `subroutine_ok` corollary for `decrypt_par::<15, U17>`. -/
theorem decryptPar17_inplace_bytes_subroutine_ok {P : Program} {fnAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (decodeWords decryptPar17Words)) :
    subroutine_ok P fnAddr decryptPar17InplaceBytesSpec := by
  refine subroutine_ok_map (decryptPar17_inplace_subroutine_ok hc) ?_
  rintro ⟨dkPtr, bufPtr, dk, bs⟩ R s0 hpre
  dsimp only [decryptPar17InplaceBytesSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  refine ⟨(dkPtr, bufPtr, dk, bytesToBlocks17 bs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [decryptPar17InplaceSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    rw [pointsToBytes_eq_blocks17At bufPtr hlen] at hmem
    exact ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  · dsimp only [decryptPar17InplaceSpec, decryptPar17InplaceBytesSpec] at hpost ⊢
    rwa [blocks17At_eq_pointsToBytes] at hpost

end
end
end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
