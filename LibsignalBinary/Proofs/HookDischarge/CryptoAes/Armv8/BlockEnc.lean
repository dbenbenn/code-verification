/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model
meta import ProofLib.StdStartup.StdDetect

/-!
# Binary Contract for `aes::armv8::encdec::encrypt::<15>` (`Armv8.BlockEnc`)

Placement-generic (`hasInstrs`) ARM64 `SepWP` and `subroutine_ok` contracts for the 39-instruction
position-independent hardware AES-256 single-block encryption routine
`aes::armv8::encdec::encrypt::<15>`, covering both the in-place (`x1 = x2 = blkPtr`) and disjoint
(`x1 = inPtr`, `x2 = outPtr`) calling conventions, plus 16-byte `↦ₛ` / `memRegion` ↔ `↦₁₂₈`
bridge lemmas.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (evalAesOp_aesmc_vd_irrel u32OfBytesLE bytesToU32LE u128OfU32sLE bytesToU128LE u128ToBytesLE
   armv8Encrypt15 roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

attribute [local irreducible] evalAesOp

/-! ## 1. 16-Byte `↦ₛ` / `memRegion` ↔ `↦₁₂₈` Bridge Lemmas -/

theorem u128ToBytesLE_length (v : BitVec 128) : (u128ToBytesLE v).length = 16 := by
  simp [u128ToBytesLE]

private theorem bytesToU128LE_list16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    bytesToU128LE [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      u128OfU32sLE (u32OfBytesLE b0 b1 b2 b3) (u32OfBytesLE b4 b5 b6 b7)
        (u32OfBytesLE b8 b9 b10 b11) (u32OfBytesLE b12 b13 b14 b15) := rfl

theorem bytesToU128LE_u128ToBytesLE (v : BitVec 128) :
    bytesToU128LE (u128ToBytesLE v) = v := by
  have hl : u128ToBytesLE v =
      [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
       v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8,
       v.extractLsb' 64 8, v.extractLsb' 72 8, v.extractLsb' 80 8, v.extractLsb' 88 8,
       v.extractLsb' 96 8, v.extractLsb' 104 8, v.extractLsb' 112 8, v.extractLsb' 120 8] := by
    simp [u128ToBytesLE, List.ofFn_succ, List.ofFn_zero]
  have h0 : u32OfBytesLE (v.extractLsb' 0 8) (v.extractLsb' 8 8)
      (v.extractLsb' 16 8) (v.extractLsb' 24 8) = v.extractLsb' 0 32 := by
    dsimp only [u32OfBytesLE]; bv_bits
  have h1 : u32OfBytesLE (v.extractLsb' 32 8) (v.extractLsb' 40 8)
      (v.extractLsb' 48 8) (v.extractLsb' 56 8) = v.extractLsb' 32 32 := by
    dsimp only [u32OfBytesLE]; bv_bits
  have h2 : u32OfBytesLE (v.extractLsb' 64 8) (v.extractLsb' 72 8)
      (v.extractLsb' 80 8) (v.extractLsb' 88 8) = v.extractLsb' 64 32 := by
    dsimp only [u32OfBytesLE]; bv_bits
  have h3 : u32OfBytesLE (v.extractLsb' 96 8) (v.extractLsb' 104 8)
      (v.extractLsb' 112 8) (v.extractLsb' 120 8) = v.extractLsb' 96 32 := by
    dsimp only [u32OfBytesLE]; bv_bits
  have h4 : u128OfU32sLE (v.extractLsb' 0 32) (v.extractLsb' 32 32)
      (v.extractLsb' 64 32) (v.extractLsb' 96 32) = v := by
    dsimp only [u128OfU32sLE]; bv_bits
  rw [hl, bytesToU128LE_list16, h0, h1, h2, h3, h4]

theorem u128ToBytesLE_bytesToU128LE {bs : List (BitVec 8)} (h : bs.length = 16) :
    u128ToBytesLE (bytesToU128LE bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  simp only [u128ToBytesLE, bytesToU128LE, bytesToU32LE, u32OfBytesLE, u128OfU32sLE,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.getD_cons_zero,
    List.getD_cons_succ, List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem unpack64_pair_eq_u128ToBytesLE (v : BitVec 128) :
    unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64) = u128ToBytesLE v := by
  simp only [unpack64, u128ToBytesLE, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits,
          by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem pointsTo128_eq_pointsToBytes (ptr : BitVec 64) (v : BitVec 128) :
    (ptr ↦₁₂₈ v) = (ptr ↦ₛ u128ToBytesLE v) := by
  rw [pointsTo128_split64, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      ← unpack64_pair_eq_u128ToBytesLE, pointsToBytes_append, unpack64_length]

theorem pointsToBytes16_eq_pointsTo128 {ptr : BitVec 64} {bs : List (BitVec 8)}
    (h : bs.length = 16) :
    (ptr ↦ₛ bs) = (ptr ↦₁₂₈ bytesToU128LE bs) := by
  rw [pointsTo128_eq_pointsToBytes, u128ToBytesLE_bytesToU128LE h]

theorem pointsTo128_entails_memRegion (ptr : BitVec 64) (v : BitVec 128) :
    (ptr ↦₁₂₈ v) ⊢ memRegion ptr 16 := by
  rw [pointsTo128_eq_pointsToBytes]
  simpa [u128ToBytesLE_length] using pointsToBytes_entails_memRegion ptr (u128ToBytesLE v)

theorem memRegion16_eq_exists_pointsTo128 (ptr : BitVec 64) :
    memRegion ptr 16 = ∃∗ v : BitVec 128, (ptr ↦₁₂₈ v) :=
  (IsBlock.memRegion ptr 16).eq (IsBlock.sepExists fun v => IsBlock.pointsTo128 ptr v)
    fun m => ⟨fun _ => ⟨m.read128 ptr, rfl⟩, fun _ => trivial⟩

/-! ## 2. Direct 128-Bit `↦₁₂₈` SIMD Load/Store Step Combinators -/

private structure SepLoad128 (a : BitVec 64) (P : SepProp) (v : BitVec 128) : Prop where
  load : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.read128 a = v
  readable : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.canRead a 16 = true

private theorem SepLoad128.here {a : BitVec 64} {v : BitVec 128} :
    SepLoad128 a (a ↦₁₂₈ v) v where
  load hm := (IsBlock.pointsTo128 a v).read hm
  readable hm := (IsBlock.pointsTo128 a v).canRead (by decide) hm

private theorem SepLoad128.left {a : BitVec 64} {P Q : SepProp} {v : BitVec 128}
    (h : SepLoad128 a P v) : SepLoad128 a (P ∗ Q) v where
  load hm := h.load (by rwa [sepConj_assoc] at hm)
  readable hm := h.readable (by rwa [sepConj_assoc] at hm)

private theorem SepLoad128.right {a : BitVec 64} {P Q : SepProp} {v : BitVec 128}
    (h : SepLoad128 a Q v) : SepLoad128 a (P ∗ Q) v where
  load hm := h.load (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)
  readable hm := h.readable (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)

private structure SepStore128 (a : BitVec 64) (v' : BitVec 128) (P P' : SepProp) : Prop where
  store : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → (m.write128 a v' ⊨ P' ∗ R)
  writable : ∀ {R : SepProp} {m : Memory}, (m ⊨ P ∗ R) → m.canWrite a 16 = true

private theorem SepStore128.here {a : BitVec 64} {v v' : BitVec 128} :
    SepStore128 a v' (a ↦₁₂₈ v) (a ↦₁₂₈ v') where
  store hm := (IsBlock.pointsTo128 a v).write128 hm v'
  writable hm := (IsBlock.pointsTo128 a v).canWrite (by decide) hm

private theorem SepStore128.left {a : BitVec 64} {v' : BitVec 128} {P P' Q : SepProp}
    (h : SepStore128 a v' P P') : SepStore128 a v' (P ∗ Q) (P' ∗ Q) where
  store hm := by
    rw [sepConj_assoc] at hm ⊢
    exact h.store hm
  writable hm := h.writable (by rwa [sepConj_assoc] at hm)

private theorem SepStore128.right {a : BitVec 64} {v' : BitVec 128} {P Q Q' : SepProp}
    (h : SepStore128 a v' Q Q') : SepStore128 a v' (P ∗ Q) (P ∗ Q') where
  store hm := by
    rw [sepConj_comm P Q, sepConj_assoc] at hm
    rw [sepConj_comm P Q', sepConj_assoc]
    exact h.store hm
  writable hm := h.writable (by rw [sepConj_comm P Q, sepConj_assoc] at hm; exact hm)

private theorem perm_write128 (m : Memory) (addr : BitVec 64) (val : BitVec 128) :
    (m.write128 addr val).perm = m.perm := by
  simp only [Memory.write128]
  exact (Memory.perm_write64 _ _ _).trans (Memory.perm_write64 _ _ _)

private theorem step_ldrSimd128_128 {prog : Program} {target_pc pc ea : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v : BitVec 128}
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad128 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read128 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 16 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .Q128 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hm)

private theorem step_ldpSimd128_128 {prog : Program} {target_pc pc ea ea2 : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 128}
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 16#64 = ea2)
    (hload1 : SepLoad128 ea P v1)
    (hload2 : SepLoad128 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 v1).writeVReg128 vt2 v2).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read128 ea = v1 := hload1.load hm
  have hread2 : s.mem.read128 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 16 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 16 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldpSimd .Q128 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  exact SepWP.to_reaches_pc hnext (hmem.symm ▸ hm)

private theorem step_strSimd128_perm {prog : Program} {target_pc pc ea : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 128}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readVReg128 vt = val)
    (hstore : SepStore128 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write128 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 16 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (perm_write128 s.mem ea val)) hm'

local syntax "solve_load128" : tactic
local macro_rules
  | `(tactic| solve_load128) => `(tactic| first
      | exact SepLoad128.here
      | (apply SepLoad128.left; solve_load128)
      | (apply SepLoad128.right; solve_load128))

local syntax "solve_store128" : tactic
local macro_rules
  | `(tactic| solve_store128) => `(tactic| first
      | exact SepStore128.here
      | (apply SepStore128.left; solve_store128)
      | (apply SepStore128.right; solve_store128))

local macro "wp_ldr128 " hf:term:max : tactic => `(tactic| (
  apply step_ldrSimd128_128 $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · dsimp only [roundKeys15At]; solve_load128
  · wp_focus_close wp_norm_lhs))

local macro "wp_ldp128 " hf:term:max : tactic => `(tactic| (
  apply step_ldpSimd128_128 $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | bv_lin)
  · dsimp only [roundKeys15At]; solve_load128
  · dsimp only [roundKeys15At]; solve_load128
  · wp_focus_close wp_norm_lhs))

local macro "wp_str128 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_strSimd128_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · solve_store128
  · wp_focus_close wp_norm_lhs
  intro $m $hm; try wp_norm_state))

/-! ## 3. Machine Code & Specifications (`encrypt::<15>`, 39 Instructions) -/

/-- Exact 39 instruction words (`156` B) of `aes::armv8::encdec::encrypt::<15>`. -/
@[expose] def encrypt15Words : List (BitVec 32) :=
  [0xad400801#32, 0x3dc00020#32, 0x4e284801#32, 0x4e286821#32, 0x4e284822#32,
   0x4e286842#32, 0xad410400#32, 0x4e284840#32, 0x4e286800#32, 0x4e284801#32,
   0x4e286821#32, 0xad420800#32, 0x4e284820#32, 0x4e286800#32, 0x4e284802#32,
   0x4e286842#32, 0xad430400#32, 0x4e284840#32, 0x4e286800#32, 0x4e284801#32,
   0x4e286821#32, 0xad440800#32, 0x4e284820#32, 0x4e286800#32, 0x4e284802#32,
   0x4e286842#32, 0xad450400#32, 0x4e284840#32, 0x4e286800#32, 0x4e284801#32,
   0x4e286821#32, 0xad460800#32, 0x4e284820#32, 0x4e286800#32, 0x4e284802#32,
   0x3dc03800#32, 0x6e221c00#32, 0x3d800040#32, 0xd65f03c0#32]

/-- Decoded 39-instruction sequence of `aes::armv8::encdec::encrypt::<15>`. -/
@[expose] def encrypt15Instrs : List Instr := decodeWords encrypt15Words

private theorem map_decode_eq_of_all_isSome : ∀ ws : List (BitVec 32),
    ws.all (fun w => (Arm64.decode w).isSome) = true →
    ws.map Arm64.decode = (decodeWords ws).map some
  | [], _ => rfl
  | w :: ws, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, decodeWords, decodeWord]
    cases hd : Arm64.decode w with
    | none => simp [hd] at h
    | some i => exact congrArg (some i :: ·) (map_decode_eq_of_all_isSome ws h.2)

theorem encrypt15Instrs_template_eq :
    encrypt15Words.map Arm64.decode = encrypt15Instrs.map some :=
  map_decode_eq_of_all_isSome _ (by decide)

/-- In-place Hoare contract (`x0 = ekPtr`, `x1 = blkPtr`, `x2 = blkPtr`) for `encrypt::<15>`,
    preserving all GPRs (`sf.regs = s0.regs`), `sp`, `tpidrEl0`, and `PureStepPreserved s0 sf`. -/
@[expose] def encrypt15InplaceSpec :
    Spec (BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × BitVec 128) where
  pre := fun (ekPtr, blkPtr, ek, blk) s0 =>
    ⌜s0.readReg64 .x0 = ekPtr ∧ s0.readReg64 .x1 = blkPtr ∧ s0.readReg64 .x2 = blkPtr⌝ ∗
    (roundKeys15At ekPtr ek ∗ (blkPtr ↦₁₂₈ blk))
  post := fun (ekPtr, blkPtr, ek, blk) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
    (roundKeys15At ekPtr ek ∗ (blkPtr ↦₁₂₈ armv8Encrypt15 ek blk))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Separate-buffer Hoare contract (`x0 = ekPtr`, `x1 = inPtr`, `x2 = outPtr`) for `encrypt::<15>`,
    preserving all GPRs (`sf.regs = s0.regs`), `sp`, `tpidrEl0`, and `PureStepPreserved s0 sf`. -/
@[expose] def encrypt15Spec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × Vector (BitVec 128) 15 × BitVec 128 × BitVec 128) where
  pre := fun (ekPtr, inPtr, outPtr, ek, blk, oldOut) s0 =>
    ⌜s0.readReg64 .x0 = ekPtr ∧ s0.readReg64 .x1 = inPtr ∧ s0.readReg64 .x2 = outPtr⌝ ∗
    (roundKeys15At ekPtr ek ∗ (inPtr ↦₁₂₈ blk) ∗ (outPtr ↦₁₂₈ oldOut))
  post := fun (ekPtr, inPtr, outPtr, ek, blk, _oldOut) s0 sf =>
    ⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
    (roundKeys15At ekPtr ek ∗ (inPtr ↦₁₂₈ blk) ∗ (outPtr ↦₁₂₈ armv8Encrypt15 ek blk))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. Verification of `encrypt::<15>` -/

private theorem fin_foldl_13_expand (ek : Vector (BitVec 128) 15)
    (op1 op2 : BitVec 128 → BitVec 128 → BitVec 128) (blk : BitVec 128) :
    Fin.foldl 13 (fun s (r : Fin 13) => op2 0#128 (op1 ek[r.val] s)) blk =
      op2 0#128 (op1 ek[12]
        (op2 0#128 (op1 ek[11]
        (op2 0#128 (op1 ek[10]
        (op2 0#128 (op1 ek[9]
        (op2 0#128 (op1 ek[8]
        (op2 0#128 (op1 ek[7]
        (op2 0#128 (op1 ek[6]
        (op2 0#128 (op1 ek[5]
        (op2 0#128 (op1 ek[4]
        (op2 0#128 (op1 ek[3]
        (op2 0#128 (op1 ek[2]
        (op2 0#128 (op1 ek[1]
        (op2 0#128 (op1 ek[0] blk))))))))))))))))))))))))) := by
  simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, Nat.reduceAdd]

private theorem armv8Encrypt15_expand (ek : Vector (BitVec 128) 15) (blk : BitVec 128) :
    armv8Encrypt15 ek blk =
      ek[14] ^^^ evalAesOp .AESE ek[13]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[12]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[11]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[10]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[9]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[8]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[7]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[6]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[5]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[4]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[3]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[2]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[1]
        (evalAesOp .AESMC 0#128 (evalAesOp .AESE ek[0] blk)))))))))))))))))))))))))) :=
  congrArg (fun x => ek[14] ^^^ evalAesOp .AESE ek[13] x)
    (fin_foldl_13_expand ek (evalAesOp .AESE) (evalAesOp .AESMC) blk)

namespace Simp
@[scoped simp] theorem regs_writeVReg128_eq (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).regs = s.regs := by cases s; rfl
@[scoped simp] theorem regs_setPC_eq (s : State) (pc : BitVec 64) :
    (s.setPC pc).regs = s.regs := by cases s; rfl
@[scoped simp] theorem regs_setMem_eq (s : State) (m : Memory) :
    (s.setMem m).regs = s.regs := by cases s; rfl
end Simp
open scoped Simp

set_option maxHeartbeats 400000 in
private theorem encrypt15_sepWP {P : Program} {entry ekPtr inPtr outPtr : BitVec 64}
    {ek : Vector (BitVec 128) 15} {blk : BitVec 128} {Q Q' : SepProp} {s0 : State}
    (R : SepProp)
    (hc : hasInstrs P entry encrypt15Instrs)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ekPtr)
    (hx1 : s0.readReg64 .x1 = inPtr)
    (hx2 : s0.readReg64 .x2 = outPtr)
    (hload_blk : SepLoad128 inPtr (roundKeys15At ekPtr ek ∗ Q) blk)
    (hstore_blk : SepStore128 outPtr (armv8Encrypt15 ek blk)
      (roundKeys15At ekPtr ek ∗ Q) (roundKeys15At ekPtr ek ∗ Q')) :
    SepWP P (s0.readReg64 Reg.lr) s0 (roundKeys15At ekPtr ek ∗ Q)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          sf.mem ⊨ (⌜PureStepPreserved s0 sf ∧ sf.regs = s0.regs⌝ ∗
            (roundKeys15At ekPtr ek ∗ Q')) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun _ => ⌜False⌝) := by
  have_instrs hc 0 39
  wp_ldp128 hf_0
  apply step_ldrSimd128_128 hf_1
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · exact hload_blk
  · wp_focus_close wp_norm_lhs
  wp_steps 4
  wp_ldp128 hf_6
  wp_steps 4
  wp_ldp128 hf_11
  wp_steps 4
  wp_ldp128 hf_16
  wp_steps 4
  wp_ldp128 hf_21
  wp_steps 4
  wp_ldp128 hf_26
  wp_steps 4
  wp_ldp128 hf_31
  wp_steps 3
  wp_ldr128 hf_35
  wp_steps 1
  apply step_strSimd128_perm (val := armv8Encrypt15 ek blk) hf_37
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · rw [armv8Encrypt15_expand]; simp [wp_norm, arm64_norm]
  · exact hstore_blk
  · wp_focus_close wp_norm_lhs
  intro m1 hm1; try wp_norm_state
  wp_steps 1
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hm1]), by simp [wp_norm, arm64_norm]⟩, hm⟩
  · rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, *]

/-- Placement-generic `subroutine_ok` verification of in-place `encrypt::<15>` (`x1 = x2 = blkPtr`). -/
theorem encrypt15_inplace_subroutine_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry encrypt15Instrs) :
    subroutine_ok P entry encrypt15InplaceSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ekPtr, blkPtr, ek, blk⟩ R s0 hpc hrun hpre _hsp
  dsimp only [encrypt15InplaceSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hpre⟩
  refine ⟨roundKeys15At ekPtr ek ∗ (blkPtr ↦₁₂₈ blk), hpre, ?_⟩
  exact encrypt15_sepWP (ek := ek) (blk := blk) (Q := blkPtr ↦₁₂₈ blk)
    (Q' := blkPtr ↦₁₂₈ armv8Encrypt15 ek blk) R hc hpc hrun hx0 hx1 hx2
    (by solve_load128) (by solve_store128)

/-- Placement-generic `subroutine_ok` verification of separate-buffer `encrypt::<15>`
    (`x1 = inPtr`, `x2 = outPtr`). -/
theorem encrypt15_subroutine_ok {P : Program} {entry : BitVec 64}
    (hc : hasInstrs P entry encrypt15Instrs) :
    subroutine_ok P entry encrypt15Spec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ekPtr, inPtr, outPtr, ek, blk, oldOut⟩ R s0 hpc hrun hpre _hsp
  dsimp only [encrypt15Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hpre⟩
  refine ⟨roundKeys15At ekPtr ek ∗ (inPtr ↦₁₂₈ blk) ∗ (outPtr ↦₁₂₈ oldOut), hpre, ?_⟩
  exact encrypt15_sepWP (ek := ek) (blk := blk)
    (Q := (inPtr ↦₁₂₈ blk) ∗ (outPtr ↦₁₂₈ oldOut))
    (Q' := (inPtr ↦₁₂₈ blk) ∗ (outPtr ↦₁₂₈ armv8Encrypt15 ek blk)) R hc hpc hrun hx0 hx1 hx2
    (by solve_load128) (by solve_store128)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockEnc
